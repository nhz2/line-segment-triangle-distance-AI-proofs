import DistanceAccuracy.SegmentCoordinates
import DistanceAccuracy.FaceEvaluation

/-! Joint face geometry after the actual crossing point FMA. -/
namespace DistanceAccuracy.CrossingCoordinates
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant
open Reconstruction ReconstructionIEEE FaceCoordinates

lemma anchor_error {rho eta L a p₀ p₁ s P AP AX : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/1024) (hL : 0 ≤ L) (heta : eta ≤ rho^2*L)
    (ha : |a| ≤ L) (hp0 : |p₀| ≤ L) (hp1 : |p₁| ≤ L) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hP : RoundError rho eta (p₁-p₀) P) (hAP : RoundError rho eta (a-p₀) AP)
    (hAX : RoundError rho eta (AP-s*P) AX) :
    |AX-(a-((1-s)*p₀+s*p₁))| ≤ 9*rho*L := by
  have hp := round_difference hr hrmax hL heta hp1 hp0 hP
  have hap := round_difference hr hrmax hL heta ha hp0 hAP
  have hs : |(-s)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hs0]; exact hs1
  have hin : |(AP-s*P)-(a-((1-s)*p₀+s*p₁))| ≤ 6*rho*L := by
    have hh := affine_input_error hr hL hs hap hp
    convert hh using 1 <;> congr 1 <;> ring
  have hpoint := interval_abs hL hp0 hp1 hs0 hs1
  have hideal := difference_abs ha hpoint
  have hh := round_propagate (C := 6) (K := 2) hr hL heta (by linarith) hin hideal hAX
  norm_num at hh ⊢
  exact hh

lemma coordinate_201_bound {v : E3} {L : ℝ} (hL : 0 ≤ L)
    (hv : ∀ k, |v k| ≤ (201/100)*L) :
    (∀ k, |v k| ≤ ((7/2)*L)/Real.sqrt 3) ∧ ‖v‖ ≤ (7/2)*L := by
  have hs : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsmax : Real.sqrt (3:ℝ) ≤ 26/15 := by apply Real.sqrt_le_iff.mpr; norm_num
  have hm := mul_le_mul_of_nonneg_right hsmax (show 0 ≤ (201/100)*L by positivity)
  have hcap : (201/100)*L*Real.sqrt 3 ≤ (7/2)*L := by nlinarith
  refine ⟨?_, ?_⟩
  · intro k
    exact (hv k).trans ((le_div_iff₀ hs).mpr hcap)
  · have hn := GeometryCoverage.coordinate_norm_bound (by positivity) hv
    nlinarith

/-- Given the actual clamped segment parameter, the final AX FMA and both
    face edges satisfy the same 3.5L geometry, including AX+E and AX+F. -/
theorem crossing_face_geometry (I : Interchange) [I.Valid]
    {a b c p₀ p₁ : Vec3 I} {sw : I.Word} {s : ℚ}
    {A B C P₀ P₁ : Fin 3 → ℚ} {L : ℝ}
    (ha : ∀ k, value? I (a k) = some (A k)) (hb : ∀ k, value? I (b k) = some (B k))
    (hc : ∀ k, value? I (c k) = some (C k))
    (hp0 : ∀ k, value? I (p₀ k) = some (P₀ k)) (hp1 : ∀ k, value? I (p₁ k) = some (P₁ k))
    (hs : value? I sw = some s) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hL : 0 ≤ L) (hA : ∀ k, |(A k : ℝ)| ≤ L) (hB : ∀ k, |(B k : ℝ)| ≤ L)
    (hC : ∀ k, |(C k : ℝ)| ≤ L) (hP0 : ∀ k, |(P₀ k : ℝ)| ≤ L) (hP1 : ∀ k, |(P₁ k : ℝ)| ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1/16777216)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ∃ e f ax : Fin 3 → ℚ,
      (∀ k, value? I (vsub I b a k) = some (e k)) ∧
      (∀ k, value? I (vsub I c a k) = some (f k)) ∧
      (∀ k, value? I (fma3 I (neg I sw) (vsub I p₁ p₀) (vsub I a p₀) k) = some (ax k)) ∧
      (∀ k, |(e k : ℝ)| ≤ ((7/2)*L)/Real.sqrt 3) ∧
      (∀ k, |(f k : ℝ)| ≤ ((7/2)*L)/Real.sqrt 3) ∧
      (∀ k, |(ax k : ℝ)| ≤ ((7/2)*L)/Real.sqrt 3) ∧
      ‖realVec e‖ ≤ (7/2)*L ∧ ‖realVec f‖ ≤ (7/2)*L ∧ ‖realVec ax‖ ≤ (7/2)*L ∧
      ‖realVec ax+realVec e‖ ≤ (7/2)*L ∧ ‖realVec ax+realVec f‖ ≤ (7/2)*L ∧
      (∀ k, |(ax k : ℝ)-((A k : ℝ)-((1-(s : ℝ))*(P₀ k : ℝ)+(s : ℝ)*(P₁ k : ℝ)))|
        ≤ 9*I.format.unitRoundoff*L) := by
  have hr := I.format.unitRoundoff_pos.le
  have hrmax : I.format.unitRoundoff ≤ 1/1024 := by linarith
  have hsub : 3*L < I.format.overflowThreshold := by linarith
  choose e he heErr heBound using fun k => sub_coordinates I (hb k) (ha k) hL (hB k) (hA k) hrmax heta hsub
  choose f hf hfErr hfBound using fun k => sub_coordinates I (hc k) (ha k) hL (hC k) (hA k) hrmax heta hsub
  choose p hp hpErr hpBound using fun k => sub_coordinates I (hp1 k) (hp0 k) hL (hP1 k) (hP0 k) hrmax heta hsub
  choose ap hap hapErr hapBound using fun k => sub_coordinates I (ha k) (hp0 k) hL (hA k) (hP0 k) hrmax heta hsub
  have hs0r : (0:ℝ) ≤ (s : ℝ) := by exact_mod_cast hs0
  have hs1r : (s : ℝ) ≤ 1 := by exact_mod_cast hs1
  have hsabs : |((-s : ℚ) : ℝ)| ≤ 1 := by simpa [abs_of_nonneg hs0r] using hs1r
  have hr2 := mul_self_le_mul_self hr hrmax
  choose ax hax haxErr _ using fun k => affine_step I (ReconstructionIEEE.neg_value I hs)
    (hp k) (hap k) hL hsabs (hpBound k) (hapBound k) heta (by nlinarith) (by linarith)
  have haxExact : ∀ k, |(ax k : ℝ)-((A k : ℝ)-((1-(s : ℝ))*(P₀ k : ℝ)+(s : ℝ)*(P₁ k : ℝ)))|
      ≤ 9*I.format.unitRoundoff*L := by
    intro k
    exact anchor_error hr hrmax hL heta (hA k) (hP0 k) (hP1 k) hs0r hs1r (hpErr k) (hapErr k)
      (by simpa [Rat.cast_neg, sub_eq_add_neg, add_comm] using haxErr k)
  have edge_error (z v : Fin 3 → ℚ) (hz : ∀ k, |(z k : ℝ)| ≤ L)
      (hv : ∀ k, RoundError I.format.unitRoundoff I.format.minSubnormal ((z k : ℝ)-(A k : ℝ)) (v k : ℝ)) :
      ∀ k, |(v k : ℝ)-((z k : ℝ)-(A k : ℝ))| ≤ 3*I.format.unitRoundoff*L :=
    fun k => round_difference hr hrmax hL heta (hz k) (hA k) (hv k)
  have heExact := edge_error B e hB heErr
  have hfExact := edge_error C f hC hfErr
  have hbudget : (2+12*I.format.unitRoundoff)*L ≤ (201/100)*L := by
    have hh := mul_le_mul_of_nonneg_right hrho hL
    nlinarith
  have edge_bound (z v : Fin 3 → ℚ) (hz : ∀ k, |(z k : ℝ)| ≤ L)
      (hv : ∀ k, |(v k : ℝ)-((z k : ℝ)-(A k : ℝ))| ≤ 3*I.format.unitRoundoff*L) :
      ∀ k, |(v k : ℝ)| ≤ (201/100)*L := by
    intro k
    have hd := difference_abs (hz k) (hA k)
    have hh := abs_add_le ((v k : ℝ)-((z k : ℝ)-(A k : ℝ))) ((z k : ℝ)-(A k : ℝ))
    rw [sub_add_cancel] at hh
    have hvk := hv k
    nlinarith [mul_nonneg hr hL]
  have haxBound : ∀ k, |(ax k : ℝ)| ≤ (201/100)*L := by
    intro k
    have hp := interval_abs hL (hP0 k) (hP1 k) hs0r hs1r
    have hd := difference_abs (hA k) hp
    have hh := abs_add_le ((ax k : ℝ)-((A k : ℝ)-((1-(s : ℝ))*(P₀ k : ℝ)+(s : ℝ)*(P₁ k : ℝ))))
      ((A k : ℝ)-((1-(s : ℝ))*(P₀ k : ℝ)+(s : ℝ)*(P₁ k : ℝ)))
    rw [sub_add_cancel] at hh
    have hvk := haxExact k
    nlinarith [mul_nonneg hr hL]
  have sum_bound (z v : Fin 3 → ℚ) (hz : ∀ k, |(z k : ℝ)| ≤ L)
      (hv : ∀ k, |(v k : ℝ)-((z k : ℝ)-(A k : ℝ))| ≤ 3*I.format.unitRoundoff*L) :
      ∀ k, |(realVec ax+realVec v) k| ≤ (201/100)*L := by
    intro k
    let point := (1-(s : ℝ))*(P₀ k : ℝ)+(s : ℝ)*(P₁ k : ℝ)
    have hp := interval_abs hL (hP0 k) (hP1 k) hs0r hs1r
    have hd := difference_abs (hz k) hp
    have hh := abs_add_le ((ax k : ℝ)-((A k : ℝ)-point)) ((v k : ℝ)-((z k : ℝ)-(A k : ℝ)))
    have hh' := abs_add_le (((ax k : ℝ)-((A k : ℝ)-point))+((v k : ℝ)-((z k : ℝ)-(A k : ℝ)))) ((z k : ℝ)-point)
    have hid : ((ax k : ℝ)-((A k : ℝ)-point))+((v k : ℝ)-((z k : ℝ)-(A k : ℝ)))+((z k : ℝ)-point) =
        (realVec ax+realVec v) k := by simp [realVec]; ring
    rw [hid] at hh'
    have h0 := haxExact k
    have h1 := hv k
    change |(ax k : ℝ)-((A k : ℝ)-point)| ≤ _ at h0
    change |(z k : ℝ)-point| ≤ _ at hd
    nlinarith
  obtain ⟨heC, heN⟩ := coordinate_201_bound (v := realVec e) hL (edge_bound B e hB heExact)
  obtain ⟨hfC, hfN⟩ := coordinate_201_bound (v := realVec f) hL (edge_bound C f hC hfExact)
  obtain ⟨haxC, haxN⟩ := coordinate_201_bound (v := realVec ax) hL haxBound
  have hsumE := (coordinate_201_bound hL (sum_bound B e hB heExact)).2
  have hsumF := (coordinate_201_bound hL (sum_bound C f hC hfExact)).2
  exact ⟨e, f, ax, he, hf, hax, heC, hfC, haxC, heN, hfN, haxN, hsumE, hsumF, haxExact⟩

/-- Sharp displacement of any decoded actual crossing AX from the common
    rounded affine geometry. Output decoding is used only to identify words. -/
theorem crossing_anchor_displacement (I : Interchange) [I.Valid]
    {APw Pw : Vec3 I} {sw : I.Word} {s : ℚ} {ap p ax : Fin 3 → ℚ} {D : ℝ}
    (hAP : ∀ k, value? I (APw k) = some (ap k))
    (hP : ∀ k, value? I (Pw k) = some (p k))
    (hs : value? I sw = some s)
    (hax : ∀ k, value? I (fma3 I (neg I sw) Pw APw k) = some (ax k))
    (hD : ‖realVec ap-(s : ℝ)•realVec p‖ ≤ D)
    (hlim : D < I.format.overflowThreshold) :
    ‖realVec ax-(realVec ap-(s : ℝ)•realVec p)‖ ≤ I.format.unitRoundoff*D+I.format.minSubnormal := by
  have hid : ((-s : ℚ) : ℝ)•realVec p+realVec ap = realVec ap-(s : ℝ)•realVec p := by
    simp only [Rat.cast_neg]; module
  obtain ⟨out, hout, herr⟩ := ProjectionRounding.fma3_finite_norm_error I
    (ReconstructionIEEE.neg_value I hs) hP hAP (by rw [hid]; exact hD.trans_lt hlim)
  have heq : out = ax := funext (fun k => Option.some.inj ((hout k).symm.trans (hax k)))
  subst out
  rw [hid] at herr
  exact herr.trans (add_le_add (mul_le_mul_of_nonneg_left hD I.format.unitRoundoff_pos.le) (le_refl _))

end DistanceAccuracy.CrossingCoordinates

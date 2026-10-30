import DistanceAccuracy.CrossingCoordinates

/-! Witness transfers instantiated with the actual IEEE subtraction and FMA
    words. No local rounding-error hypotheses are supplied by callers. -/
namespace DistanceAccuracy.WordGeometryTransfer
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant
open GeometryCoverage Reconstruction
variable (I : Interchange) [I.Valid]

lemma decoded_sub_error {a b : I.Word} {A B R : ℚ} {L : ℝ}
    (ha : value? I a = some A) (hb : value? I b = some B)
    (hr : value? I (sub I a b) = some R)
    (hL : 0 ≤ L) (hA : |(A : ℝ)| ≤ L) (hB : |(B : ℝ)| ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    RoundError I.format.unitRoundoff I.format.minSubnormal ((A : ℝ)-(B : ℝ)) (R : ℝ) := by
  obtain ⟨r, hd, he, _⟩ := ReconstructionIEEE.sub_coordinates I ha hb hL hA hB hrho heta (by linarith)
  have hh : r = R := Option.some.inj (hd.symm.trans hr)
  simpa only [hh] using he

/-- Each actual independently rounded edge has error at most ρ(3.5L). -/
theorem difference_error {a b : Vec3 I} {A B R : Fin 3 → ℚ} {L : ℝ}
    (ha : ∀ k, value? I (a k) = some (A k)) (hb : ∀ k, value? I (b k) = some (B k))
    (hr : ∀ k, value? I (vsub I a b k) = some (R k))
    (hL : 0 ≤ L) (hA : ∀ k, |(A k : ℝ)| ≤ L) (hB : ∀ k, |(B k : ℝ)| ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ‖realVec R-(realVec A-realVec B)‖ ≤ I.format.unitRoundoff*((7/2)*L) := by
  have hρ := I.format.unitRoundoff_pos.le
  have hη : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have herr := fun k => decoded_sub_error I (ha k) (hb k) (hr k) hL (hA k) (hB k) hrho heta hlim
  have he := difference_error_norm (A := realVec A) (B := realVec B)
    (e := realVec R-(realVec A-realVec B)) hA hB hρ hη herr
  have hs : Real.sqrt (3:ℝ) ≤ 26/15 := by apply Real.sqrt_le_iff.mpr; norm_num
  have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ 2*I.format.unitRoundoff*L+I.format.minSubnormal/2 by positivity)
  have hrL := mul_le_mul_of_nonneg_right hrho (mul_nonneg hρ hL)
  nlinarith

/-- Original exact segment/triangle witnesses transfer to the actual common
    rounded affine geometry with a 3ρD displacement, D=3.5L. -/
theorem original_common {a b c p₀ p₁ : Vec3 I}
    {A B C P₀ P₁ e f ap p : Fin 3 → ℚ} {L u v z : ℝ}
    (ha : ∀ k, value? I (a k) = some (A k)) (hb : ∀ k, value? I (b k) = some (B k))
    (hc : ∀ k, value? I (c k) = some (C k)) (hp0 : ∀ k, value? I (p₀ k) = some (P₀ k))
    (hp1 : ∀ k, value? I (p₁ k) = some (P₁ k))
    (he : ∀ k, value? I (vsub I b a k) = some (e k))
    (hf : ∀ k, value? I (vsub I c a k) = some (f k))
    (hap : ∀ k, value? I (vsub I a p₀ k) = some (ap k))
    (hp : ∀ k, value? I (vsub I p₁ p₀ k) = some (p k))
    (hL : 0 ≤ L) (hA : ∀ k, |(A k : ℝ)| ≤ L) (hB : ∀ k, |(B k : ℝ)| ≤ L)
    (hC : ∀ k, |(C k : ℝ)| ≤ L) (hP0 : ∀ k, |(P₀ k : ℝ)| ≤ L) (hP1 : ∀ k, |(P₁ k : ℝ)| ≤ L)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ‖(realVec ap+u•realVec e+v•realVec f-z•realVec p)-
      ((realVec A+u•(realVec B-realVec A)+v•(realVec C-realVec A))-
        (realVec P₀+z•(realVec P₁-realVec P₀)))‖ ≤ 3*I.format.unitRoundoff*((7/2)*L) := by
  have heErr := difference_error I hb ha he hL hB hA hrho heta hlim
  have hfErr := difference_error I hc ha hf hL hC hA hrho heta hlim
  have hapErr := difference_error I ha hp0 hap hL hA hP0 hrho heta hlim
  have hpErr := difference_error I hp1 hp0 hp hL hP1 hP0 hrho heta hlim
  have hh := original_proxy_transfer hu hv huv hz0 hz1
    (show 0 ≤ I.format.unitRoundoff*((7/2)*L) by have := I.format.unitRoundoff_pos; positivity)
    heErr hfErr hapErr hpErr
  convert hh using 1
  · congr 1; module
  · ring

/-- Shift to the actual crossing AX adds its proved FMA displacement. -/
theorem shifted_original {a b c p₀ p₁ : Vec3 I} {sw : I.Word} {s : ℚ}
    {A B C P₀ P₁ e f ap p ax : Fin 3 → ℚ} {L u v : ℝ}
    (ha : ∀ k, value? I (a k) = some (A k)) (hb : ∀ k, value? I (b k) = some (B k))
    (hc : ∀ k, value? I (c k) = some (C k)) (hp0 : ∀ k, value? I (p₀ k) = some (P₀ k))
    (hp1 : ∀ k, value? I (p₁ k) = some (P₁ k))
    (he : ∀ k, value? I (vsub I b a k) = some (e k))
    (hf : ∀ k, value? I (vsub I c a k) = some (f k))
    (hap : ∀ k, value? I (vsub I a p₀ k) = some (ap k))
    (hp : ∀ k, value? I (vsub I p₁ p₀ k) = some (p k))
    (hs : value? I sw = some s)
    (hax : ∀ k, value? I (fma3 I (neg I sw) (vsub I p₁ p₀) (vsub I a p₀) k) = some (ax k))
    (hL : 0 ≤ L) (hA : ∀ k, |(A k : ℝ)| ≤ L) (hB : ∀ k, |(B k : ℝ)| ≤ L)
    (hC : ∀ k, |(C k : ℝ)| ≤ L) (hP0 : ∀ k, |(P₀ k : ℝ)| ≤ L) (hP1 : ∀ k, |(P₁ k : ℝ)| ≤ L)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hAX : ‖realVec ap-(s : ℝ)•realVec p‖ ≤ (7/2)*L)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ‖(realVec ax+u•realVec e+v•realVec f)-
      ((realVec A+u•(realVec B-realVec A)+v•(realVec C-realVec A))-
        (realVec P₀+(s : ℝ)•(realVec P₁-realVec P₀)))‖ ≤ (201/50)*I.format.unitRoundoff*((7/2)*L) := by
  have hbase := original_common I (z := (s : ℝ)) ha hb hc hp0 hp1 he hf hap hp hL hA hB hC hP0 hP1
    hu hv huv (by exact_mod_cast hs0) (by exact_mod_cast hs1) hrho heta hlim
  have hshift := CrossingCoordinates.crossing_anchor_displacement I hap hp hs hax hAX (by linarith)
  have hh := norm_add_le
    ((realVec ap+u•realVec e+v•realVec f-(s : ℝ)•realVec p)-
      ((realVec A+u•(realVec B-realVec A)+v•(realVec C-realVec A))-
        (realVec P₀+(s : ℝ)•(realVec P₁-realVec P₀))))
    (realVec ax-(realVec ap-(s : ℝ)•realVec p))
  have hid : ((realVec ap+u•realVec e+v•realVec f-(s : ℝ)•realVec p)-
      ((realVec A+u•(realVec B-realVec A)+v•(realVec C-realVec A))-
        (realVec P₀+(s : ℝ)•(realVec P₁-realVec P₀))))+
    (realVec ax-(realVec ap-(s : ℝ)•realVec p)) =
    (realVec ax+u•realVec e+v•realVec f)-
      ((realVec A+u•(realVec B-realVec A)+v•(realVec C-realVec A))-
        (realVec P₀+(s : ℝ)•(realVec P₁-realVec P₀))) := by module
  rw [hid] at hh
  have hm := mul_le_mul_of_nonneg_right hrho (mul_nonneg I.format.unitRoundoff_pos.le hL)
  nlinarith

/-- Actual directly anchored BC edge geometry differs from the common
    triangle geometry by at most4ρD, including independent rounding. -/
theorem bc_common {a b c p : Vec3 I}
    {A B C P e f ap bp cb : Fin 3 → ℚ} {L t : ℝ}
    (ha : ∀ k, value? I (a k) = some (A k)) (hb : ∀ k, value? I (b k) = some (B k))
    (hc : ∀ k, value? I (c k) = some (C k)) (hp : ∀ k, value? I (p k) = some (P k))
    (he : ∀ k, value? I (vsub I b a k) = some (e k))
    (hf : ∀ k, value? I (vsub I c a k) = some (f k))
    (hap : ∀ k, value? I (vsub I a p k) = some (ap k))
    (hbp : ∀ k, value? I (vsub I b p k) = some (bp k))
    (hcb : ∀ k, value? I (vsub I c b k) = some (cb k))
    (hL : 0 ≤ L) (hA : ∀ k, |(A k : ℝ)| ≤ L) (hB : ∀ k, |(B k : ℝ)| ≤ L)
    (hC : ∀ k, |(C k : ℝ)| ≤ L) (hP : ∀ k, |(P k : ℝ)| ≤ L)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ‖(realVec bp+t•realVec cb)-(realVec ap+(1-t)•realVec e+t•realVec f)‖ ≤
      4*I.format.unitRoundoff*((7/2)*L) := by
  have hρ := I.format.unitRoundoff_pos.le
  have hη : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hbe := fun k => decoded_sub_error I (hb k) (hp k) (hbp k) hL (hB k) (hP k) hrho heta hlim
  have hce := fun k => decoded_sub_error I (hc k) (hb k) (hcb k) hL (hC k) (hB k) hrho heta hlim
  have hae := fun k => decoded_sub_error I (ha k) (hp k) (hap k) hL (hA k) (hP k) hrho heta hlim
  have hee := fun k => decoded_sub_error I (hb k) (ha k) (he k) hL (hB k) (hA k) hrho heta hlim
  have hfe := fun k => decoded_sub_error I (hc k) (ha k) (hf k) hL (hC k) (hA k) hrho heta hlim
  have hh := bc_vector_transfer (A := realVec A) (B := realVec B) (C := realVec C) (P := realVec P)
    (eBP := realVec bp-(realVec B-realVec P)) (eCB := realVec cb-(realVec C-realVec B))
    (eAP := realVec ap-(realVec A-realVec P)) (eBA := realVec e-(realVec B-realVec A))
    (eCA := realVec f-(realVec C-realVec A)) hA hB hC hP ht0 ht1 hρ hη hbe hce hae hee hfe
  have hid : (realVec bp-(realVec B-realVec P))+t•(realVec cb-(realVec C-realVec B))-
      (realVec ap-(realVec A-realVec P))-(1-t)•(realVec e-(realVec B-realVec A))-
      t•(realVec f-(realVec C-realVec A)) =
      (realVec bp+t•realVec cb)-(realVec ap+(1-t)•realVec e+t•realVec f) := by module
  rw [hid] at hh
  have hs : Real.sqrt (3:ℝ) ≤ 26/15 := by apply Real.sqrt_le_iff.mpr; norm_num
  have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ 8*I.format.unitRoundoff*L+2*I.format.minSubnormal by positivity)
  have hrL := mul_le_mul_of_nonneg_right hrho (mul_nonneg hρ hL)
  nlinarith

omit [I.Valid] in
/-- The shifted BC fallback combines the actual cycle and AX displacement
    budgets; both constituent bounds have concrete word theorems above. -/
lemma shifted_cycle {E F AP BP CB P AX : Determinant.E3} {L t z : ℝ}
    (hL : 0 ≤ L) (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hcycle : ‖(BP+t•CB)-(AP+(1-t)•E+t•F)‖ ≤ 4*I.format.unitRoundoff*((7/2)*L))
    (hshift : ‖AX-(AP-z•P)‖ ≤ I.format.unitRoundoff*((7/2)*L)+I.format.minSubnormal) :
    ‖(BP+t•CB-z•P)-(AX+(1-t)•E+t•F)‖ ≤ (251/50)*I.format.unitRoundoff*((7/2)*L) := by
  have hh := norm_sub_le ((BP+t•CB)-(AP+(1-t)•E+t•F)) (AX-(AP-z•P))
  have hid : ((BP+t•CB)-(AP+(1-t)•E+t•F))-(AX-(AP-z•P)) =
      (BP+t•CB-z•P)-(AX+(1-t)•E+t•F) := by module
  rw [hid] at hh
  have hm := mul_le_mul_of_nonneg_right hrho (mul_nonneg I.format.unitRoundoff_pos.le hL)
  nlinarith

end DistanceAccuracy.WordGeometryTransfer

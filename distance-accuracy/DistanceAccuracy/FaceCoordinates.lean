import DistanceAccuracy.ReconstructionIEEE
import DistanceAccuracy.WordDeterminantVector
import DistanceAccuracy.GeometryTransfer

/-! Shared rounded-coordinate geometry for face-local estimates. -/
namespace DistanceAccuracy.FaceCoordinates
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant

noncomputable def diameter (I : Interchange) (L : ℝ) : ℝ :=
  Real.sqrt 3 * (2*(1+I.format.unitRoundoff)*L+I.format.minSubnormal/2)

lemma diameter_bound (I : Interchange) {L : ℝ} (hL : 0 ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L) :
    0 ≤ diameter I L ∧ diameter I L ≤ (7/2)*L := by
  have hr := I.format.unitRoundoff_pos.le
  have he : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hs : Real.sqrt 3 ≤ 26/15 := by apply Real.sqrt_le_iff.mpr; norm_num
  have hrs : I.format.unitRoundoff^2 ≤ (1/1024:ℝ)^2 := (sq_le_sq₀ hr (by norm_num)).2 hrho
  have hb : 2*(1+I.format.unitRoundoff)+I.format.unitRoundoff^2/2 ≤ 201/100 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hb hL
  have hK : 2*(1+I.format.unitRoundoff)*L+I.format.minSubnormal/2 ≤ (201/100)*L := by nlinarith
  have hK0 : 0 ≤ 2*(1+I.format.unitRoundoff)*L+I.format.minSubnormal/2 := by positivity
  have hprod := mul_le_mul hs hK hK0 (by norm_num : (0:ℝ) ≤ 26/15)
  refine ⟨by unfold diameter; positivity, ?_⟩
  unfold diameter
  nlinarith

/-- Actual coordinate subtraction gives the common D/sqrt(3) coordinate
    bound and norm bound D used by every local face theorem. -/
theorem difference_data (I : Interchange) [I.Valid] {x y : Vec3 I}
    {X Y : Fin 3 → ℚ} {L : ℝ}
    (hx : ∀ k, value? I (x k) = some (X k)) (hy : ∀ k, value? I (y k) = some (Y k))
    (hL : 0 ≤ L) (hX : ∀ k, |(X k : ℝ)| ≤ L) (hY : ∀ k, |(Y k : ℝ)| ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ∃ R : Fin 3 → ℚ, (∀ k, value? I (vsub I y x k) = some (R k)) ∧
      (∀ k, |(R k : ℝ)| ≤ diameter I L/Real.sqrt 3) ∧
      ‖realVec R‖ ≤ diameter I L ∧
      (∀ k, Reconstruction.RoundError I.format.unitRoundoff I.format.minSubnormal
        ((Y k : ℝ)-(X k : ℝ)) (R k : ℝ)) := by
  choose R hR he _ using fun k => ReconstructionIEEE.sub_coordinates I
    (hy k) (hx k) hL (hY k) (hX k) hrho heta (by linarith)
  have hr := I.format.unitRoundoff_pos.le
  have heta0 : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hK0 : 0 ≤ 2*(1+I.format.unitRoundoff)*L+I.format.minSubnormal/2 := by positivity
  have hb : ∀ k, |(R k : ℝ)| ≤ 2*(1+I.format.unitRoundoff)*L+I.format.minSubnormal/2 := by
    intro k
    have hh := he k
    unfold Reconstruction.RoundError at hh
    have hd := Reconstruction.difference_abs (hY k) (hX k)
    have hm := mul_le_mul_of_nonneg_left hd hr
    have ht := abs_add_le ((R k : ℝ)-((Y k : ℝ)-(X k : ℝ))) ((Y k : ℝ)-(X k : ℝ))
    rw [sub_add_cancel] at ht
    nlinarith
  refine ⟨R, hR, ?_, GeometryCoverage.coordinate_norm_bound hK0 hb, he⟩
  intro k
  have hs : Real.sqrt (3:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hid : diameter I L/Real.sqrt 3 = 2*(1+I.format.unitRoundoff)*L+I.format.minSubnormal/2 := by
    unfold diameter
    field_simp
  rw [hid]
  exact hb k

lemma shared_anchor_norm (I : Interchange) {A B X E R : E3} {L : ℝ}
    (hL : 0 ≤ L) (hA : ∀ k, |A k| ≤ L) (hB : ∀ k, |B k| ≤ L)
    (hX : ∀ k, |X k| ≤ L)
    (he : ∀ k, Reconstruction.RoundError I.format.unitRoundoff I.format.minSubnormal (B k-A k) (E k))
    (hr : ∀ k, Reconstruction.RoundError I.format.unitRoundoff I.format.minSubnormal (A k-X k) (R k))
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L) :
    ‖R+E‖ ≤ (7/2)*L := by
  have hρ := I.format.unitRoundoff_pos.le
  have hη : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hcoords : ∀ k, |(R+E) k| ≤ 2*L+4*I.format.unitRoundoff*L+I.format.minSubnormal := by
    intro k
    have he' := he k
    have hr' := hr k
    unfold Reconstruction.RoundError at he' hr'
    have heD := Reconstruction.difference_abs (hB k) (hA k)
    have hrD := Reconstruction.difference_abs (hA k) (hX k)
    have hbD := Reconstruction.difference_abs (hB k) (hX k)
    have heM := mul_le_mul_of_nonneg_left heD hρ
    have hrM := mul_le_mul_of_nonneg_left hrD hρ
    have h1 := abs_add_le (R k-(A k-X k)) (E k-(B k-A k))
    have h2 := abs_add_le ((R k-(A k-X k))+(E k-(B k-A k))) (B k-X k)
    have hid : (R k-(A k-X k))+(E k-(B k-A k))+(B k-X k) = (R+E) k := by simp; ring
    rw [hid] at h2
    linarith
  have hn := GeometryCoverage.coordinate_norm_bound (by positivity) hcoords
  have hs : Real.sqrt 3 ≤ 26/15 := by apply Real.sqrt_le_iff.mpr; norm_num
  have hrs : I.format.unitRoundoff^2 ≤ (1/1024:ℝ)^2 := (sq_le_sq₀ hρ (by norm_num)).2 hrho
  have hbudget : 2+4*I.format.unitRoundoff+I.format.unitRoundoff^2 ≤ 201/100 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hbudget hL
  have hscalar : 2*L+4*I.format.unitRoundoff*L+I.format.minSubnormal ≤ (201/100)*L := by nlinarith
  have hp := mul_le_mul hs hscalar (by positivity) (by norm_num : (0:ℝ) ≤ 26/15)
  nlinarith

/-- Shared-anchor geometry for actual rounded face differences. The joint
    residuals R+E and R+F include both independent subtraction errors. -/
theorem face_geometry (I : Interchange) [I.Valid] {a b c x : Vec3 I}
    {A B C X : Fin 3 → ℚ} {L : ℝ}
    (ha : ∀ k, value? I (a k) = some (A k)) (hb : ∀ k, value? I (b k) = some (B k))
    (hc : ∀ k, value? I (c k) = some (C k)) (hx : ∀ k, value? I (x k) = some (X k))
    (hL : 0 ≤ L) (hA : ∀ k, |(A k : ℝ)| ≤ L) (hB : ∀ k, |(B k : ℝ)| ≤ L)
    (hC : ∀ k, |(C k : ℝ)| ≤ L) (hX : ∀ k, |(X k : ℝ)| ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ∃ e f r : Fin 3 → ℚ,
      (∀ k, value? I (vsub I b a k) = some (e k)) ∧
      (∀ k, value? I (vsub I c a k) = some (f k)) ∧
      (∀ k, value? I (vsub I a x k) = some (r k)) ∧
      (∀ k, |(e k : ℝ)| ≤ ((7/2)*L)/Real.sqrt 3) ∧
      (∀ k, |(f k : ℝ)| ≤ ((7/2)*L)/Real.sqrt 3) ∧
      (∀ k, |(r k : ℝ)| ≤ ((7/2)*L)/Real.sqrt 3) ∧
      ‖realVec e‖ ≤ (7/2)*L ∧ ‖realVec f‖ ≤ (7/2)*L ∧ ‖realVec r‖ ≤ (7/2)*L ∧
      ‖realVec r+realVec e‖ ≤ (7/2)*L ∧ ‖realVec r+realVec f‖ ≤ (7/2)*L := by
  obtain ⟨e, he, heC, heN, heErr⟩ := difference_data I ha hb hL hA hB hrho heta hlim
  obtain ⟨f, hf, hfC, hfN, hfErr⟩ := difference_data I ha hc hL hA hC hrho heta hlim
  obtain ⟨r, hr, hrC, hrN, hrErr⟩ := difference_data I hx ha hL hX hA hrho heta hlim
  have hdiam := (diameter_bound I hL hrho heta).2
  have hdiv := div_le_div_of_nonneg_right hdiam (Real.sqrt_nonneg 3)
  refine ⟨e, f, r, he, hf, hr, fun k => (heC k).trans hdiv,
    fun k => (hfC k).trans hdiv, fun k => (hrC k).trans hdiv,
    heN.trans hdiam, hfN.trans hdiam, hrN.trans hdiam, ?_, ?_⟩
  · exact shared_anchor_norm I (A := realVec A) (B := realVec B) (X := realVec X)
      hL hA hB hX heErr hrErr hrho heta
  · exact shared_anchor_norm I (A := realVec A) (B := realVec C) (X := realVec X)
      hL hA hC hX hfErr hrErr hrho heta

end DistanceAccuracy.FaceCoordinates

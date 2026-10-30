import DistanceAccuracy.ThreeDotsAdmissible
import DistanceAccuracy.WordDirectSolve
import DistanceAccuracy.WordEndpointSolve

/-! Range-free local projection theorems for the actual segment solves. -/
namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds Determinant
set_option exponentiation.threshold 2048
set_option maxHeartbeats 1000000

lemma numerator_range (fmt : Format) {L D b d t : ℝ}
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hD : 0 ≤ D) (hDL : D ≤ 9*L) (ht : |t| ≤ 1)
    (hb : |b| ≤ 2*D^2+2*fmt.interchange.format.minSubnormal)
    (hd : |d| ≤ 2*D^2+2*fmt.interchange.format.minSubnormal) :
    |t*b+d| < fmt.interchange.format.overflowThreshold := by
  have hη : fmt.interchange.format.minSubnormal ≤ 1 := by
    cases fmt <;> norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.minSubnormal]
  have he : 0 ≤ fmt.interchange.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hm := mul_le_mul ht hb (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hh := abs_add_le (t*b) d
  rw [abs_mul] at hh
  have hr := fmt.quadratic_range hL hadm
  have hs : D^2 ≤ (9*L)^2 := by gcongr
  nlinarith [sq_nonneg L]

/-- The actual second segment parameter, with no local accuracy, finite-dot,
    or numerator-range assumptions. -/
theorem second_solve_admissible (fmt : Format)
    {Pw Qw Rw : Vec3 fmt.interchange} {p q r : Fin 3 → ℚ}
    {tw : fmt.interchange.Word} {t : ℚ} {D L : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hP : ∀ i, value? fmt.interchange (Pw i) = some (p i))
    (hQ : ∀ i, value? fmt.interchange (Qw i) = some (q i))
    (hR : ∀ i, value? fmt.interchange (Rw i) = some (r i))
    (ht : value? fmt.interchange tw = some t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hA : fourthRoot fmt.leastSubnormal < ‖realVec p‖) (hDL : D ≤ 9*L)
    (hpD : ‖realVec p‖ ≤ D) (hqD : ‖realVec q‖ ≤ D) (hrD : ‖realVec r‖ ≤ D)
    (hkD : ‖realVec r+(t : ℝ)•realVec q‖ ≤ D)
    (hpC : ∀ i, |(p i : ℝ)| ≤ D/Real.sqrt 3)
    (hqC : ∀ i, |(q i : ℝ)| ≤ D/Real.sqrt 3)
    (hrC : ∀ i, |(r i : ℝ)| ≤ D/Real.sqrt 3) :
    ∃ s : ℚ, value? fmt.interchange (clamp01nan fmt.interchange
      (div fmt.interchange (fma fmt.interchange tw (dot3 fmt.interchange Pw Qw) (dot3 fmt.interchange Pw Rw))
        (dot3 fmt.interchange Pw Pw))) = some s ∧ 0 ≤ s ∧ s ≤ 1 ∧
      ∀ sstar : ℝ, 0 ≤ sstar → sstar ≤ 1 →
      ‖(realVec r+(t : ℝ)•realVec q)+(s : ℝ)•(-realVec p)‖^2 ≤
        ‖(realVec r+(t : ℝ)•realVec q)+sstar•(-realVec p)‖^2+
        ((419/50)*fmt.interchange.format.unitRoundoff*D)^2+
        64*fmt.interchange.format.minSubnormal*(1+‖realVec p‖^2) := by
  obtain ⟨a, b, d, ha, hb, hd, hap, haErr, haSharp, hbSharp, hdSharp, hbMag, hdMag⟩ :=
    three_dots_admissible fmt hP hQ hR hL hadm hA hDL hpD hqD hrD hpC hqC hrC
  obtain ⟨s, hs, hs0, hs1⟩ := clamp01nan_bounded fmt.interchange hone
    (div fmt.interchange (fma fmt.interchange tw (dot3 fmt.interchange Pw Qw) (dot3 fmt.interchange Pw Rw))
      (dot3 fmt.interchange Pw Pw))
  have hD : 0 ≤ D := (norm_nonneg _).trans hpD
  have hne : realVec p ≠ 0 := by
    have hh := lt_of_le_of_lt (fourthRoot_nonneg _) hA
    exact norm_pos_iff.mp hh
  have hρmax : fmt.interchange.format.unitRoundoff ≤ 1/16777216 := by
    have hh := fmt.rho_le
    cases fmt <;> norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32,
      FP.IEEE.binary64, FP.IEEE.Format.unitRoundoff]
  have hlim1 : (1:ℝ) < fmt.interchange.format.overflowThreshold := by
    have hh := fmt.quadratic_range hL hadm
    nlinarith [sq_nonneg L]
  have ht0r : (0:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht0
  have ht1r : (t : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hn := numerator_range fmt hL hadm hD hDL
    (show |(t : ℝ)| ≤ 1 by rwa [abs_of_nonneg ht0r]) hbMag hdMag
  refine ⟨s, hs, hs0, hs1, ?_⟩
  intro sstar hsstar0 hsstar1
  exact second_word_projection_loss fmt.interchange hone ha hb hd ht hs hap hne hD hpD hkD
    ht0r ht1r (by exact_mod_cast hs0) (by exact_mod_cast hs1) hsstar0 hsstar1 hρmax hlim1 hn
    haErr haSharp hbSharp hdSharp

/-- A direct actual dot quotient has the same conservative local loss bound. -/
theorem direct_solve_admissible (fmt : Format)
    {Ew Rw : Vec3 fmt.interchange} {e r : Fin 3 → ℚ} {D L : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hE : ∀ i, value? fmt.interchange (Ew i) = some (e i))
    (hR : ∀ i, value? fmt.interchange (Rw i) = some (r i))
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hA : fourthRoot fmt.leastSubnormal < ‖realVec e‖) (hDL : D ≤ 9*L)
    (heD : ‖realVec e‖ ≤ D) (hrD : ‖realVec r‖ ≤ D)
    (heC : ∀ i, |(e i : ℝ)| ≤ D/Real.sqrt 3)
    (hrC : ∀ i, |(r i : ℝ)| ≤ D/Real.sqrt 3) :
    ∃ s : ℚ, value? fmt.interchange (clamp01nan fmt.interchange
      (div fmt.interchange (neg fmt.interchange (dot3 fmt.interchange Ew Rw)) (dot3 fmt.interchange Ew Ew))) = some s ∧
      0 ≤ s ∧ s ≤ 1 ∧ ∀ sstar : ℝ, 0 ≤ sstar → sstar ≤ 1 →
      ‖realVec r+(s : ℝ)•realVec e‖^2 ≤ ‖realVec r+sstar•realVec e‖^2+
        ((419/50)*fmt.interchange.format.unitRoundoff*D)^2+
        64*fmt.interchange.format.minSubnormal*(1+‖realVec e‖^2) := by
  obtain ⟨a, _, d, ha, _, hd, hap, haErr, haSharp, _, hdSharp, _, _⟩ :=
    three_dots_admissible fmt hE hE hR hL hadm hA hDL heD heD hrD heC heC hrC
  obtain ⟨s, hs, hs0, hs1⟩ := clamp01nan_bounded fmt.interchange hone
    (div fmt.interchange (neg fmt.interchange (dot3 fmt.interchange Ew Rw)) (dot3 fmt.interchange Ew Ew))
  have hD : 0 ≤ D := (norm_nonneg _).trans heD
  have hne : realVec e ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (fourthRoot_nonneg _) hA)
  have hρmax : fmt.interchange.format.unitRoundoff ≤ 1/16777216 := by
    cases fmt <;> norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32,
      FP.IEEE.binary64, FP.IEEE.Format.unitRoundoff]
  have hlim1 : (1:ℝ) < fmt.interchange.format.overflowThreshold := by
    have hh := fmt.quadratic_range hL hadm
    nlinarith [sq_nonneg L]
  refine ⟨s, hs, hs0, hs1, ?_⟩
  intro sstar hsstar0 hsstar1
  exact direct_word_projection_loss fmt.interchange hone ha hd hs hap hne hD heD hrD
    (by exact_mod_cast hs0) (by exact_mod_cast hs1) hsstar0 hsstar1 hρmax hlim1 haErr haSharp hdSharp

/-- Actual endpoint `(dot(P,Q)-dot(Q,R))/dot(Q,Q)` projection. The mixed
    numerator dot retains the implementation's original operand order. -/
theorem endpoint_solve_admissible (fmt : Format)
    {Pw Qw Rw : Vec3 fmt.interchange} {p q r : Fin 3 → ℚ} {D L : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hP : ∀ i, value? fmt.interchange (Pw i) = some (p i))
    (hQ : ∀ i, value? fmt.interchange (Qw i) = some (q i))
    (hR : ∀ i, value? fmt.interchange (Rw i) = some (r i))
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hA : fourthRoot fmt.leastSubnormal < ‖realVec q‖) (hDL : D ≤ 9*L)
    (hpD : ‖realVec p‖ ≤ D) (hqD : ‖realVec q‖ ≤ D) (hrD : ‖realVec r‖ ≤ D)
    (hkD : ‖realVec r-realVec p‖ ≤ D)
    (hpC : ∀ i, |(p i : ℝ)| ≤ D/Real.sqrt 3)
    (hqC : ∀ i, |(q i : ℝ)| ≤ D/Real.sqrt 3)
    (hrC : ∀ i, |(r i : ℝ)| ≤ D/Real.sqrt 3) :
    ∃ s : ℚ, value? fmt.interchange (clamp01nan fmt.interchange
      (div fmt.interchange (sub fmt.interchange (dot3 fmt.interchange Pw Qw) (dot3 fmt.interchange Qw Rw))
        (dot3 fmt.interchange Qw Qw))) = some s ∧ 0 ≤ s ∧ s ≤ 1 ∧
      ∀ sstar : ℝ, 0 ≤ sstar → sstar ≤ 1 →
      ‖(realVec r-realVec p)+(s : ℝ)•realVec q‖^2 ≤
        ‖(realVec r-realVec p)+sstar•realVec q‖^2+
        ((419/50)*fmt.interchange.format.unitRoundoff*D)^2+
        64*fmt.interchange.format.minSubnormal*(1+‖realVec q‖^2) := by
  obtain ⟨a, _, e, ha, _, he, hap, haErr, haSharp, _, heSharp, _, heMag⟩ :=
    three_dots_admissible fmt hQ hP hR hL hadm hA hDL hqD hpD hrD hqC hpC hrC
  have hD : 0 < D := (lt_of_le_of_lt (fourthRoot_nonneg _) hA).trans_le hqD
  have hρ := fmt.interchange.format.unitRoundoff_pos.le
  have hη : 0 ≤ fmt.interchange.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hη1 : fmt.interchange.format.minSubnormal ≤ 1 := by
    cases fmt <;> norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.minSubnormal]
  have hρmax : fmt.interchange.format.unitRoundoff ≤ 1/16777216 := by
    cases fmt <;> norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.unitRoundoff]
  let B := D^2+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hηB : fmt.interchange.format.minSubnormal ≤ B := by dsimp [B]; nlinarith [sq_nonneg D]
  have hsqrt : 1 ≤ Real.sqrt (3:ℝ) := by apply (Real.le_sqrt (by norm_num) (by norm_num)).2; norm_num
  have hdiv := div_le_self hD.le hsqrt
  have hprod : ∀ i, |(p i : ℝ)*(q i : ℝ)| ≤ B := by
    intro i; rw [abs_mul]
    have hh := mul_le_mul ((hpC i).trans hdiv) ((hqC i).trans hdiv) (abs_nonneg _) hD.le
    dsimp [B]; nlinarith
  have hBmax : 6*B < fmt.interchange.format.overflowThreshold := by
    have hh := fmt.quadratic_range hL hadm
    have hs : D^2 ≤ (9*L)^2 := by gcongr
    dsimp [B]; nlinarith [sq_nonneg L]
  obtain ⟨b, hb, hbErr⟩ := DotWordBounds.dot3_finite_weighted fmt.interchange hP hQ hB hprod hηB (by linarith) hBmax
  change |(b : ℝ)-scalarDot p q| ≤ _ at hbErr
  rw [scalarDot_inner] at hbErr
  have hc : 0 ≤ fmt.interchange.format.unitRoundoff*(1+fmt.interchange.format.unitRoundoff)^2 := by positivity
  have hbSharp : |(b : ℝ)-inner ℝ (realVec p) (realVec q)| ≤
      (2161/1000)*fmt.interchange.format.unitRoundoff*(‖realVec q‖*D)*(1+fmt.interchange.format.unitRoundoff)^2+
      2*fmt.interchange.format.minSubnormal := by
    have hh := mul_le_mul_of_nonneg_left
      (DotWordBounds.weighted_general_scaled (a := realVec q) (b := realVec p) hD.le hpC) hc
    dsimp [realVec] at hh hbErr ⊢
    simp only [mul_comm] at hh
    nlinarith only [hh, hbErr]
  have hbMag : |(b : ℝ)| ≤ 2*D^2+2*fmt.interchange.format.minSubnormal := by
    have hh := mul_le_mul_of_nonneg_left (DotWordBounds.weighted_products_le_norm (realVec p) (realVec q)) hc
    have hn := mul_le_mul hpD hqD (norm_nonneg _) hD.le
    have hi := (abs_real_inner_le_norm (realVec p) (realVec q)).trans hn
    have hcoef := mul_le_mul_of_nonneg_right
      (FaceRanges.dot_coefficient hρ (by linarith : fmt.interchange.format.unitRoundoff ≤ 1/1024))
      (mul_nonneg (norm_nonneg (realVec p)) (norm_nonneg (realVec q)))
    have ht := abs_add_le ((b : ℝ)-inner ℝ (realVec p) (realVec q)) (inner ℝ (realVec p) (realVec q))
    rw [sub_add_cancel] at ht
    dsimp [realVec] at hh hbErr hn hi hcoef ht ⊢
    nlinarith only [hh, hbErr, hn, hi, hcoef, ht]
  obtain ⟨s, hs, hs0, hs1⟩ := clamp01nan_bounded fmt.interchange hone
    (div fmt.interchange (sub fmt.interchange (dot3 fmt.interchange Pw Qw) (dot3 fmt.interchange Qw Rw))
      (dot3 fmt.interchange Qw Qw))
  have hne : realVec q ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (fourthRoot_nonneg _) hA)
  have hlim1 : (1:ℝ) < fmt.interchange.format.overflowThreshold := by
    have hh := fmt.quadratic_range hL hadm
    nlinarith [sq_nonneg L]
  have hn : |(b : ℝ)-(e : ℝ)| < fmt.interchange.format.overflowThreshold := by
    have hh := numerator_range fmt hL hadm hD.le hDL (t := 1) (by norm_num) hbMag
      (d := -(e : ℝ)) (by simpa using heMag)
    simpa [sub_eq_add_neg] using hh
  refine ⟨s, hs, hs0, hs1, ?_⟩
  intro sstar hsstar0 hsstar1
  exact endpoint_word_projection_loss fmt.interchange hone ha hb he hs hap hne hD.le hqD hkD
    (by exact_mod_cast hs0) (by exact_mod_cast hs1) hsstar0 hsstar1 hρmax hlim1 hn haErr haSharp hbSharp heSharp

end DistanceAccuracy.ProjectionRounding

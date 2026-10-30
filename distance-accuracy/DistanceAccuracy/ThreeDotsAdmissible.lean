import DistanceAccuracy.FaceLocalAdmissible

/-! Shared actual-dot interface for the second and endpoint projection solves. -/
namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant DotWordBounds FaceRanges
set_option exponentiation.threshold 2048
set_option maxHeartbeats 1000000

/-- Three actual finite dot products, their sharp weighted error budgets,
    denominator positivity, and coarse numerator ranges. -/
theorem three_dots_admissible (fmt : Format)
    {E F R : Vec3 fmt.interchange} {e f r : Fin 3 → ℚ} {D L : ℝ}
    (hE : ∀ i, value? fmt.interchange (E i) = some (e i))
    (hF : ∀ i, value? fmt.interchange (F i) = some (f i))
    (hR : ∀ i, value? fmt.interchange (R i) = some (r i))
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hA : fourthRoot fmt.leastSubnormal < ‖realVec e‖) (hDL : D ≤ 9*L)
    (heD : ‖realVec e‖ ≤ D) (hfD : ‖realVec f‖ ≤ D) (hrD : ‖realVec r‖ ≤ D)
    (heC : ∀ i, |(e i : ℝ)| ≤ D/Real.sqrt 3)
    (hfC : ∀ i, |(f i : ℝ)| ≤ D/Real.sqrt 3)
    (hrC : ∀ i, |(r i : ℝ)| ≤ D/Real.sqrt 3) :
    ∃ a b d : ℚ,
      value? fmt.interchange (dot3 fmt.interchange E E) = some a ∧
      value? fmt.interchange (dot3 fmt.interchange E F) = some b ∧
      value? fmt.interchange (dot3 fmt.interchange E R) = some d ∧ 0 < a ∧
      |(a : ℝ)-‖realVec e‖^2| ≤ ‖realVec e‖^2 ∧
      |(a : ℝ)-‖realVec e‖^2| ≤ (2042/1000)*fmt.interchange.format.unitRoundoff*(‖realVec e‖*D)*(1+fmt.interchange.format.unitRoundoff)^2+2*fmt.interchange.format.minSubnormal ∧
      |(b : ℝ)-inner ℝ (realVec e) (realVec f)| ≤ (2161/1000)*fmt.interchange.format.unitRoundoff*(‖realVec e‖*D)*(1+fmt.interchange.format.unitRoundoff)^2+2*fmt.interchange.format.minSubnormal ∧
      |(d : ℝ)-inner ℝ (realVec e) (realVec r)| ≤ (2161/1000)*fmt.interchange.format.unitRoundoff*(‖realVec e‖*D)*(1+fmt.interchange.format.unitRoundoff)^2+2*fmt.interchange.format.minSubnormal ∧
      |(b : ℝ)| ≤ 2*D^2+2*fmt.interchange.format.minSubnormal ∧
      |(d : ℝ)| ≤ 2*D^2+2*fmt.interchange.format.minSubnormal := by
  let P := D^2+1
  have hρ : fmt.interchange.format.unitRoundoff = fmt.rho := by
    cases fmt
    · exact fp32_parameters.1
    · exact fp64_parameters.1
  have hη : fmt.interchange.format.minSubnormal = fmt.leastSubnormal := by
    cases fmt
    · exact fp32_parameters.2.2
    · exact fp64_parameters.2.2
  have hρ0 := fmt.interchange.format.unitRoundoff_pos.le
  have hρmax : fmt.interchange.format.unitRoundoff ≤ 1/1024 := by
    rw [hρ]; have hh := fmt.rho_le; norm_num at hh; linarith
  have hD : 0 < D := (lt_of_le_of_lt (fourthRoot_nonneg _) hA).trans_le heD
  have hP : 0 < P := by dsimp [P]; positivity
  have hηP : fmt.interchange.format.minSubnormal ≤ P := by
    have hh : fmt.leastSubnormal ≤ 1 := by cases fmt <;> norm_num [Format.leastSubnormal]
    rw [hη]; dsimp [P]; nlinarith [sq_nonneg D]
  have hPmax : 6*P < fmt.interchange.format.overflowThreshold := by
    have hh := fmt.quadratic_range hL hadm
    have hs : D^2 ≤ (9*L)^2 := by gcongr
    dsimp [P]; nlinarith [sq_nonneg L]
  have hsqrt : 1 ≤ Real.sqrt (3:ℝ) := by apply (Real.le_sqrt (by norm_num) (by norm_num)).2; norm_num
  have hdiv := div_le_self hD.le hsqrt
  have hp (a b : Fin 3 → ℚ)
      (ha : ∀ i, |(a i : ℝ)| ≤ D/Real.sqrt 3) (hb : ∀ i, |(b i : ℝ)| ≤ D/Real.sqrt 3) :
      ∀ i, |(a i : ℝ)*(b i : ℝ)| ≤ P := by
    intro i; rw [abs_mul]
    have hh := mul_le_mul ((ha i).trans hdiv) ((hb i).trans hdiv) (abs_nonneg _) hD.le
    dsimp [P]; nlinarith
  obtain ⟨a, ha, haErr⟩ := dot3_finite_weighted fmt.interchange hE hE hP (hp e e heC heC) hηP (by linarith) hPmax
  obtain ⟨b, hb, hbErr⟩ := dot3_finite_weighted fmt.interchange hE hF hP (hp e f heC hfC) hηP (by linarith) hPmax
  obtain ⟨d, hd, hdErr⟩ := dot3_finite_weighted fmt.interchange hE hR hP (hp e r heC hrC) hηP (by linarith) hPmax
  change |(a : ℝ)-scalarDot e e| ≤ _ at haErr
  change |(b : ℝ)-scalarDot e f| ≤ _ at hbErr
  change |(d : ℝ)-scalarDot e r| ≤ _ at hdErr
  rw [scalarDot_self] at haErr
  rw [scalarDot_inner] at hbErr hdErr
  have hcoef0 : 0 ≤ fmt.interchange.format.unitRoundoff*(1+fmt.interchange.format.unitRoundoff)^2 := by positivity
  have haSharp : |(a : ℝ)-‖realVec e‖^2| ≤ (2042/1000)*fmt.interchange.format.unitRoundoff*(‖realVec e‖*D)*(1+fmt.interchange.format.unitRoundoff)^2+2*fmt.interchange.format.minSubnormal := by
    have hh := mul_le_mul_of_nonneg_left (weighted_self_scaled (a := realVec e) hD heC) hcoef0
    simp only [realVec, WithLp.ofLp_toLp, ← sq, abs_sq] at hh haErr ⊢
    nlinarith only [hh, haErr]
  have sharp (w : Fin 3 → ℚ) (z : ℚ)
      (hw : ∀ i, |(w i : ℝ)| ≤ D/Real.sqrt 3)
      (hz : |(z : ℝ)-inner ℝ (realVec e) (realVec w)| ≤ fmt.interchange.format.unitRoundoff*(1+fmt.interchange.format.unitRoundoff)^2*
        (3*|(e 0 : ℝ)*(w 0 : ℝ)|+2*|(e 1 : ℝ)*(w 1 : ℝ)|+|(e 2 : ℝ)*(w 2 : ℝ)|)+2*fmt.interchange.format.minSubnormal) :
      |(z : ℝ)-inner ℝ (realVec e) (realVec w)| ≤ (2161/1000)*fmt.interchange.format.unitRoundoff*(‖realVec e‖*D)*(1+fmt.interchange.format.unitRoundoff)^2+2*fmt.interchange.format.minSubnormal := by
    have hh := mul_le_mul_of_nonneg_left (weighted_general_scaled (a := realVec e) (b := realVec w) hD.le hw) hcoef0
    dsimp [realVec] at hh hz ⊢
    nlinarith only [hh, hz]
  have hbSharp := sharp f b hfC hbErr
  have hdSharp := sharp r d hrC hdErr
  have general (w : Fin 3 → ℚ) (z : ℚ)
      (hz : |(z : ℝ)-inner ℝ (realVec e) (realVec w)| ≤ fmt.interchange.format.unitRoundoff*(1+fmt.interchange.format.unitRoundoff)^2*
        (3*|(e 0 : ℝ)*(w 0 : ℝ)|+2*|(e 1 : ℝ)*(w 1 : ℝ)|+|(e 2 : ℝ)*(w 2 : ℝ)|)+2*fmt.interchange.format.minSubnormal) :
      |(z : ℝ)-inner ℝ (realVec e) (realVec w)| ≤ 3*fmt.interchange.format.unitRoundoff*(1+fmt.interchange.format.unitRoundoff)^2*‖realVec e‖*‖realVec w‖+2*fmt.interchange.format.minSubnormal := by
    have hh := mul_le_mul_of_nonneg_left (weighted_products_le_norm (realVec e) (realVec w)) hcoef0
    dsimp [realVec] at hh hz ⊢
    nlinarith only [hh, hz]
  have haGeneral := general e a (by simpa only [real_inner_self_eq_norm_sq] using haErr)
  rw [real_inner_self_eq_norm_sq] at haGeneral
  have haGeneral' : |(a : ℝ)-‖realVec e‖^2| ≤ 3*fmt.interchange.format.unitRoundoff*(1+fmt.interchange.format.unitRoundoff)^2*‖realVec e‖^2+2*fmt.interchange.format.minSubnormal := by
    nlinarith only [haGeneral]
  obtain ⟨_, _, hhmax⟩ := FaceRanges.root_bounds fmt
  have hetaA : fmt.interchange.format.minSubnormal ≤ ‖realVec e‖^2/8 := by
    rw [hη]
    exact FaceRanges.eta_small (fourthRoot_nonneg _) hhmax (fourthRoot_pow_four fmt.subnormal_nonneg).symm hA
  obtain ⟨haHalf, haLo, _⟩ := FaceRanges.self_dot_half hρ0 hρmax hetaA haGeneral'
  have haPos : 0 < (a : ℝ) := by
    have hh : 0 < ‖realVec e‖ := lt_of_le_of_lt (fourthRoot_nonneg _) hA
    nlinarith
  have magnitude (w : Fin 3 → ℚ) (z : ℚ) (hwD : ‖realVec w‖ ≤ D)
      (hz : |(z : ℝ)-inner ℝ (realVec e) (realVec w)| ≤ 3*fmt.interchange.format.unitRoundoff*(1+fmt.interchange.format.unitRoundoff)^2*‖realVec e‖*‖realVec w‖+2*fmt.interchange.format.minSubnormal) :
      |(z : ℝ)| ≤ 2*D^2+2*fmt.interchange.format.minSubnormal := by
    have hprod := mul_le_mul heD hwD (norm_nonneg _) hD.le
    have hi := (abs_real_inner_le_norm (realVec e) (realVec w)).trans hprod
    have hcoef := mul_le_mul_of_nonneg_right (FaceRanges.dot_coefficient hρ0 hρmax)
      (mul_nonneg (norm_nonneg (realVec e)) (norm_nonneg (realVec w)))
    have hh := abs_add_le ((z : ℝ)-inner ℝ (realVec e) (realVec w)) (inner ℝ (realVec e) (realVec w))
    rw [sub_add_cancel] at hh
    nlinarith
  exact ⟨a, b, d, ha, hb, hd, by exact_mod_cast haPos, haHalf.trans (by nlinarith [sq_nonneg ‖realVec e‖]),
    haSharp, hbSharp, hdSharp, magnitude f b hfD (general f b hbErr), magnitude r d hrD (general r d hdErr)⟩

end DistanceAccuracy.ProjectionRounding

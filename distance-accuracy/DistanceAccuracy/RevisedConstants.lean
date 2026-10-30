import DistanceAccuracy.Claim4

/-! Constants for the elementary compensated-determinant estimate and the
looser reconstruction lower bound. These assembly lemmas are conditional on
branch estimates; they do not assert those estimates for IEEEAlgorithm. -/
namespace DistanceAccuracy

lemma revised_crossing_coefficient : F (V 8.4 + 5.02) + 3.53 < 35.9 := by
  have h1 : J 3.60 8.4 ≤ 17.504 := by
    have h : hypot (8.4 + 3.60) 7.02 ≤ 13.904 :=
      hypot_le (by norm_num) (by norm_num)
    dsimp [J]; linarith
  have h2 : V 8.4 ≤ 18.935 :=
    hypot_le_of_le (J_nonneg (by norm_num)) h1 (by norm_num) (by norm_num)
  have h3 : J 3.17 (V 8.4 + 5.02) ≤ 31.189 := by
    have h : hypot (V 8.4 + 5.02 + 3.17) 7.02 ≤ 28.019 :=
      hypot_le_of_le (by have := V_nonneg (8.4 : ℝ); linarith)
        (show V 8.4 + 5.02 + 3.17 ≤ 27.125 by linarith)
        (by norm_num) (by norm_num)
    dsimp [J]; linarith
  have h4 : F (V 8.4 + 5.02) ≤ 32.3 :=
    hypot_le_of_le (J_nonneg (by norm_num)) h3 (by norm_num) (by norm_num)
  linarith

lemma revised_thin_coefficient : F (3.02 + 16 + 4.02) + 3.53 < 35.9 := by
  have h1 : J 3.17 (3.02 + 16 + 4.02) ≤ 30.304 := by
    have h : hypot (3.02 + 16 + 4.02 + 3.17) 7.02 ≤ 27.134 :=
      hypot_le (by norm_num) (by norm_num)
    dsimp [J]; linarith
  have h2 : F (3.02 + 16 + 4.02) ≤ 31.444 :=
    hypot_le_of_le (J_nonneg (by norm_num)) h1 (by norm_num) (by norm_num)
  linarith

lemma revised_exact_root_coefficient : (35.9 : ℝ) * (2 * Real.sqrt 3) < 128 := by
  have := sqrt_three_le; linarith

lemma revised_rounded_root_coefficient : (36.91 : ℝ) * (2 * Real.sqrt 3) < 128 := by
  have := sqrt_three_le; linarith

/-- Assembly using the elementary determinant route and the separately proved
120rhoL reconstruction budget. The two inequalities remain branch obligations. -/
theorem revised_claim4_of_bounds {rho L H h d computed : ℝ}
    (hrho : 0 ≤ rho) (hL : 0 ≤ L) (hH : 0 ≤ H) (hbudget : 8*h ≤ H)
    (hlower : d-computed ≤ 120*rho*L)
    (hupper : computed-d ≤ 35.9*rho*(2*Real.sqrt 3*L)+8*h) :
    |computed-d| ≤ 64*(2*rho)*L+H := by
  have hc := mul_le_mul_of_nonneg_right (le_of_lt revised_exact_root_coefficient)
    (mul_nonneg hrho hL)
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hrho hL]
  · nlinarith

end DistanceAccuracy

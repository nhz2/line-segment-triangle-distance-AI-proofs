import DistanceAccuracy.Bounds

/-!
# Exact checks of constants

All decimals are exact rational real numbers. These proofs use kernel-checked
arithmetic and inequalities; they do not evaluate an IEEE square root or rely
on the Python checker.
-/
namespace DistanceAccuracy

lemma hypot_le_of_le {a b A C : ℝ} (ha : 0 ≤ a) (hA : a ≤ A)
    (hC : 0 ≤ C) (hs : A ^ 2 + b ^ 2 ≤ C ^ 2) : hypot a b ≤ C :=
  (hypot_mono ha hA).trans (hypot_le hC hs)

lemma crossing_coefficient : F (V 8.34 + 5.02) + 3.53 < 35.8 := by
  have h1 : J 3.60 8.34 ≤ 17.45078 := by
    have h : hypot (8.34 + 3.60) 7.02 ≤ 13.85078 :=
      hypot_le (by norm_num) (by norm_num)
    dsimp [J]; linarith
  have h2 : V 8.34 ≤ 18.88540 :=
    hypot_le_of_le (J_nonneg (by norm_num)) h1 (by norm_num) (by norm_num)
  have h3 : J 3.17 (V 8.34 + 5.02) ≤ 31.14066 := by
    have h : hypot (V 8.34 + 5.02 + 3.17) 7.02 ≤ 27.97066 :=
      hypot_le_of_le (by have := V_nonneg (8.34 : ℝ); linarith)
        (show V 8.34 + 5.02 + 3.17 ≤ 27.07540 by linarith)
        (by norm_num) (by norm_num)
    dsimp [J]; linarith
  have h4 : F (V 8.34 + 5.02) ≤ 32.24849 :=
    hypot_le_of_le (J_nonneg (by norm_num)) h3 (by norm_num) (by norm_num)
  linarith

lemma direct_crossing_coefficient : V 8.34 + 4.03 < 35.8 := by
  have h1 : J 3.60 8.34 ≤ 17.45078 := by
    have h : hypot (8.34 + 3.60) 7.02 ≤ 13.85078 :=
      hypot_le (by norm_num) (by norm_num)
    dsimp [J]; linarith
  have h2 : V 8.34 ≤ 18.88540 :=
    hypot_le_of_le (J_nonneg (by norm_num)) h1 (by norm_num) (by norm_num)
  linarith

lemma line_coefficient : F 3.02 + 3.53 < 19 := by
  have h1 : J 3.17 3.02 ≤ 12.53 := by
    have h : hypot (3.02 + 3.17) 7.02 ≤ 9.36 :=
      hypot_le (by norm_num) (by norm_num)
    dsimp [J]; linarith
  have h2 : F 3.02 ≤ 15.08 :=
    hypot_le_of_le (J_nonneg (by norm_num)) h1 (by norm_num) (by norm_num)
  linarith

lemma point_coefficient : P 0 < 24.47 := by
  have h1 : J 3.60 (0 + 2.02) ≤ 12.60 := by
    have h : hypot (0 + 2.02 + 3.60) 7.02 ≤ 9.00 :=
      hypot_le (by norm_num) (by norm_num)
    dsimp [J]; linarith
  have h2 : V (0 + 2.02) ≤ 14.53 :=
    hypot_le_of_le (J_nonneg (by norm_num)) h1 (by norm_num) (by norm_num)
  have h3 : hypot (V (0 + 2.02) + 4.02) 8.38 ≤ 20.36 :=
    hypot_le_of_le (by have := V_nonneg (0 + 2.02 : ℝ); linarith)
      (show V (0 + 2.02) + 4.02 ≤ 18.55 by linarith)
      (by norm_num) (by norm_num)
  exact max_lt (by linarith) (by linarith)

lemma separated_coefficient : 8.04 + max (P 0) (F 3.02 + 3.53) < 32.52 := by
  have hp := point_coefficient
  have hl := line_coefficient
  have hm : max (P 0) (F 3.02 + 3.53) < 24.48 := max_lt (by linarith) (by linarith)
  linarith

lemma sqrt_three_le : Real.sqrt 3 ≤ (1.733 : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  norm_num

lemma exact_root_coefficient : (35.8 : ℝ) * (2 * Real.sqrt 3) < 128 := by
  have := sqrt_three_le
  linarith

lemma rounded_root_coefficient : (36.81 : ℝ) * (2 * Real.sqrt 3) < 128 := by
  have := sqrt_three_le
  linarith

/-- The Float32 remainder bound; the Float64 bound is smaller. -/
lemma remainder_coefficient :
    (1 / 256 : ℝ) + 10 / 2176 + 1 / 2 ^ 43 < 1 / 100 := by norm_num

/-- Conservative exact radical bounds for the weighted-dot constants. -/
lemma kappa_bound : Real.sqrt (14 / 3 : ℝ) ≤ 2.161 := by
  apply Real.sqrt_le_iff.mpr; norm_num
lemma lambda_bound : Real.sqrt (25 / 6 : ℝ) ≤ 2.042 := by
  apply Real.sqrt_le_iff.mpr; norm_num
lemma inv_sqrt_three_bound : Real.sqrt (1 / 3 : ℝ) ≤ 0.578 := by
  apply Real.sqrt_le_iff.mpr; norm_num

lemma local_coefficients :
    Real.sqrt (14 / 3 : ℝ) + Real.sqrt (25 / 6 : ℝ) + 1 + 0.01 < 5.22 ∧
    2 * Real.sqrt (14 / 3 : ℝ) + Real.sqrt (25 / 6 : ℝ) + 2 + 0.01 < 8.38 ∧
    Real.sqrt (14 / 3 : ℝ) + Real.sqrt (25 / 6 : ℝ) + 3 + 0.01 < 7.22 ∧
    2 + 2 * Real.sqrt (1 / 3 : ℝ) + 0.01 < 3.17 ∧
    3 + Real.sqrt (1 / 3 : ℝ) + 0.01 < 3.60 ∧
    2 * Real.sqrt (14 / 3 : ℝ) + 4 + 0.01 < 8.34 := by
  have := kappa_bound
  have := lambda_bound
  have := inv_sqrt_three_bound
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor <;> linarith

/-- η = 2ρ·floatmin, so h⁴ = 2ρ H⁴. This proves the shared underflow
budget without using a floating-point fourth root. -/
lemma underflow_budget {rho h H : ℝ} (hrho : rho ≤ 1 / 2 ^ 24)
    (hh : 0 ≤ h) (hH : 0 ≤ H) (hfourth : h ^ 4 = 2 * rho * H ^ 4) :
    32 * h ≤ H := by
  have hc : (32 : ℝ) ^ 4 * 2 * rho ≤ 1 := by norm_num at hrho ⊢; linarith
  have hm := mul_le_mul_of_nonneg_right hc (pow_nonneg hH 4)
  have hp : (32 * h) ^ 4 ≤ H ^ 4 := by
    rw [mul_pow, hfourth]
    nlinarith only [hm]
  exact (pow_le_pow_iff_left₀ (by positivity) hH (by decide : (4 : ℕ) ≠ 0)).1 hp

end DistanceAccuracy

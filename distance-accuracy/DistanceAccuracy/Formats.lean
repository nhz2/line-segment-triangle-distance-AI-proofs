import DistanceAccuracy.Constants

/-! Exact format parameters. These are not an operational IEEE-754 semantics. -/
set_option exponentiation.threshold 2048

namespace DistanceAccuracy

inductive Format where
  | binary32 | binary64
  deriving DecidableEq

noncomputable def Format.rho : Format → ℝ
  | .binary32 => 1 / 2 ^ 24
  | .binary64 => 1 / 2 ^ 53

noncomputable def Format.leastNormal : Format → ℝ
  | .binary32 => 1 / 2 ^ 126
  | .binary64 => 1 / 2 ^ 1022

noncomputable def Format.leastSubnormal : Format → ℝ
  | .binary32 => 1 / 2 ^ 149
  | .binary64 => 1 / 2 ^ 1074

lemma Format.rho_nonneg (f : Format) : 0 ≤ f.rho := by cases f <;> norm_num [Format.rho]
lemma Format.rho_le (f : Format) : f.rho ≤ 1 / 2 ^ 24 := by
  cases f <;> norm_num [Format.rho]
lemma Format.normal_nonneg (f : Format) : 0 ≤ f.leastNormal := by
  cases f <;> norm_num [Format.leastNormal]
lemma Format.subnormal_nonneg (f : Format) : 0 ≤ f.leastSubnormal := by
  cases f <;> norm_num [Format.leastSubnormal]
lemma Format.subnormal_identity (f : Format) : f.leastSubnormal = 2 * f.rho * f.leastNormal := by
  cases f with
  | binary32 => norm_num [Format.rho, Format.leastNormal, Format.leastSubnormal]
  | binary64 =>
    change (1 / (2 : ℝ) ^ 1074) = 2 * (1 / (2 : ℝ) ^ 53) * (1 / (2 : ℝ) ^ 1022)
    rw [show (1074 : ℕ) = 52 + 1022 by decide, pow_add]
    simp only [one_div, mul_inv_rev]
    norm_num

noncomputable def fourthRoot (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)
lemma fourthRoot_nonneg (x : ℝ) : 0 ≤ fourthRoot x := Real.sqrt_nonneg _
lemma fourthRoot_pow_four {x : ℝ} (hx : 0 ≤ x) : fourthRoot x ^ 4 = x := by
  have h1 : fourthRoot x ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h2 := Real.sq_sqrt hx
  calc
    fourthRoot x ^ 4 = (fourthRoot x ^ 2) ^ 2 := by ring
    _ = x := by rw [h1, h2]

lemma Format.fourth_root_relation (f : Format) :
    fourthRoot f.leastSubnormal ^ 4 = 2 * f.rho * fourthRoot f.leastNormal ^ 4 := by
  rw [fourthRoot_pow_four f.normal_nonneg, fourthRoot_pow_four f.subnormal_nonneg]
  exact f.subnormal_identity

lemma Format.underflow_budget (f : Format) :
    32 * fourthRoot f.leastSubnormal ≤ fourthRoot f.leastNormal :=
  DistanceAccuracy.underflow_budget f.rho_le (fourthRoot_nonneg _) (fourthRoot_nonneg _)
    f.fourth_root_relation

end DistanceAccuracy

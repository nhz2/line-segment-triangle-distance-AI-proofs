import DistanceAccuracy.Formats

namespace DistanceAccuracy
set_option exponentiation.threshold 2048

noncomputable def Format.rootLower : Format → ℝ
  | .binary32 => 1 / 2 ^ 32
  | .binary64 => 1 / 2 ^ 256

lemma Format.rootLower_nonneg (f : Format) : 0 ≤ f.rootLower := by
  cases f <;> norm_num [Format.rootLower]

lemma Format.rootLower_le (f : Format) : f.rootLower ≤ fourthRoot f.leastNormal := by
  apply (pow_le_pow_iff_left₀ f.rootLower_nonneg (fourthRoot_nonneg _) (show (4:ℕ) ≠ 0 by decide)).mp
  rw [fourthRoot_pow_four f.normal_nonneg]
  cases f <;> norm_num [Format.rootLower, Format.leastNormal]

lemma Format.large_subnormal_budget (f : Format) {L : ℝ}
    (hL : fourthRoot f.leastNormal / 64 ≤ L) :
    f.leastSubnormal ≤ f.rho ^ 2 * L := by
  have hbase : f.leastSubnormal ≤ f.rho ^ 2 * (f.rootLower / 64) := by
    cases f <;> norm_num [Format.leastSubnormal, Format.rho, Format.rootLower]
  have hlo : f.rootLower / 64 ≤ L := (div_le_div_of_nonneg_right f.rootLower_le (by norm_num)).trans hL
  exact hbase.trans (mul_le_mul_of_nonneg_left hlo (sq_nonneg _))

lemma Format.large_sqrt_subnormal_budget (f : Format) {L : ℝ}
    (hL : fourthRoot f.leastNormal / 64 ≤ L) :
    2 * Real.sqrt f.leastSubnormal ≤ f.rho * L := by
  have hb : Real.sqrt f.leastSubnormal ≤ f.rho * (f.rootLower / 64) / 2 := by
    rw [Real.sqrt_le_iff]
    cases f <;> norm_num [Format.leastSubnormal, Format.rho, Format.rootLower]
  have hlo : f.rootLower / 64 ≤ L := (div_le_div_of_nonneg_right f.rootLower_le (by norm_num)).trans hL
  have hm := mul_le_mul_of_nonneg_left hlo f.rho_nonneg
  linarith

noncomputable def Format.subnormalFourthLower : Format → ℝ
  | .binary32 => 1 / 2 ^ 38
  | .binary64 => 1 / 2 ^ 269

lemma Format.subnormalFourthLower_nonneg (f : Format) : 0 ≤ f.subnormalFourthLower := by
  cases f <;> norm_num [Format.subnormalFourthLower]

lemma Format.subnormalFourthLower_le (f : Format) :
    f.subnormalFourthLower ≤ fourthRoot f.leastSubnormal := by
  apply (pow_le_pow_iff_left₀ f.subnormalFourthLower_nonneg (fourthRoot_nonneg _)
    (by decide : (4:ℕ) ≠ 0)).mp
  rw [fourthRoot_pow_four f.subnormal_nonneg]
  cases f <;> norm_num [Format.subnormalFourthLower, Format.leastSubnormal]

lemma Format.large_eta_absorption (f : Format) {L : ℝ}
    (hL : fourthRoot f.leastNormal/64 ≤ L) :
    f.leastSubnormal ≤ f.rho*fourthRoot f.leastSubnormal*L/1000 := by
  have hlo : f.rootLower/64 ≤ L := (div_le_div_of_nonneg_right f.rootLower_le (by norm_num)).trans hL
  have hr0 := f.rootLower_nonneg
  have hl0 : 0 ≤ f.rootLower/64 := by positivity
  have hprod := mul_le_mul f.subnormalFourthLower_le hlo hl0 (fourthRoot_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hprod f.rho_nonneg
  have hnum : 1000*f.leastSubnormal ≤ f.rho*(f.subnormalFourthLower*(f.rootLower/64)) := by
    cases f <;> norm_num [Format.rho, Format.rootLower, Format.subnormalFourthLower, Format.leastSubnormal]
  nlinarith

lemma Format.sqrt_eta_absorption (f : Format) :
    1000000*Real.sqrt f.leastSubnormal ≤ f.rho := by
  have h : Real.sqrt f.leastSubnormal ≤ f.rho/1000000 := by
    apply Real.sqrt_le_iff.mpr
    cases f <;> norm_num [Format.rho, Format.leastSubnormal]
  linarith

end DistanceAccuracy

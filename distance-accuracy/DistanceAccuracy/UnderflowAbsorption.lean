import DistanceAccuracy.FormatBudgets

namespace DistanceAccuracy
set_option exponentiation.threshold 2048

lemma Format.subnormal_root_small (f : Format) : fourthRoot f.leastSubnormal ≤ (1/100:ℝ) := by
  apply (pow_le_pow_iff_left₀ (fourthRoot_nonneg _) (by norm_num : (0:ℝ) ≤ 1/100)
    (by decide : (4:ℕ) ≠ 0)).mp
  rw [fourthRoot_pow_four f.subnormal_nonneg]
  cases f <;> norm_num [Format.leastSubnormal]

/-- A shared budget for a second solve, two affine roundings and the stored
squared norm. The reduced solve's division by A carries its own 4h term. -/
lemma Format.kernel_absolute_budget (f : Format) {D : ℝ} (hD : 0 ≤ D) :
    8*Real.sqrt f.leastSubnormal*(1+D)+3*f.leastSubnormal+Real.sqrt (2*f.leastSubnormal) ≤
      fourthRoot f.leastSubnormal+(1/1000)*f.rho*D := by
  let h := fourthRoot f.leastSubnormal
  have hh0 : 0 ≤ h := fourthRoot_nonneg _
  have hh1 : h ≤ (1/100:ℝ) := f.subnormal_root_small
  have hh2 : h^2 = Real.sqrt f.leastSubnormal := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hh4 : h^4 = f.leastSubnormal := fourthRoot_pow_four f.subnormal_nonneg
  have hsq1 : h^2 ≤ 1 := by nlinarith
  have heta : f.leastSubnormal ≤ Real.sqrt f.leastSubnormal := by
    have hp := mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hsq1)
    nlinarith
  have hconst : 12*Real.sqrt f.leastSubnormal+4*f.leastSubnormal ≤ h := by
    have hp := mul_nonneg hh0 (show 0 ≤ 1-16*h by linarith)
    nlinarith
  have hroot : Real.sqrt (2*f.leastSubnormal) ≤ 2*Real.sqrt f.leastSubnormal := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hs := Real.sq_sqrt f.subnormal_nonneg
      nlinarith [f.subnormal_nonneg]
  have hscaled := mul_le_mul_of_nonneg_right f.sqrt_eta_absorption hD
  have hscaled0 := mul_nonneg (Real.sqrt_nonneg f.leastSubnormal) hD
  change _ ≤ h+(1/1000)*f.rho*D
  nlinarith [f.subnormal_nonneg,Real.sqrt_nonneg f.leastSubnormal]

end DistanceAccuracy

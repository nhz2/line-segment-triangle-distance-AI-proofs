import DistanceAccuracy.LowerBound

/-! A sharper one-sided squared-norm evaluation budget. -/
namespace DistanceAccuracy.NormUpper

/-- The multiply/FMA/FMA norm schedule incurs at most 1.51ρr+sqrt(2η)
    upward error. Unlike the lower estimate this needs no sign premise on q. -/
theorem norm_upper {rho eta r q : ℝ}
    (hrho : 0 ≤ rho) (hrhomax : rho ≤ 1/1024) (heta : 0 ≤ eta) (hr : 0 ≤ r)
    (hq : q-r^2 ≤ 3*rho*(1+rho)^2*r^2+2*eta) :
    Real.sqrt q-r ≤ (151/100)*rho*r+Real.sqrt (2*eta) := by
  have hs := (sq_le_sq₀ hrho (by norm_num : (0:ℝ) ≤ 1/1024)).2 hrhomax
  have hp := mul_nonneg hrho (show 0 ≤ 1/50-(6-(151/100:ℝ)^2)*rho-3*rho^2 by nlinarith)
  have hc : 1+3*rho*(1+rho)^2 ≤ (1+(151/100)*rho)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg r)
  have he := Real.sq_sqrt (show 0 ≤ 2*eta by positivity)
  have hu : Real.sqrt q ≤ (1+(151/100)*rho)*r+Real.sqrt (2*eta) := by
    apply LowerBound.sqrt_upper (by positivity) (Real.sqrt_nonneg _)
    nlinarith
  nlinarith

end DistanceAccuracy.NormUpper

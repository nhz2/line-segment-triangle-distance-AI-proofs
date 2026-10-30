import DistanceAccuracy.EvaluateLower
import DistanceAccuracy.UpperSelection
import DistanceAccuracy.RevisedConstants

namespace DistanceAccuracy.AccuracyAssembly
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds
open UpperSelection

/-- Final scalar budget for the common diameter D=3.5L. -/
lemma budget {rho L h H computed d : ℝ}
    (hr : 0 ≤ rho) (hL : 0 ≤ L) (hh : 0 ≤ h) (hH : 32*h ≤ H)
    (hlo : d-computed ≤ 120*rho*L)
    (hhi : computed ≤ d+36.4*rho*((7/2)*L)+32*h) :
    |computed-d| ≤ 64*(2*rho)*L+H := by
  have hm := mul_nonneg hr hL
  apply abs_le.mpr
  constructor <;> nlinarith only [hlo,hhi,hm,hh,hH]

/-- Combine a large-coordinate upper theorem with the independently proved
all-pairings lower and small-coordinate theorems. -/
theorem of_upper (fmt : DistanceAccuracy.Format)
    (x y : Simplex fmt.interchange) (L : ℝ)
    (hadm : Geometry.admissible fmt.interchange x y L)
    (hupper : fourthRoot fmt.leastNormal/64 ≤ L →
      Upper fmt.interchange (Geometry.distance fmt.interchange x y+
        36.4*fmt.rho*((7/2)*L)+32*fourthRoot fmt.leastSubnormal)
        (evaluate fmt.interchange x y).q) :
    ∃ q : ℝ, fmt.interchange.decode? (evaluate fmt.interchange x y).q = some q ∧
      |Real.sqrt q-Geometry.distance fmt.interchange x y| ≤
        64*(2*fmt.interchange.format.unitRoundoff)*L+fourthRoot fmt.interchange.format.minNormal := by
  have hrho : fmt.interchange.format.unitRoundoff = fmt.rho := by
    cases fmt with
    | binary32 => exact fp32_parameters.1
    | binary64 => exact fp64_parameters.1
  have hn : fmt.interchange.format.minNormal = fmt.leastNormal := by
    cases fmt with
    | binary32 => exact fp32_parameters.2.1
    | binary64 => exact fp64_parameters.2.1
  by_cases hlarge : fourthRoot fmt.leastNormal/64 ≤ L
  · obtain ⟨q,hq,hb⟩ := hupper hlarge
    obtain ⟨v,hv,_,hlo⟩ := EvaluateLower.large_lower fmt x y L hadm hlarge
    have hqr := real_decode fmt.interchange hq
    have heq : v = (q:ℝ) := Option.some.inj (hv.symm.trans hqr)
    subst v
    refine ⟨q,hqr,?_⟩
    rw [hrho,hn]
    rw [hrho] at hlo
    exact budget fmt.rho_nonneg hadm.1 (fourthRoot_nonneg _) fmt.underflow_budget hlo hb
  · obtain ⟨q,hq,_,hb⟩ := EvaluateLower.small_accuracy fmt x y L hadm (le_of_not_ge hlarge)
    refine ⟨q,hq,?_⟩
    rw [hn]
    have hm := mul_nonneg fmt.interchange.format.unitRoundoff_pos.le hadm.1
    nlinarith only [hb,hm]

end DistanceAccuracy.AccuracyAssembly

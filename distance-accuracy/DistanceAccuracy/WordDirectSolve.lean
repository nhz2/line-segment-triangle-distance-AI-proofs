import DistanceAccuracy.WordSecondSolve

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant

/-- A direct dot quotient has the same conservative 8.38 local loss budget.
No extra multiplication or FMA is postulated: its numerator is the actual word
negation, and the quotient may overflow before clamping. -/
theorem direct_word_projection_loss (I : Interchange) [I.Valid]
    {aw dw : I.Word} {a d s : ℚ} {E R : E3} {D sstar : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hd : value? I dw = some d)
    (hs : value? I (clamp01nan I (IEEEAlgorithm.div I (neg I dw) aw)) = some s)
    (hap : 0 < a) (hE : E ≠ 0) (hD : 0 ≤ D) (hED : ‖E‖ ≤ D) (hRD : ‖R‖ ≤ D)
    (hs0 : (0 : ℝ) ≤ (s : ℝ)) (hs1 : (s : ℝ) ≤ 1)
    (hstar0 : 0 ≤ sstar) (hstar1 : sstar ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1 / 16777216)
    (hlim1 : (1 : ℝ) < I.format.overflowThreshold)
    (hAerr : |(a : ℝ) - ‖E‖ ^ 2| ≤ ‖E‖ ^ 2)
    (hA : |(a : ℝ) - ‖E‖ ^ 2| ≤ (2042 / 1000) * I.format.unitRoundoff * (‖E‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal)
    (hDdot : |(d : ℝ) - inner ℝ E R| ≤ (2161 / 1000) * I.format.unitRoundoff * (‖E‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal) :
    ‖R + (s : ℝ) • E‖ ^ 2 ≤ ‖R + sstar • E‖ ^ 2 +
      ((419 / 50) * I.format.unitRoundoff * D) ^ 2 + 64 * I.format.minSubnormal * (1 + ‖E‖ ^ 2) := by
  obtain ⟨deltaQ, zetaQ, hdQ, hzQ, hKKT⟩ := positive_clamped_optimal I hone ha (neg_value I hd) hap
    (by linarith only [hrho]) hlim1 hs hstar0 hstar1
  have hr := I.format.unitRoundoff_pos.le
  have heta : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hresult := second_squared_loss (P := -E) (Q := (0 : E3)) (R := R) (t := (0 : ℝ))
    (ah := (a : ℝ)) (bh := (0 : ℝ)) (dh := -(d : ℝ)) (num := -(d : ℝ)) (delta := 0) (zeta := 0)
    (neg_ne_zero.mpr hE) hD (by simpa using hED) (by simpa using hRD)
    hr hrho heta (by exact_mod_cast hap.le) (by simpa using hAerr) (by simpa using hA)
    (by simp only [inner_zero_right, sub_zero, abs_zero, norm_neg]; positivity)
    (by simpa only [inner_neg_left, norm_neg, neg_sub_neg, abs_sub_comm] using hDdot)
    (by simpa using hr) (by simp only [abs_zero]; positivity) hdQ hzQ (by ring)
    hs0 hs1 (by norm_num) (by norm_num) hstar0 hstar1
    (by simpa only [Rat.cast_neg] using hKKT)
  simpa using hresult

end DistanceAccuracy.ProjectionRounding

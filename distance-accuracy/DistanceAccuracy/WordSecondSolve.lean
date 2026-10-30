import DistanceAccuracy.SecondSolveCore
import DistanceAccuracy.TotalProjection
import DistanceAccuracy.WordProjectionRounding

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant OperationBounds

/-- Positive numerator division, including overflow to infinity, satisfies the
variational condition for projection along the negated direction. -/
theorem positive_clamped_optimal (I : Interchange) [I.Valid]
    {aw nw : I.Word} {a n s : ℚ} {sstar : ℝ}
    (hone : value? I (one I) = some 1) (ha : value? I aw = some a)
    (hn : value? I nw = some n) (hap : 0 < a)
    (hr : I.format.unitRoundoff < 1) (hlim : (1 : ℝ) < I.format.overflowThreshold)
    (hs : value? I (clamp01nan I (IEEEAlgorithm.div I nw aw)) = some s)
    (hsstar0 : 0 ≤ sstar) (hsstar1 : sstar ≤ 1) :
    ∃ delta zeta : ℝ, |delta| ≤ I.format.unitRoundoff ∧ |zeta| ≤ I.format.minSubnormal / 2 ∧
      0 ≤ (((a : ℝ) / (1 + delta)) * (s : ℝ) +
        (-(n : ℝ) - ((a : ℝ) / (1 + delta)) * zeta)) * (sstar - (s : ℝ)) := by
  obtain ⟨delta, zeta, hd, hz, hform⟩ := clamped_division_representation I hone hn ha (ne_of_gt hap) hlim hs
  have hdl := (abs_le.mp hd).1
  have hdelta : 0 < 1 + delta := by linarith only [hdl, hr]
  have har : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hap
  refine ⟨delta, zeta, hd, hz, ?_⟩
  rw [hform]
  apply quotient_effective_optimal (bh := -(n : ℝ)) har hdelta _ (by norm_num) hsstar0 hsstar1
  simp

/-- The actual FMA numerator and actual divided/clamped second parameter
satisfy the tight 8.38 squared-loss bound. Only the previously derived dot
mixed bounds and explicit range of the exact FMA input are needed. -/
theorem second_word_projection_loss (I : Interchange) [I.Valid]
    {aw bw dw tw : I.Word} {a b d t s : ℚ} {P Q R : E3} {D sstar : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hd : value? I dw = some d) (ht : value? I tw = some t)
    (hs : value? I (clamp01nan I (IEEEAlgorithm.div I (fma I tw bw dw) aw)) = some s)
    (hap : 0 < a) (hP : P ≠ 0) (hD : 0 ≤ D) (hPD : ‖P‖ ≤ D)
    (hkD : ‖R + (t : ℝ) • Q‖ ≤ D)
    (ht0 : (0 : ℝ) ≤ (t : ℝ)) (ht1 : (t : ℝ) ≤ 1)
    (hs0 : (0 : ℝ) ≤ (s : ℝ)) (hs1 : (s : ℝ) ≤ 1)
    (hstar0 : 0 ≤ sstar) (hstar1 : sstar ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1 / 16777216)
    (hlim1 : (1 : ℝ) < I.format.overflowThreshold)
    (hnumlim : |(t : ℝ) * (b : ℝ) + (d : ℝ)| < I.format.overflowThreshold)
    (hAerr : |(a : ℝ) - ‖P‖ ^ 2| ≤ ‖P‖ ^ 2)
    (hA : |(a : ℝ) - ‖P‖ ^ 2| ≤ (2042 / 1000) * I.format.unitRoundoff * (‖P‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal)
    (hB : |(b : ℝ) - inner ℝ P Q| ≤ (2161 / 1000) * I.format.unitRoundoff * (‖P‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal)
    (hDdot : |(d : ℝ) - inner ℝ P R| ≤ (2161 / 1000) * I.format.unitRoundoff * (‖P‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal) :
    ‖(R + (t : ℝ) • Q) + (s : ℝ) • (-P)‖ ^ 2 ≤ ‖(R + (t : ℝ) • Q) + sstar • (-P)‖ ^ 2 +
      ((419 / 50) * I.format.unitRoundoff * D) ^ 2 + 64 * I.format.minSubnormal * (1 + ‖P‖ ^ 2) := by
  obtain ⟨n, hn, _⟩ := fma_exists_error I ht hb hd
    (no_overflow_of_lt I _ (by simpa only [Rat.cast_add, Rat.cast_mul] using hnumlim))
  obtain ⟨delta, zeta, hnum, hdelta, hzeta⟩ := word_fma_decomposition I ht hb hd hn
  obtain ⟨deltaQ, zetaQ, hdQ, hzQ, hKKT⟩ := positive_clamped_optimal I hone ha hn hap
    (by linarith only [hrho]) hlim1 hs hstar0 hstar1
  exact second_squared_loss hP hD hPD hkD I.format.unitRoundoff_pos.le hrho
    (by unfold FP.IEEE.Format.minSubnormal; positivity) (by exact_mod_cast hap.le)
    hAerr hA hB hDdot hdelta hzeta hdQ hzQ hnum hs0 hs1 ht0 ht1 hstar0 hstar1 hKKT

end DistanceAccuracy.ProjectionRounding

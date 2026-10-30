import DistanceAccuracy.WordSecondSolve

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant OperationBounds

/-- Mixed factor decomposition for the actual endpoint numerator subtraction. -/
theorem word_subtraction_decomposition (I : Interchange) [I.Valid]
    {bw ew : I.Word} {b e n : ℚ}
    (hb : value? I bw = some b) (he : value? I ew = some e)
    (hn : value? I (IEEEAlgorithm.sub I bw ew) = some n) :
    ∃ delta zeta : ℝ, (n : ℝ) = ((b : ℝ) - (e : ℝ)) * (1 + delta) + zeta ∧
      |delta| ≤ I.format.unitRoundoff ∧ |zeta| ≤ I.format.minSubnormal / 2 := by
  have hround := Software.binary_even_roundFinite_of_decode I .sub bw ew b e n hb he hn
  simp only [Software.binaryExact, Rat.cast_sub] at hround
  have herr := I.format.roundFinite_mixed_error ((b : ℝ) - (e : ℝ))
  rw [← hround] at herr
  apply relative_absolute_decomposition I.format.unitRoundoff_pos.le _ herr
  unfold FP.IEEE.Format.minSubnormal
  positivity

/-- The actual endpoint quotient `(dot(P,Q)-dot(Q,R))/dot(Q,Q)` has the same
8.38 loss budget. Overflowing quotient results are covered. -/
theorem endpoint_word_projection_loss (I : Interchange) [I.Valid]
    {aw bw ew : I.Word} {a b e s : ℚ} {P Q R : E3} {D sstar : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b) (he : value? I ew = some e)
    (hs : value? I (clamp01nan I (IEEEAlgorithm.div I (sub I bw ew) aw)) = some s)
    (hap : 0 < a) (hQ : Q ≠ 0) (hD : 0 ≤ D) (hQD : ‖Q‖ ≤ D) (hkD : ‖R - P‖ ≤ D)
    (hs0 : (0 : ℝ) ≤ (s : ℝ)) (hs1 : (s : ℝ) ≤ 1)
    (hstar0 : 0 ≤ sstar) (hstar1 : sstar ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1 / 16777216)
    (hlim1 : (1 : ℝ) < I.format.overflowThreshold)
    (hnumlim : |(b : ℝ) - (e : ℝ)| < I.format.overflowThreshold)
    (hAerr : |(a : ℝ) - ‖Q‖ ^ 2| ≤ ‖Q‖ ^ 2)
    (hA : |(a : ℝ) - ‖Q‖ ^ 2| ≤ (2042 / 1000) * I.format.unitRoundoff * (‖Q‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal)
    (hB : |(b : ℝ) - inner ℝ P Q| ≤ (2161 / 1000) * I.format.unitRoundoff * (‖Q‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal)
    (hE : |(e : ℝ) - inner ℝ Q R| ≤ (2161 / 1000) * I.format.unitRoundoff * (‖Q‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal) :
    ‖(R - P) + (s : ℝ) • Q‖ ^ 2 ≤ ‖(R - P) + sstar • Q‖ ^ 2 +
      ((419 / 50) * I.format.unitRoundoff * D) ^ 2 + 64 * I.format.minSubnormal * (1 + ‖Q‖ ^ 2) := by
  obtain ⟨n, hn, _⟩ := binary_exists_error I .sub hb he
    (no_overflow_of_lt I _ (by simpa only [Software.binaryExact, Rat.cast_sub] using hnumlim))
  obtain ⟨delta, zeta, hnum, hd, hz⟩ := word_subtraction_decomposition I hb he hn
  obtain ⟨deltaQ, zetaQ, hdQ, hzQ, hKKT⟩ := positive_clamped_optimal I hone ha hn hap
    (by linarith only [hrho]) hlim1 hs hstar0 hstar1
  have hresult := second_squared_loss (P := -Q) (Q := -P) (R := R) (t := (1 : ℝ))
    (ah := (a : ℝ)) (bh := (b : ℝ)) (dh := -(e : ℝ))
    (neg_ne_zero.mpr hQ) hD (by simpa using hQD) (by simpa [sub_eq_add_neg] using hkD)
    I.format.unitRoundoff_pos.le hrho (by unfold FP.IEEE.Format.minSubnormal; positivity)
    (by exact_mod_cast hap.le) (by simpa using hAerr) (by simpa using hA)
    (by simpa [real_inner_comm] using hB)
    (by simpa only [inner_neg_left, norm_neg, neg_sub_neg, abs_sub_comm] using hE)
    hd hz hdQ hzQ (by simpa only [one_mul, sub_eq_add_neg] using hnum)
    hs0 hs1 (by norm_num) (by norm_num) hstar0 hstar1 hKKT
  simpa [sub_eq_add_neg] using hresult

end DistanceAccuracy.ProjectionRounding

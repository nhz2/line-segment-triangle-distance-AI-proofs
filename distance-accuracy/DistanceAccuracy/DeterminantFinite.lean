import DistanceAccuracy.Determinant
import DistanceAccuracy.OperationBounds

namespace DistanceAccuracy.Determinant
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds

lemma rounded_magnitude {x y rho eta P : ℝ}
    (hr : 0 ≤ rho) (hx : |x| ≤ P)
    (he : |y - x| ≤ rho * |x| + eta / 2) :
    |y| ≤ (1 + rho) * P + eta / 2 := by
  have ht : |y| ≤ |y - x| + |x| := by
    simpa using (abs_add_le (y - x) x)
  have hm := mul_le_mul_of_nonneg_left hx hr
  nlinarith

/-- A simple range envelope guarantees every compensated determinant
intermediate is finite. It is deliberately generous: ten times a bound on
either exact product must fit below the overflow threshold. -/
theorem det2_finite (I : Interchange) [I.Valid]
    {a b c d : I.Word} {ar br cr dr : ℚ} {P : ℝ}
    (ha : value? I a = some ar) (hb : value? I b = some br)
    (hc : value? I c = some cr) (hd : value? I d = some dr)
    (hP : 0 < P) (hab : |(ar : ℝ) * (br : ℝ)| ≤ P)
    (hcd : |(cr : ℝ) * (dr : ℝ)| ≤ P)
    (heta : I.format.minSubnormal ≤ P)
    (hrho : I.format.unitRoundoff ≤ 1 / 4)
    (hlim : 10 * P < I.format.overflowThreshold) :
    ∃ w e f out : ℚ,
      value? I (IEEEAlgorithm.mul I c d) = some w ∧
      value? I (IEEEAlgorithm.fma I (IEEEAlgorithm.neg I c) d
        (IEEEAlgorithm.mul I c d)) = some e ∧
      value? I (IEEEAlgorithm.fma I a b (IEEEAlgorithm.neg I
        (IEEEAlgorithm.mul I c d))) = some f ∧
      value? I (IEEEAlgorithm.det2 I a b c d) = some out := by
  have hr := I.format.unitRoundoff_pos
  have hproduct : |((cr * dr : ℚ) : ℝ)| < I.format.overflowThreshold := by
    rw [Rat.cast_mul]; linarith
  obtain ⟨w, hw, hwerr⟩ := binary_exists_error I .mul hc hd (no_overflow_of_lt I _ hproduct)
  change value? I (IEEEAlgorithm.mul I c d) = some w at hw
  simp only [Software.binaryExact, Rat.cast_mul] at hwerr
  have hwmag := rounded_magnitude (le_of_lt hr) hcd hwerr
  have hwp : |(w : ℝ)| ≤ 2 * P := by
    nlinarith [mul_nonneg hP.le (sub_nonneg.mpr hrho)]
  have hemag : |((-cr * dr + w : ℚ) : ℝ)| ≤ 3 * P := by
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_neg]
    have h := abs_add_le (-(cr : ℝ) * (dr : ℝ)) (w : ℝ)
    simp only [neg_mul, abs_neg] at h ⊢
    linarith
  have hfmag : |((ar * br + -w : ℚ) : ℝ)| ≤ 3 * P := by
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_neg]
    have h := abs_add_le ((ar : ℝ) * (br : ℝ)) (-(w : ℝ))
    rw [abs_neg] at h
    linarith
  obtain ⟨e, he, heerr⟩ := fma_exists_error I (neg_value I hc) hd hw
    (no_overflow_of_lt I _ (by linarith : |((-cr * dr + w : ℚ) : ℝ)| < I.format.overflowThreshold))
  obtain ⟨f, hf, hferr⟩ := fma_exists_error I ha hb (neg_value I hw)
    (no_overflow_of_lt I _ (by linarith : |((ar * br + -w : ℚ) : ℝ)| < I.format.overflowThreshold))
  have heabs := rounded_magnitude (le_of_lt hr) hemag heerr
  have hfabs := rounded_magnitude (le_of_lt hr) hfmag hferr
  have hep : |(e : ℝ)| ≤ 5 * P := by
    nlinarith [mul_nonneg hP.le (sub_nonneg.mpr hrho)]
  have hfp : |(f : ℝ)| ≤ 5 * P := by
    nlinarith [mul_nonneg hP.le (sub_nonneg.mpr hrho)]
  have hsum : |((f + e : ℚ) : ℝ)| < I.format.overflowThreshold := by
    rw [Rat.cast_add]
    have h := abs_add_le (f : ℝ) (e : ℝ)
    linarith
  obtain ⟨out, ho, _⟩ := binary_exists_error I .add hf he (no_overflow_of_lt I _ hsum)
  exact ⟨w, e, f, out, hw, he, hf, ho⟩

end DistanceAccuracy.Determinant

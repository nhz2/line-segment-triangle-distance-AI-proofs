import DistanceAccuracy.WordFaceProjection
import DistanceAccuracy.DeterminantFinite

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds Determinant

/-- Finiteness of the reciprocal/products/FMA in a face solve from bounded
normalized coefficients. No finite intermediate is assumed. -/
theorem word_face_finite (I : Interchange) [I.Valid]
    {aw bw dw vw : I.Word} {a b d v : ℚ} {T : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hd : value? I dw = some d) (hv : value? I vw = some v)
    (hap : 0 < a) (hv1 : |(v : ℝ)| ≤ 1) (hT : 0 < T)
    (hbT : |(b : ℝ)| ≤ (a : ℝ) * T) (hdT : |(d : ℝ)| ≤ (a : ℝ) * T)
    (hrmax : I.format.unitRoundoff ≤ 1 / 16) (heta : I.format.minSubnormal ≤ T)
    (hnormal : I.format.minNormal ≤ 1 / (a : ℝ))
    (hrecip : 1 / (a : ℝ) < I.format.overflowThreshold)
    (hlim : 8 * T < I.format.overflowThreshold) :
    ∃ c m q : ℚ,
      value? I (IEEEAlgorithm.mul I bw (IEEEAlgorithm.div I (one I) aw)) = some c ∧
      value? I (IEEEAlgorithm.mul I (IEEEAlgorithm.neg I dw)
        (IEEEAlgorithm.div I (one I) aw)) = some m ∧
      value? I (IEEEAlgorithm.fma I (IEEEAlgorithm.neg I vw)
        (IEEEAlgorithm.mul I bw (IEEEAlgorithm.div I (one I) aw))
        (IEEEAlgorithm.mul I (IEEEAlgorithm.neg I dw) (IEEEAlgorithm.div I (one I) aw))) = some q := by
  obtain ⟨ir, di, hir, hie, hdi⟩ := reciprocal_relative I hone ha hap hnormal hrecip
  have har : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hap
  have hr := I.format.unitRoundoff_pos.le
  have hdim := (abs_le.mp hdi).1
  have hdiM := (abs_le.mp hdi).2
  have hdiPos : 0 ≤ 1 + di := by linarith
  have hi0 : 0 ≤ (ir : ℝ) := by rw [hie]; positivity
  have hi2 : (ir : ℝ) ≤ 2 / (a : ℝ) := by
    rw [hie]
    apply (le_div_iff₀ har).2
    field_simp
    linarith
  have hprod (z : ℝ) (hz : |z| ≤ (a : ℝ) * T) : |z * (ir : ℝ)| ≤ 2 * T := by
    rw [abs_mul, abs_of_nonneg hi0]
    have h1 := mul_le_mul hz hi2 hi0 (show 0 ≤ (a : ℝ) * T by positivity)
    have heq : (a : ℝ) * T * (2 / (a : ℝ)) = 2 * T := by field_simp
    linarith
  have hbprod := hprod (b : ℝ) hbT
  have hdprod := hprod (-(d : ℝ)) (by simpa using hdT)
  obtain ⟨c, hc, hce⟩ := binary_exists_error I .mul hb hir
    (no_overflow_of_lt I _ (by simpa only [Software.binaryExact, Rat.cast_mul] using
      (show |(b : ℝ) * (ir : ℝ)| < I.format.overflowThreshold by linarith)))
  obtain ⟨m, hm, hme⟩ := binary_exists_error I .mul (neg_value I hd) hir
    (no_overflow_of_lt I _ (by simpa only [Software.binaryExact, Rat.cast_mul, Rat.cast_neg] using
      (show |-(d : ℝ) * (ir : ℝ)| < I.format.overflowThreshold by linarith)))
  simp only [Software.binaryExact, Rat.cast_mul, Rat.cast_neg] at hce hme
  have hcMag := rounded_magnitude hr hbprod hce
  have hmMag := rounded_magnitude hr hdprod hme
  have hc3 : |(c : ℝ)| ≤ 3 * T := by nlinarith [mul_nonneg hT.le (sub_nonneg.mpr hrmax)]
  have hm3 : |(m : ℝ)| ≤ 3 * T := by nlinarith [mul_nonneg hT.le (sub_nonneg.mpr hrmax)]
  have hq6 : |((-v * c + m : ℚ) : ℝ)| ≤ 6 * T := by
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_neg]
    have h := abs_add_le (-(v : ℝ) * (c : ℝ)) (m : ℝ)
    rw [abs_mul, abs_neg] at h
    have hmul := mul_le_mul hv1 hc3 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  obtain ⟨q, hq, _⟩ := fma_exists_error I (neg_value I hv) hc hm
    (no_overflow_of_lt I _ (by linarith : |((-v * c + m : ℚ) : ℝ)| < I.format.overflowThreshold))
  exact ⟨c, m, q, hc, hm, hq⟩

end DistanceAccuracy.ProjectionRounding

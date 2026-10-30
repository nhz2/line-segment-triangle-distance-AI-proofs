import DistanceAccuracy.DeterminantFinite
import DistanceAccuracy.WordDeterminantVector

namespace DistanceAccuracy.DotWordBounds
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds Determinant

lemma weighted_products_le_norm (a b : E3) :
    3 * |a 0 * b 0| + 2 * |a 1 * b 1| + |a 2 * b 2| ≤ 3 * ‖a‖ * ‖b‖ := by
  have hc := real_inner_le_norm (absVec a) (absVec b)
  simp only [norm_absVec] at hc
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ,
    absVec, abs_mul] at hc
  simp only [abs_mul]
  nlinarith [mul_nonneg (abs_nonneg (a 1)) (abs_nonneg (b 1)),
    mul_nonneg (abs_nonneg (a 2)) (abs_nonneg (b 2))]

/-- Finite mixed dot product and its weighted forward error, derived from a
single bound on all three exact products. -/
theorem dot3_finite_weighted (I : Interchange) [I.Valid]
    {a b : Vec3 I} {ar br : Fin 3 → ℚ} {P : ℝ}
    (ha : ∀ i, value? I (a i) = some (ar i))
    (hb : ∀ i, value? I (b i) = some (br i))
    (hP : 0 < P) (hp : ∀ i, |(ar i : ℝ) * (br i : ℝ)| ≤ P)
    (heta : I.format.minSubnormal ≤ P)
    (hrho : I.format.unitRoundoff ≤ 1 / 16)
    (hlim : 6 * P < I.format.overflowThreshold) :
    ∃ q : ℚ, value? I (dot3 I a b) = some q ∧
      |(q : ℝ) - ((ar 0 : ℝ) * (br 0 : ℝ) + (ar 1 : ℝ) * (br 1 : ℝ) +
        (ar 2 : ℝ) * (br 2 : ℝ))| ≤
      I.format.unitRoundoff * (1 + I.format.unitRoundoff) ^ 2 *
        (3 * |(ar 0 : ℝ) * (br 0 : ℝ)| + 2 * |(ar 1 : ℝ) * (br 1 : ℝ)| +
          |(ar 2 : ℝ) * (br 2 : ℝ)|) + 2 * I.format.minSubnormal := by
  have hr := I.format.unitRoundoff_pos.le
  have h0 : |((ar 0 * br 0 : ℚ) : ℝ)| < I.format.overflowThreshold := by
    rw [Rat.cast_mul]; have := hp 0; linarith
  obtain ⟨p, hpd, hpe⟩ := binary_exists_error I .mul (ha 0) (hb 0) (no_overflow_of_lt I _ h0)
  change value? I (IEEEAlgorithm.mul I (a 0) (b 0)) = some p at hpd
  simp only [Software.binaryExact, Rat.cast_mul] at hpe
  have hpm := rounded_magnitude hr (hp 0) hpe
  have hpb : |(p : ℝ)| ≤ 2 * P := by nlinarith [mul_nonneg hP.le (sub_nonneg.mpr hrho)]
  have h1 : |((ar 1 * br 1 + p : ℚ) : ℝ)| ≤ 3 * P := by
    simp only [Rat.cast_add, Rat.cast_mul]
    have := abs_add_le ((ar 1 : ℝ) * (br 1 : ℝ)) (p : ℝ)
    have := hp 1
    linarith
  obtain ⟨s, hsd, hse⟩ := fma_exists_error I (ha 1) (hb 1) hpd
    (no_overflow_of_lt I _ (by linarith : |((ar 1 * br 1 + p : ℚ) : ℝ)| < I.format.overflowThreshold))
  have hsm := rounded_magnitude hr h1 hse
  have hsb : |(s : ℝ)| ≤ 4 * P := by nlinarith [mul_nonneg hP.le (sub_nonneg.mpr hrho)]
  have h2 : |((ar 2 * br 2 + s : ℚ) : ℝ)| ≤ 5 * P := by
    simp only [Rat.cast_add, Rat.cast_mul]
    have := abs_add_le ((ar 2 : ℝ) * (br 2 : ℝ)) (s : ℝ)
    have := hp 2
    linarith
  obtain ⟨q, hqd, hqe⟩ := fma_exists_error I (ha 2) (hb 2) hsd
    (no_overflow_of_lt I _ (by linarith : |((ar 2 * br 2 + s : ℚ) : ℝ)| < I.format.overflowThreshold))
  refine ⟨q, hqd, ?_⟩
  apply DistanceAccuracy.dot3_error hr hrho
    (show 0 ≤ I.format.minSubnormal by unfold FP.IEEE.Format.minSubnormal; positivity) hpe
  · simpa only [Rat.cast_add, Rat.cast_mul, add_comm] using hse
  · simpa only [Rat.cast_add, Rat.cast_mul, add_comm] using hqe

/-- The general 3rho(1+rho)^2 norm bound for the actual word dot product. -/
theorem dot3_finite_error (I : Interchange) [I.Valid]
    {a b : Vec3 I} {ar br : Fin 3 → ℚ} {P : ℝ}
    (ha : ∀ i, value? I (a i) = some (ar i))
    (hb : ∀ i, value? I (b i) = some (br i))
    (hP : 0 < P) (hp : ∀ i, |(ar i : ℝ) * (br i : ℝ)| ≤ P)
    (heta : I.format.minSubnormal ≤ P)
    (hrho : I.format.unitRoundoff ≤ 1 / 16)
    (hlim : 6 * P < I.format.overflowThreshold) :
    ∃ q : ℚ, value? I (dot3 I a b) = some q ∧
      |(q : ℝ) - ((ar 0 : ℝ) * (br 0 : ℝ) + (ar 1 : ℝ) * (br 1 : ℝ) +
        (ar 2 : ℝ) * (br 2 : ℝ))| ≤
      3 * I.format.unitRoundoff * (1 + I.format.unitRoundoff) ^ 2 *
        ‖realVec ar‖ * ‖realVec br‖ + 2 * I.format.minSubnormal := by
  obtain ⟨q, hq, he⟩ := dot3_finite_weighted I ha hb hP hp heta hrho hlim
  refine ⟨q, hq, ?_⟩
  have hw := weighted_products_le_norm (realVec ar) (realVec br)
  have hr := I.format.unitRoundoff_pos
  have hm := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ I.format.unitRoundoff * (1 + I.format.unitRoundoff) ^ 2 by positivity)
  dsimp [realVec] at hm ⊢
  nlinarith

end DistanceAccuracy.DotWordBounds

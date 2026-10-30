import DistanceAccuracy.DotWordBounds

namespace DistanceAccuracy.DotWordBounds
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds Determinant

/-- A summed-product range budget avoids multiplying the largest coordinate
product by six. This is essential when dotting large cross products near the
permitted coordinate limit. -/
theorem dot3_finite_weighted_sum (I : Interchange) [I.Valid]
    {a b : Vec3 I} {ar br : Fin 3 → ℚ} {P : ℝ}
    (ha : ∀ i, value? I (a i) = some (ar i))
    (hb : ∀ i, value? I (b i) = some (br i))
    (hP : 0 < P)
    (hsum : |(ar 0 : ℝ) * (br 0 : ℝ)| + |(ar 1 : ℝ) * (br 1 : ℝ)| +
      |(ar 2 : ℝ) * (br 2 : ℝ)| ≤ P)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff * P)
    (hrho : I.format.unitRoundoff ≤ 1 / 1024)
    (hlim : (11 / 10 : ℝ) * P < I.format.overflowThreshold) :
    ∃ q : ℚ, value? I (dot3 I a b) = some q ∧
      |(q : ℝ) - ((ar 0 : ℝ) * (br 0 : ℝ) + (ar 1 : ℝ) * (br 1 : ℝ) +
        (ar 2 : ℝ) * (br 2 : ℝ))| ≤
      I.format.unitRoundoff * (1 + I.format.unitRoundoff) ^ 2 *
        (3 * |(ar 0 : ℝ) * (br 0 : ℝ)| + 2 * |(ar 1 : ℝ) * (br 1 : ℝ)| +
          |(ar 2 : ℝ) * (br 2 : ℝ)|) + 2 * I.format.minSubnormal := by
  have hr := I.format.unitRoundoff_pos.le
  have h0 := abs_nonneg ((ar 0 : ℝ) * (br 0 : ℝ))
  have h1 := abs_nonneg ((ar 1 : ℝ) * (br 1 : ℝ))
  have h2 := abs_nonneg ((ar 2 : ℝ) * (br 2 : ℝ))
  have hp0 : |(ar 0 : ℝ) * (br 0 : ℝ)| ≤ P := by linarith only [hsum, h1, h2]
  have hprod : |((ar 0 * br 0 : ℚ) : ℝ)| < I.format.overflowThreshold := by
    rw [Rat.cast_mul]
    linarith only [hp0, hlim, hP]
  obtain ⟨p, hpd, hpe⟩ := binary_exists_error I .mul (ha 0) (hb 0) (no_overflow_of_lt I _ hprod)
  change value? I (IEEEAlgorithm.mul I (a 0) (b 0)) = some p at hpd
  simp only [Software.binaryExact, Rat.cast_mul] at hpe
  have hpm := rounded_magnitude hr (le_refl |(ar 0 : ℝ) * (br 0 : ℝ)|) hpe
  have hrp := mul_le_mul_of_nonneg_right hrho hP.le
  have hpM := mul_le_mul_of_nonneg_left hp0 hr
  have hpb : |(p : ℝ)| ≤ |(ar 0 : ℝ) * (br 0 : ℝ)| + 2 * I.format.unitRoundoff * P := by
    nlinarith only [hpm, hpM, heta, mul_nonneg hr hP.le]
  have hsarg : |((ar 1 * br 1 + p : ℚ) : ℝ)| ≤
      |(ar 0 : ℝ) * (br 0 : ℝ)| + |(ar 1 : ℝ) * (br 1 : ℝ)| + 2 * I.format.unitRoundoff * P := by
    simp only [Rat.cast_add, Rat.cast_mul]
    have h := abs_add_le ((ar 1 : ℝ) * (br 1 : ℝ)) (p : ℝ)
    linarith only [h, hpb]
  have hsarg' : |((ar 1 * br 1 + p : ℚ) : ℝ)| ≤ P + 2 * I.format.unitRoundoff * P := by
    linarith only [hsarg, hsum, h2]
  have hsLim : |((ar 1 * br 1 + p : ℚ) : ℝ)| < I.format.overflowThreshold := by
    nlinarith only [hsarg', hrp, hlim, hP]
  obtain ⟨s, hsd, hse⟩ := fma_exists_error I (ha 1) (hb 1) hpd (no_overflow_of_lt I _ hsLim)
  have hsm := rounded_magnitude hr hsarg hse
  have hsscale := mul_le_mul_of_nonneg_left
    (show |(ar 0 : ℝ) * (br 0 : ℝ)| + |(ar 1 : ℝ) * (br 1 : ℝ)| ≤ P by linarith only [hsum, h2]) hr
  have hr2P := mul_le_mul_of_nonneg_right hrho (mul_nonneg hr hP.le)
  have hsb : |(s : ℝ)| ≤ |(ar 0 : ℝ) * (br 0 : ℝ)| + |(ar 1 : ℝ) * (br 1 : ℝ)| +
      4 * I.format.unitRoundoff * P := by
    nlinarith only [hsm, hsscale, hr2P, heta, mul_nonneg hr hP.le]
  have hqarg : |((ar 2 * br 2 + s : ℚ) : ℝ)| ≤ P + 4 * I.format.unitRoundoff * P := by
    simp only [Rat.cast_add, Rat.cast_mul]
    have h := abs_add_le ((ar 2 : ℝ) * (br 2 : ℝ)) (s : ℝ)
    linarith only [h, hsb, hsum]
  have hqLim : |((ar 2 * br 2 + s : ℚ) : ℝ)| < I.format.overflowThreshold := by
    nlinarith only [hqarg, hrp, hlim, hP]
  obtain ⟨q, hqd, hqe⟩ := fma_exists_error I (ha 2) (hb 2) hsd (no_overflow_of_lt I _ hqLim)
  refine ⟨q, hqd, ?_⟩
  apply DistanceAccuracy.dot3_error hr (by linarith only [hrho])
    (show 0 ≤ I.format.minSubnormal by unfold FP.IEEE.Format.minSubnormal; positivity) hpe
  · simpa only [Rat.cast_add, Rat.cast_mul, add_comm] using hse
  · simpa only [Rat.cast_add, Rat.cast_mul, add_comm] using hqe

theorem dot3_finite_error_sum (I : Interchange) [I.Valid]
    {a b : Vec3 I} {ar br : Fin 3 → ℚ} {P : ℝ}
    (ha : ∀ i, value? I (a i) = some (ar i))
    (hb : ∀ i, value? I (b i) = some (br i))
    (hP : 0 < P)
    (hsum : |(ar 0 : ℝ) * (br 0 : ℝ)| + |(ar 1 : ℝ) * (br 1 : ℝ)| +
      |(ar 2 : ℝ) * (br 2 : ℝ)| ≤ P)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff * P)
    (hrho : I.format.unitRoundoff ≤ 1 / 1024)
    (hlim : (11 / 10 : ℝ) * P < I.format.overflowThreshold) :
    ∃ q : ℚ, value? I (dot3 I a b) = some q ∧
      |(q : ℝ) - ((ar 0 : ℝ) * (br 0 : ℝ) + (ar 1 : ℝ) * (br 1 : ℝ) +
        (ar 2 : ℝ) * (br 2 : ℝ))| ≤
      3 * I.format.unitRoundoff * (1 + I.format.unitRoundoff) ^ 2 *
        ‖realVec ar‖ * ‖realVec br‖ + 2 * I.format.minSubnormal := by
  obtain ⟨q, hq, he⟩ := dot3_finite_weighted_sum I ha hb hP hsum heta hrho hlim
  refine ⟨q, hq, ?_⟩
  have hw := weighted_products_le_norm (realVec ar) (realVec br)
  have hr := I.format.unitRoundoff_pos
  have hm := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ I.format.unitRoundoff * (1 + I.format.unitRoundoff) ^ 2 by positivity)
  dsimp [realVec] at hm ⊢
  nlinarith only [hm, he]

end DistanceAccuracy.DotWordBounds

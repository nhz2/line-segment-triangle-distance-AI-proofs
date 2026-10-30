import DistanceAccuracy.WordDeterminantVector

namespace DistanceAccuracy.Determinant
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge

lemma ordinary_determinant_error (F : FP.IEEE.Format) (a b c d : ℝ)
    (hrmax : F.unitRoundoff ≤ 1 / 4) :
    |F.roundFinite (a * b - F.roundFinite (c * d)) - (a * b - c * d)| ≤
      F.unitRoundoff * |a * b - c * d| +
      F.unitRoundoff * (1 + F.unitRoundoff) * |c * d| + 2 * F.minSubnormal := by
  have hr := F.unitRoundoff_pos.le
  have heta : 0 ≤ F.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hp := F.roundFinite_mixed_error (c * d)
  have hf := F.roundFinite_mixed_error (a * b - F.roundFinite (c * d))
  have hi : |a * b - F.roundFinite (c * d)| ≤ |a * b - c * d| + |F.roundFinite (c * d) - c * d| := by
    have h := abs_sub (a * b - c * d) (F.roundFinite (c * d) - c * d)
    convert h using 1 <;> congr 1 <;> ring
  have ht : |F.roundFinite (a * b - F.roundFinite (c * d)) - (a * b - c * d)| ≤
      |F.roundFinite (a * b - F.roundFinite (c * d)) - (a * b - F.roundFinite (c * d))| +
      |F.roundFinite (c * d) - c * d| := by
    have h := abs_sub (F.roundFinite (a * b - F.roundFinite (c * d)) -
      (a * b - F.roundFinite (c * d))) (F.roundFinite (c * d) - c * d)
    convert h using 1 <;> congr 1 <;> ring
  have h1 := mul_le_mul_of_nonneg_left hi hr
  have h2 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1 + F.unitRoundoff by positivity)
  nlinarith [mul_nonneg heta (sub_nonneg.mpr hrmax)]

lemma word_ordinary_determinant_error (I : Interchange) [I.Valid]
    {a b c d : I.Word} {ar br cr dr w f : ℚ}
    (ha : value? I a = some ar) (hb : value? I b = some br)
    (hc : value? I c = some cr) (hd : value? I d = some dr)
    (hw : value? I (IEEEAlgorithm.mul I c d) = some w)
    (hf : value? I (IEEEAlgorithm.fma I a b (IEEEAlgorithm.neg I (IEEEAlgorithm.mul I c d))) = some f)
    (hrmax : I.format.unitRoundoff ≤ 1 / 4) :
    |(f : ℝ) - ((ar : ℝ) * (br : ℝ) - (cr : ℝ) * (dr : ℝ))| ≤
      I.format.unitRoundoff * |(ar : ℝ) * (br : ℝ) - (cr : ℝ) * (dr : ℝ)| +
      I.format.unitRoundoff * (1 + I.format.unitRoundoff) * |(cr : ℝ) * (dr : ℝ)| +
      2 * I.format.minSubnormal := by
  have hw' := Software.binary_even_roundFinite_of_decode I .mul c d cr dr w hc hd hw
  have hf' := fma_roundFinite_of_decode I ha hb (neg_value I hw) hf
  simp only [Software.binaryExact, Rat.cast_mul] at hw'
  simp only [Rat.cast_neg] at hf'
  rw [hf', hw']
  simpa only [sub_eq_add_neg] using ordinary_determinant_error I.format
    (ar : ℝ) (br : ℝ) (cr : ℝ) (dr : ℝ) hrmax

/-- Finite ordinary cross product and its vector forward error from a product
range envelope. -/
theorem word_cross3_exists_error (I : Interchange) [I.Valid]
    {a b : Vec3 I} {ar br : Fin 3 → ℚ} {B P : ℝ}
    (ha : ∀ i, value? I (a i) = some (ar i))
    (hb : ∀ i, value? I (b i) = some (br i))
    (hB : 0 ≤ B) (hbB : ∀ i, |(br i : ℝ)| ≤ B)
    (hP : 0 < P) (hproducts : ∀ i j, |(ar i : ℝ) * (br j : ℝ)| ≤ P)
    (heta : I.format.minSubnormal ≤ P)
    (hrmax : I.format.unitRoundoff ≤ 1 / 4)
    (hlim : 10 * P < I.format.overflowThreshold) :
    ∃ out : Fin 3 → ℚ,
      (∀ i, value? I (cross3 I a b i) = some (out i)) ∧
      ‖realVec out - exactCross (realVec ar) (realVec br)‖ ≤
        I.format.unitRoundoff * ‖exactCross (realVec ar) (realVec br)‖ +
        I.format.unitRoundoff * (1 + I.format.unitRoundoff) * (‖realVec ar‖ * B) +
        4 * I.format.minSubnormal := by
  have hex (i : Fin 3) := det2_finite I (ha (i + 1)) (hb (i + 2))
    (ha (i + 2)) (hb (i + 1)) hP (hproducts _ _) (hproducts _ _) heta hrmax hlim
  choose w e f out hw he hf ho using hex
  have hcross : ∀ i, value? I (cross3 I a b i) = some (f i) := by
    intro i
    fin_cases i
    · simpa [cross3] using hf 0
    · simpa [cross3] using hf 1
    · simpa [cross3] using hf 2
  refine ⟨f, hcross, ?_⟩
  have hscalar (i : Fin 3) := word_ordinary_determinant_error I
    (ha (i + 1)) (hb (i + 2)) (ha (i + 2)) (hb (i + 1)) (hw i) (hf i) hrmax
  have hr := I.format.unitRoundoff_pos
  have heta0 : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hv := vector_mixed_bound (le_of_lt hr)
    (show 0 ≤ I.format.unitRoundoff * (1 + I.format.unitRoundoff) by positivity)
    (show 0 ≤ 2 * I.format.minSubnormal by positivity)
    (r := realVec f - exactCross (realVec ar) (realVec br))
    (n := exactCross (realVec ar) (realVec br)) (p := selectedProducts (realVec ar) (realVec br))
    (by
      intro i
      fin_cases i
      · simpa [realVec, exactCross, selectedProducts] using hscalar 0
      · simpa [realVec, exactCross, selectedProducts] using hscalar 1
      · simpa [realVec, exactCross, selectedProducts] using hscalar 2)
  have hp := selectedProducts_bound (a := realVec ar) (b := realVec br) hB hbB
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ I.format.unitRoundoff * (1 + I.format.unitRoundoff) by positivity)
  have hs : Real.sqrt (3 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hs' := mul_le_mul_of_nonneg_right hs heta0
  nlinarith

/-- The combined accurate-normal/ordinary-cross relative coefficient still
fits 3.60, including the second-order product term retained in this proof. -/
lemma combined_cross_envelope {rho : ℝ} (hr : 0 ≤ rho)
    (hrmax : rho ≤ 1 / 16777216) :
    3 + rho + (1 + rho) ^ 2 / Real.sqrt 3 ≤ (18 / 5 : ℝ) := by
  have hs : (173 / 100 : ℝ) ≤ Real.sqrt 3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hr2 : rho ^ 2 ≤ rho / 16777216 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrmax)]
  have hU : (1 + rho) ^ 2 ≤ (1000001 / 1000000 : ℝ) := by nlinarith
  have hfrac : (1 + rho) ^ 2 / Real.sqrt 3 ≤ (1000001 / 1000000 : ℝ) / (173 / 100) :=
    div_le_div₀ (by norm_num) hU (by norm_num) hs
  nlinarith

end DistanceAccuracy.Determinant

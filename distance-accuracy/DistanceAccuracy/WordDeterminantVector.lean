import DistanceAccuracy.DeterminantVector
import DistanceAccuracy.DeterminantFinite

namespace DistanceAccuracy.Determinant
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge

noncomputable def realVec (v : Fin 3 → ℚ) : E3 := WithLp.toLp 2 (fun i => (v i : ℝ))

/-- The actual compensated cross-product words satisfy the mixed vector bound.
Only finite decodings of inputs and the four scalar intermediates are assumed;
all rounding estimates are derived from the IEEE library. -/
theorem word_cross3Accurate_error (I : Interchange) [I.Valid]
    {a b : Vec3 I} {ar br wr er fr out : Fin 3 → ℚ} {B : ℝ}
    (ha : ∀ i, value? I (a i) = some (ar i))
    (hb : ∀ i, value? I (b i) = some (br i))
    (hw : ∀ i, value? I (IEEEAlgorithm.mul I (a (i + 2)) (b (i + 1))) = some (wr i))
    (he : ∀ i, value? I (IEEEAlgorithm.fma I (IEEEAlgorithm.neg I (a (i + 2)))
      (b (i + 1)) (IEEEAlgorithm.mul I (a (i + 2)) (b (i + 1)))) = some (er i))
    (hf : ∀ i, value? I (IEEEAlgorithm.fma I (a (i + 1)) (b (i + 2))
      (IEEEAlgorithm.neg I (IEEEAlgorithm.mul I (a (i + 2)) (b (i + 1))))) = some (fr i))
    (ho : ∀ i, value? I (cross3Accurate I a b i) = some (out i))
    (hB : 0 ≤ B) (hbB : ∀ i, |(br i : ℝ)| ≤ B)
    (hrmax : I.format.unitRoundoff ≤ 1 / 4) :
    ‖realVec out - exactCross (realVec ar) (realVec br)‖ ≤
      (2 * I.format.unitRoundoff + I.format.unitRoundoff ^ 2) *
        ‖exactCross (realVec ar) (realVec br)‖ +
      I.format.unitRoundoff ^ 2 * (1 + I.format.unitRoundoff) * (‖realVec ar‖ * B) +
      4 * I.format.minSubnormal := by
  have hscalar (i : Fin 3) := det2_mixed_error I
    (ha (i + 1)) (hb (i + 2)) (ha (i + 2)) (hb (i + 1))
    (hw i) (he i) (hf i)
    (show value? I (det2 I (a (i + 1)) (b (i + 2)) (a (i + 2)) (b (i + 1))) = some (out i) by
      fin_cases i
      · simpa [cross3Accurate] using ho 0
      · simpa [cross3Accurate] using ho 1
      · simpa [cross3Accurate] using ho 2) hrmax
  have hr := I.format.unitRoundoff_pos
  have heta : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hv := compensated_vector_bound (le_of_lt hr) heta
    (r := realVec out - exactCross (realVec ar) (realVec br))
    (n := exactCross (realVec ar) (realVec br)) (p := selectedProducts (realVec ar) (realVec br))
    (by
      intro i
      fin_cases i
      · simpa [realVec, exactCross, selectedProducts] using hscalar 0
      · simpa [realVec, exactCross, selectedProducts] using hscalar 1
      · simpa [realVec, exactCross, selectedProducts] using hscalar 2)
  have hp := selectedProducts_bound (a := realVec ar) (b := realVec br) hB hbB
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ I.format.unitRoundoff ^ 2 * (1 + I.format.unitRoundoff) by positivity)
  linarith

/-- Finite output and the vector accuracy bound derived from a single product
range envelope, rather than assumed intermediate finiteness. -/
theorem word_cross3Accurate_exists_error (I : Interchange) [I.Valid]
    {a b : Vec3 I} {ar br : Fin 3 → ℚ} {B P : ℝ}
    (ha : ∀ i, value? I (a i) = some (ar i))
    (hb : ∀ i, value? I (b i) = some (br i))
    (hB : 0 ≤ B) (hbB : ∀ i, |(br i : ℝ)| ≤ B)
    (hP : 0 < P) (hproducts : ∀ i j, |(ar i : ℝ) * (br j : ℝ)| ≤ P)
    (heta : I.format.minSubnormal ≤ P)
    (hrmax : I.format.unitRoundoff ≤ 1 / 4)
    (hlim : 10 * P < I.format.overflowThreshold) :
    ∃ out : Fin 3 → ℚ,
      (∀ i, value? I (cross3Accurate I a b i) = some (out i)) ∧
      ‖realVec out - exactCross (realVec ar) (realVec br)‖ ≤
        (2 * I.format.unitRoundoff + I.format.unitRoundoff ^ 2) *
          ‖exactCross (realVec ar) (realVec br)‖ +
        I.format.unitRoundoff ^ 2 * (1 + I.format.unitRoundoff) * (‖realVec ar‖ * B) +
        4 * I.format.minSubnormal := by
  have hex (i : Fin 3) := det2_finite I (ha (i + 1)) (hb (i + 2))
    (ha (i + 2)) (hb (i + 1)) hP (hproducts _ _) (hproducts _ _) heta hrmax hlim
  choose w e f out hw he hf ho using hex
  have hcross : ∀ i, value? I (cross3Accurate I a b i) = some (out i) := by
    intro i
    fin_cases i
    · simpa [cross3Accurate] using ho 0
    · simpa [cross3Accurate] using ho 1
    · simpa [cross3Accurate] using ho 2
  exact ⟨out, hcross, word_cross3Accurate_error I ha hb hw he hf hcross hB hbB hrmax⟩

/-- The normalized error of the actual accurate cross-product in the thick
branch, with intermediate finiteness proved from the product envelope. -/
theorem word_cross3Accurate_thick (I : Interchange) [I.Valid]
    {a b : Vec3 I} {ar br : Fin 3 → ℚ} {D P h : ℝ}
    (ha : ∀ i, value? I (a i) = some (ar i))
    (hb : ∀ i, value? I (b i) = some (br i))
    (hD : 0 < D) (hbB : ∀ i, |(br i : ℝ)| ≤ D / Real.sqrt 3)
    (hP : 0 < P) (hproducts : ∀ i j, |(ar i : ℝ) * (br j : ℝ)| ≤ P)
    (heta : I.format.minSubnormal ≤ P)
    (hrmax : I.format.unitRoundoff ≤ 1 / 16777216)
    (hlim : 10 * P < I.format.overflowThreshold)
    (hA : 0 < ‖realVec ar‖) (hh : 0 < h) (he : I.format.minSubnormal = h ^ 4)
    (hfloor : h ^ 2 ≤ ‖exactCross (realVec ar) (realVec br)‖)
    (harea : 16 * I.format.unitRoundoff * ‖realVec ar‖ * D ≤
      ‖exactCross (realVec ar) (realVec br)‖) :
    ∃ out : Fin 3 → ℚ,
      (∀ i, value? I (cross3Accurate I a b i) = some (out i)) ∧
      ‖realVec out - exactCross (realVec ar) (realVec br)‖ /
        ‖exactCross (realVec ar) (realVec br)‖ ≤
          (2037 / 1000) * I.format.unitRoundoff + 4 * h ^ 2 := by
  obtain ⟨out, ho, herr⟩ := word_cross3Accurate_exists_error I ha hb
    (show 0 ≤ D / Real.sqrt 3 by positivity) hbB hP hproducts heta (by linarith) hlim
  refine ⟨out, ho, ?_⟩
  apply thick_normal_budget I.format.unitRoundoff_pos hrmax hA hD hh he hfloor harea
  simpa only [mul_div_assoc] using herr

end DistanceAccuracy.Determinant

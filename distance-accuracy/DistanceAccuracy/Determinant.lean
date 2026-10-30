import DistanceAccuracy.IEEEBridge
import FP.IEEE.ProductRoundoff
import FP.IEEE.Software.ProductBounds

/-!
# Compensated determinant bounds without an imported 2u theorem

The elementary mixed bound retains a second-order term proportional to the
rounded product. This can be paired with a thin-triangle edge fallback instead
of requiring the sharper, substantially more difficult, 2u relative theorem.
No determinant-accuracy hypothesis is assumed below.
-/
namespace DistanceAccuracy.Determinant

/-- Accumulating the errors of the corrected FMA and final addition. -/
lemma compensated_error {rho eta z eps e f out : ℝ}
    (hr : 0 ≤ rho) (he : |e - eps| ≤ eta / 2)
    (hf : |f - (z - eps)| ≤ rho * |z - eps| + eta / 2)
    (ho : |out - (f + e)| ≤ rho * |f + e| + eta / 2) :
    |out - z| ≤ (2 * rho + rho ^ 2) * |z| +
      rho * (1 + rho) * |eps| + (3 / 2 + rho) * eta := by
  have hsum : |f + e - z| ≤ |f - (z - eps)| + |e - eps| := by
    have h := abs_add_le (f - (z - eps)) (e - eps)
    convert h using 1 <;> congr 1 <;> ring
  have hmag : |f + e| ≤ |z| + |f + e - z| := by
    have h := abs_add_le z (f + e - z)
    convert h using 1 <;> congr 1 <;> ring
  have htotal : |out - z| ≤ |out - (f + e)| + |f + e - z| := by
    have h := abs_add_le (out - (f + e)) (f + e - z)
    convert h using 1 <;> congr 1 <;> ring
  have hze : |z - eps| ≤ |z| + |eps| := abs_sub _ _
  have h₁ := mul_le_mul_of_nonneg_left hsum hr
  have h₂ := mul_le_mul_of_nonneg_left hmag hr
  have h₃ := mul_le_mul_of_nonneg_left hf hr
  have h₄ := mul_le_mul_of_nonneg_left he hr
  have h₅ := mul_le_mul_of_nonneg_left hze hr
  have h₆ := mul_le_mul_of_nonneg_left hze (sq_nonneg rho)
  nlinarith

/-- Product rounding makes the retained error genuinely second order. -/
lemma compensated_product_error {rho eta z product eps e f out : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1 / 4) (heta : 0 ≤ eta)
    (hp : |eps| ≤ rho * |product| + eta / 2)
    (he : |e - eps| ≤ eta / 2)
    (hf : |f - (z - eps)| ≤ rho * |z - eps| + eta / 2)
    (ho : |out - (f + e)| ≤ rho * |f + e| + eta / 2) :
    |out - z| ≤ (2 * rho + rho ^ 2) * |z| +
      rho ^ 2 * (1 + rho) * |product| + 2 * eta := by
  have h := compensated_error hr he hf ho
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ rho * (1 + rho) by positivity)
  have hrs := mul_self_le_mul_self hr hrmax
  have hc : 0 ≤ 1 / 2 - 3 / 2 * rho - rho ^ 2 / 2 := by nlinarith
  have hec := mul_nonneg hc heta
  nlinarith

/-- The residual-underflow subcase of the sharper paper bound. -/
lemma compensated_small_residual {rho eta z eps e f out : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1 / 4) (heta : 0 ≤ eta)
    (hsmall : rho * |eps| ≤ eta)
    (he : |e - eps| ≤ eta / 2)
    (hf : |f - (z - eps)| ≤ rho * |z - eps| + eta / 2)
    (ho : |out - (f + e)| ≤ rho * |f + e| + eta / 2) :
    |out - z| ≤ (2 * rho + rho ^ 2) * |z| + 3 * eta := by
  have h := compensated_error hr he hf ho
  have h₁ := mul_le_mul_of_nonneg_left hsmall hr
  have h₂ := mul_le_mul_of_nonneg_right hrmax heta
  nlinarith

open FP.IEEE

/-- Exact real-valued evaluation schedule of the compensated determinant.
Upper overflow is intentionally dealt with by the word-level bridge, not by
pretending a real-valued rounding function can return an infinity. -/
noncomputable def kahan (F : FP.IEEE.Format) (a b c d : ℝ) : ℝ :=
  let w := F.roundFinite (c * d)
  let e := F.roundFinite (w - c * d)
  let f := F.roundFinite (a * b - w)
  F.roundFinite (f + e)

/-- The correction FMA has a half-subnormal absolute defect, for the sign
orientation used by `IEEEAlgorithm.det2`. -/
theorem correction_error (F : FP.IEEE.Format) {c d : ℝ}
    (hc : F.Representable c) (hd : F.Representable d)
    (hrange : |c * d| < F.overflowThreshold) :
    |F.roundFinite (F.roundFinite (c * d) - c * d) -
      (F.roundFinite (c * d) - c * d)| ≤ F.minSubnormal / 2 := by
  have h := F.roundFinite_product_residual_error hc hd hrange
  have hneg : F.roundFinite (c * d) - c * d = -(c * d - F.roundFinite (c * d)) := by ring
  rw [hneg, F.roundFinite_neg]
  simpa only [neg_sub_neg, abs_sub_comm] using h

/-- Unconditional mixed determinant estimate, given only representability of
the product operands and finiteness of that product. Neither the determinant
nor its correction must be normal, and arbitrary cancellation is allowed. -/
theorem kahan_mixed_error (F : FP.IEEE.Format) {a b c d : ℝ}
    (hc : F.Representable c) (hd : F.Representable d)
    (hrange : |c * d| < F.overflowThreshold)
    (hrhomax : F.unitRoundoff ≤ 1 / 4) :
    |kahan F a b c d - (a * b - c * d)| ≤
      (2 * F.unitRoundoff + F.unitRoundoff ^ 2) * |a * b - c * d| +
      F.unitRoundoff ^ 2 * (1 + F.unitRoundoff) * |c * d| + 2 * F.minSubnormal := by
  let w := F.roundFinite (c * d)
  let eps := w - c * d
  let e := F.roundFinite eps
  let f := F.roundFinite (a * b - w)
  have hp : |eps| ≤ F.unitRoundoff * |c * d| + F.minSubnormal / 2 :=
    F.roundFinite_mixed_error (c * d)
  have he : |e - eps| ≤ F.minSubnormal / 2 := correction_error F hc hd hrange
  have hf : |f - ((a * b - c * d) - eps)| ≤
      F.unitRoundoff * |(a * b - c * d) - eps| + F.minSubnormal / 2 := by
    have h := F.roundFinite_mixed_error (a * b - w)
    convert h using 1 <;> dsimp [f, eps] <;> ring_nf
  exact compensated_product_error F.unitRoundoff_pos.le hrhomax
    (by unfold FP.IEEE.Format.minSubnormal; positivity)
    hp he hf (F.roundFinite_mixed_error (f + e))

open FP.IEEE.Interchange
open IEEEAlgorithm IEEEBridge

/-- Recover the finite FMA rounding equation from the concrete word operation. -/
lemma fma_roundFinite_of_decode (I : Interchange) [I.Valid]
    {a b c : I.Word} {x y z r : ℚ}
    (ha : value? I a = some x) (hb : value? I b = some y) (hc : value? I c = some z)
    (hr : value? I (IEEEAlgorithm.fma I a b c) = some r) :
    (r : ℝ) = I.format.roundFinite ((x : ℝ) * (y : ℝ) + (z : ℝ)) := by
  have h := Software.mixedFma_even_cast I I I I a b c x y z ha hb hc
  rw [show I.decode? (Software.mixedFma I I I I .nearestEven a b c).value = some (r : ℝ)
    from real_decode I hr] at h
  unfold FP.IEEE.Format.round? at h
  split_ifs at h with hfin
  · exact Option.some.inj h

lemma neg_value (I : Interchange) [I.Valid] {a : I.Word} {x : ℚ}
    (ha : value? I a = some x) : value? I (IEEEAlgorithm.neg I a) = some (-x) := by
  have h := Software.negate_toRat? I a
  rw [show (Datum.decode I a).toRat? = some x from ha] at h
  exact h

/-- The real-valued schedule is the decoded concrete `det2` schedule. The
premises assert finite decoding only; they contain no numerical-accuracy bound. -/
theorem det2_decoded (I : Interchange) [I.Valid]
    {a b c d : I.Word} {ar br cr dr w e f out : ℚ}
    (ha : value? I a = some ar) (hb : value? I b = some br)
    (hc : value? I c = some cr) (hd : value? I d = some dr)
    (hw : value? I (IEEEAlgorithm.mul I c d) = some w)
    (he : value? I (IEEEAlgorithm.fma I (IEEEAlgorithm.neg I c) d
      (IEEEAlgorithm.mul I c d)) = some e)
    (hf : value? I (IEEEAlgorithm.fma I a b (IEEEAlgorithm.neg I
      (IEEEAlgorithm.mul I c d))) = some f)
    (ho : value? I (IEEEAlgorithm.det2 I a b c d) = some out) :
    (out : ℝ) = kahan I.format ar br cr dr := by
  have hw' := Software.binary_even_roundFinite_of_decode I .mul c d cr dr w hc hd hw
  simp only [Software.binaryExact, Rat.cast_mul] at hw'
  have he' := fma_roundFinite_of_decode I (neg_value I hc) hd hw he
  have hf' := fma_roundFinite_of_decode I ha hb (neg_value I hw) hf
  have ho' := Software.binary_even_roundFinite_of_decode I .add _ _ f e out hf he ho
  simp only [Software.binaryExact, Rat.cast_add] at ho'
  simp only [Rat.cast_neg] at he' hf'
  rw [show -(cr : ℝ) * (dr : ℝ) + (w : ℝ) = (w : ℝ) - (cr : ℝ) * (dr : ℝ) by ring] at he'
  rw [show (ar : ℝ) * (br : ℝ) + -(w : ℝ) = (ar : ℝ) * (br : ℝ) - (w : ℝ) by ring] at hf'
  rw [ho', hf', he', hw']
  rfl

/-- An error bound for the actual word-level compensated determinant. -/
theorem det2_mixed_error (I : Interchange) [I.Valid]
    {a b c d : I.Word} {ar br cr dr w e f out : ℚ}
    (ha : value? I a = some ar) (hb : value? I b = some br)
    (hc : value? I c = some cr) (hd : value? I d = some dr)
    (hw : value? I (IEEEAlgorithm.mul I c d) = some w)
    (he : value? I (IEEEAlgorithm.fma I (IEEEAlgorithm.neg I c) d
      (IEEEAlgorithm.mul I c d)) = some e)
    (hf : value? I (IEEEAlgorithm.fma I a b (IEEEAlgorithm.neg I
      (IEEEAlgorithm.mul I c d))) = some f)
    (ho : value? I (IEEEAlgorithm.det2 I a b c d) = some out)
    (hrhomax : I.format.unitRoundoff ≤ 1 / 4) :
    |(out : ℝ) - ((ar : ℝ) * (br : ℝ) - (cr : ℝ) * (dr : ℝ))| ≤
      (2 * I.format.unitRoundoff + I.format.unitRoundoff ^ 2) *
        |(ar : ℝ) * (br : ℝ) - (cr : ℝ) * (dr : ℝ)| +
      I.format.unitRoundoff ^ 2 * (1 + I.format.unitRoundoff) *
        |(cr : ℝ) * (dr : ℝ)| + 2 * I.format.minSubnormal := by
  rw [det2_decoded I ha hb hc hd hw he hf ho]
  apply kahan_mixed_error I.format
    (Software.rat_representable_of_decode I c cr hc)
    (Software.rat_representable_of_decode I d dr hd)
  · simpa only [Software.binaryExact, Rat.cast_mul] using
      Software.binary_even_range_of_decode I .mul c d cr dr w hc hd hw
  · exact hrhomax

end DistanceAccuracy.Determinant

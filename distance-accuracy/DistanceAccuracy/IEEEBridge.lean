import DistanceAccuracy.IEEEAlgorithm
import DistanceAccuracy.Rounding
import DistanceAccuracy.Formats

/-!
# Deriving local error bounds from actual IEEE operations

The local rounding inequalities are consequences of the FP library's proved
rounding semantics, rather than free assumptions about an unspecified rounding
function. Finiteness and no-overflow conditions remain explicit here; they must
be discharged at each use in the geometric algorithm.
-/
namespace DistanceAccuracy.IEEEBridge
open FP.IEEE FP.IEEE.Interchange
open IEEEAlgorithm

variable (I : Interchange) [I.Valid]

def value? (w : I.Word) : Option ℚ := (Datum.decode I w).toRat?

lemma real_decode {w : I.Word} {x : ℚ} (h : value? I w = some x) :
    I.decode? w = some (x : ℝ) := by
  have hd := Datum.toRat?_decode I w
  rw [show (Datum.decode I w).toRat? = some x from h] at hd
  exact hd.symm

lemma mul_error {a b : I.Word} {x y p : ℚ}
    (ha : value? I a = some x) (hb : value? I b = some y)
    (hp : value? I (IEEEAlgorithm.mul I a b) = some p)
    (ho : Software.overflowWithMode I.format .nearestEven (x * y) = false) :
    |(p : ℝ) - (x : ℝ) * (y : ℝ)| ≤
      I.format.unitRoundoff * |(x : ℝ) * (y : ℝ)| + I.format.minSubnormal / 2 := by
  obtain ⟨r, hr, he⟩ := Software.binary_even_mixed_error I .mul a b x y ha hb ho
  have hp' := real_decode I hp
  have hsame : r = (p : ℝ) := Option.some.inj (hr.symm.trans hp')
  simpa [hsame, Software.binaryExact, Rat.cast_mul] using he

lemma fma_error {a b c : I.Word} {x y z r : ℚ}
    (ha : value? I a = some x) (hb : value? I b = some y) (hc : value? I c = some z)
    (hr : value? I (IEEEAlgorithm.fma I a b c) = some r)
    (ho : Software.overflowWithMode I.format .nearestEven (x * y + z) = false) :
    |(r : ℝ) - ((x : ℝ) * (y : ℝ) + (z : ℝ))| ≤
      I.format.unitRoundoff * |(x : ℝ) * (y : ℝ) + (z : ℝ)| + I.format.minSubnormal / 2 := by
  obtain ⟨v, hv, he⟩ := Software.mixedFma_even_mixed_error I I I I a b c x y z ha hb hc ho
  have hr' := real_decode I hr
  have hsame : v = (r : ℝ) := Option.some.inj (hv.symm.trans hr')
  simpa [hsame, Rat.cast_mul, Rat.cast_add] using he

/-- The actual nested-FMA dot product satisfies the weighted bound once its
three operation ranges are proved. Underflow is allowed throughout. -/
theorem dot3_error {a b : Vec3 I} {x y : Fin 3 → ℚ} {p s q : ℚ}
    (ha : ∀ k, value? I (a k) = some (x k))
    (hb : ∀ k, value? I (b k) = some (y k))
    (hp : value? I (IEEEAlgorithm.mul I (a 0) (b 0)) = some p)
    (hs : value? I (IEEEAlgorithm.fma I (a 1) (b 1) (IEEEAlgorithm.mul I (a 0) (b 0))) = some s)
    (hq : value? I (IEEEAlgorithm.dot3 I a b) = some q)
    (hop : Software.overflowWithMode I.format .nearestEven (x 0 * y 0) = false)
    (hos : Software.overflowWithMode I.format .nearestEven (x 1 * y 1 + p) = false)
    (hoq : Software.overflowWithMode I.format .nearestEven (x 2 * y 2 + s) = false)
    (hrho : I.format.unitRoundoff ≤ 1 / 16) :
    |(q : ℝ) - ((x 0 : ℝ) * (y 0 : ℝ) + (x 1 : ℝ) * (y 1 : ℝ) + (x 2 : ℝ) * (y 2 : ℝ))| ≤
      I.format.unitRoundoff * (1 + I.format.unitRoundoff) ^ 2 *
        (3 * |(x 0 : ℝ) * (y 0 : ℝ)| + 2 * |(x 1 : ℝ) * (y 1 : ℝ)| +
          |(x 2 : ℝ) * (y 2 : ℝ)|) + 2 * I.format.minSubnormal := by
  have h1 := mul_error I (ha 0) (hb 0) hp hop
  have h2 := fma_error I (ha 1) (hb 1) hp hs hos
  have h3 := fma_error I (ha 2) (hb 2) hs hq hoq
  apply DistanceAccuracy.dot3_error I.format.unitRoundoff_pos.le hrho
    (show 0 ≤ I.format.minSubnormal by unfold FP.IEEE.Format.minSubnormal; positivity)
    h1
  · simpa only [add_comm] using h2
  · simpa only [add_comm] using h3

/-- The abstract proof's format constants match the concrete IEEE library. -/
lemma fp32_parameters :
    fp32.format.unitRoundoff = Format.binary32.rho ∧
    fp32.format.minNormal = Format.binary32.leastNormal ∧
    fp32.format.minSubnormal = Format.binary32.leastSubnormal := by
  norm_num [fp32, FP.IEEE.binary32, FP.IEEE.Format.unitRoundoff, FP.IEEE.Format.minNormal,
    FP.IEEE.Format.minSubnormal, Format.rho, Format.leastNormal, Format.leastSubnormal]

set_option exponentiation.threshold 2048 in
lemma fp64_parameters :
    fp64.format.unitRoundoff = Format.binary64.rho ∧
    fp64.format.minNormal = Format.binary64.leastNormal ∧
    fp64.format.minSubnormal = Format.binary64.leastSubnormal := by
  norm_num [fp64, FP.IEEE.binary64, FP.IEEE.Format.unitRoundoff, FP.IEEE.Format.minNormal,
    FP.IEEE.Format.minSubnormal, Format.rho, Format.leastNormal, Format.leastSubnormal]

end DistanceAccuracy.IEEEBridge

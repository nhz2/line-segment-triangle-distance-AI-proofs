import DistanceAccuracy.ProjectionRounding
import DistanceAccuracy.Determinant
import DistanceAccuracy.OperationBounds

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge

/-- Finite word division agrees with the verified nearest-even real rounding
operation. Finiteness of the output replaces an extra overflow premise. -/
lemma div_roundFinite_of_decode (I : Interchange) [I.Valid]
    {a b : I.Word} {x y q : ℚ}
    (ha : value? I a = some x) (hb : value? I b = some y) (hy : y ≠ 0)
    (hq : value? I (IEEEAlgorithm.div I a b) = some q) :
    (q : ℝ) = I.format.roundFinite ((x : ℝ) / (y : ℝ)) := by
  have h := Software.mixedDiv_even_cast I I I a b x y ha hb hy
  rw [show I.decode? (Software.mixedDiv I I I .nearestEven a b).value = some (q : ℝ)
    from real_decode I hq] at h
  unfold FP.IEEE.Format.round? at h
  split_ifs at h with hfin
  exact Option.some.inj h

/-- Multiplicative-plus-additive decomposition derived from concrete IEEE
word division, including subnormal results and zero exact numerators. -/
theorem word_division_decomposition (I : Interchange) [I.Valid]
    {a b : I.Word} {x y q : ℚ}
    (ha : value? I a = some x) (hb : value? I b = some y) (hy : y ≠ 0)
    (hq : value? I (IEEEAlgorithm.div I a b) = some q) :
    ∃ delta zeta : ℝ,
      (q : ℝ) = ((x : ℝ) / (y : ℝ)) * (1 + delta) + zeta ∧
      |delta| ≤ I.format.unitRoundoff ∧ |zeta| ≤ I.format.minSubnormal / 2 := by
  have he := I.format.roundFinite_mixed_error ((x : ℝ) / (y : ℝ))
  rw [← div_roundFinite_of_decode I ha hb hy hq] at he
  apply relative_absolute_decomposition (le_of_lt I.format.unitRoundoff_pos) _ he
  unfold FP.IEEE.Format.minSubnormal
  positivity

/-- Direct clamped quotient KKT derived from concrete IEEE division. The
caller connects the finite clamped word to the displayed real clamp. -/
theorem word_negative_division_optimal (I : Interchange) [I.Valid]
    {aw bw : I.Word} {a b q : ℚ} {x lo hi : ℝ}
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hap : 0 < a) (hr : I.format.unitRoundoff < 1)
    (hq : value? I (IEEEAlgorithm.div I (IEEEAlgorithm.neg I bw) aw) = some q)
    (hlohi : lo ≤ hi) (hxlo : lo ≤ x) (hxhi : x ≤ hi) :
    ∃ delta zeta : ℝ, |delta| ≤ I.format.unitRoundoff ∧
      |zeta| ≤ I.format.minSubnormal / 2 ∧
      0 ≤ (((a : ℝ) / (1 + delta)) * max lo (min hi (q : ℝ)) +
        ((b : ℝ) - (a : ℝ) / (1 + delta) * zeta)) *
        (x - max lo (min hi (q : ℝ))) := by
  obtain ⟨delta, zeta, heq, hd, hz⟩ := word_division_decomposition I
    (Determinant.neg_value I hb) ha (ne_of_gt hap) hq
  refine ⟨delta, zeta, hd, hz, ?_⟩
  have hdl := (abs_le.mp hd).1
  have hdpos : 0 < 1 + delta := by linarith
  have har : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hap
  apply quotient_effective_optimal har hdpos _ hlohi hxlo hxhi
  simpa only [Rat.cast_neg] using heq

/-- For finite input, the concrete NaN-aware clamp equals the exact interval
clamp. This connects the KKT statement above to the algorithm's actual word. -/
lemma clamp01nan_finite (I : Interchange) [I.Valid] {w : I.Word} {q : ℚ}
    (hone : value? I (one I) = some 1) (hw : value? I w = some q) :
    value? I (clamp01nan I w) = some (max 0 (min 1 q)) := by
  have hz := OperationBounds.zero_value I
  by_cases hp : 0 < q
  · have hgt : gt I w (zero I) = true := (OperationBounds.gt_finite I hw hz).mpr hp
    by_cases hq : q < 1
    · have hlt : lt I w (one I) = true := (OperationBounds.lt_finite I hw hone).mpr hq
      simp [clamp01nan, hgt, hlt, hw, min_eq_right hq.le, max_eq_right hp.le]
    · have hlt : lt I w (one I) = false := by
        cases hh : lt I w (one I)
        · rfl
        · exact False.elim (hq ((OperationBounds.lt_finite I hw hone).mp hh))
      have h1q : 1 ≤ q := le_of_not_gt hq
      simp [clamp01nan, hgt, hlt, hone, min_eq_left h1q]
  · have hgt : gt I w (zero I) = false := by
      cases hh : gt I w (zero I)
      · rfl
      · exact False.elim (hp ((OperationBounds.gt_finite I hw hz).mp hh))
    have hlt : lt I (zero I) (one I) = true := (OperationBounds.lt_finite I hz hone).mpr (by norm_num)
    have hq0 : q ≤ 0 := le_of_not_gt hp
    have hq1 : q ≤ 1 := by linarith
    simp [clamp01nan, hgt, hlt, hz, min_eq_right hq1, max_eq_left hq0]

/-- KKT for the decoded parameter actually returned by clamp01nan, under
finite positive-denominator division. -/
theorem clamped_negative_division_optimal (I : Interchange) [I.Valid]
    {aw bw : I.Word} {a b q t : ℚ} {x : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hap : 0 < a) (hr : I.format.unitRoundoff < 1)
    (hq : value? I (IEEEAlgorithm.div I (IEEEAlgorithm.neg I bw) aw) = some q)
    (ht : value? I (clamp01nan I (IEEEAlgorithm.div I (IEEEAlgorithm.neg I bw) aw)) = some t)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ delta zeta : ℝ, |delta| ≤ I.format.unitRoundoff ∧
      |zeta| ≤ I.format.minSubnormal / 2 ∧
      0 ≤ (((a : ℝ) / (1 + delta)) * (t : ℝ) +
        ((b : ℝ) - (a : ℝ) / (1 + delta) * zeta)) * (x - (t : ℝ)) := by
  have hc := clamp01nan_finite I hone hq
  rw [ht] at hc
  have htc : t = max 0 (min 1 q) := Option.some.inj hc
  have htcr : (t : ℝ) = max 0 (min 1 (q : ℝ)) := by exact_mod_cast htc
  rw [htcr]
  exact word_negative_division_optimal I ha hb hap hr hq (by norm_num) hx0 hx1

/-- A normal-range reciprocal has a pure relative factor, with finiteness
proved from the exact reciprocal range. -/
theorem reciprocal_relative (I : Interchange) [I.Valid]
    {aw : I.Word} {a : ℚ}
    (hone : value? I (one I) = some 1) (ha : value? I aw = some a)
    (hap : 0 < a)
    (hnormal : I.format.minNormal ≤ 1 / (a : ℝ))
    (hlim : 1 / (a : ℝ) < I.format.overflowThreshold) :
    ∃ ir : ℚ, ∃ delta : ℝ,
      value? I (IEEEAlgorithm.div I (one I) aw) = some ir ∧
      (ir : ℝ) = (1 / (a : ℝ)) * (1 + delta) ∧ |delta| ≤ I.format.unitRoundoff := by
  have har : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hap
  have hrec : 0 < 1 / (a : ℝ) := by positivity
  obtain ⟨ir, hi, _⟩ := OperationBounds.div_exists_error I hone ha (ne_of_gt hap)
    (OperationBounds.no_overflow_of_lt I _ (by simpa only [Rat.cast_div, Rat.cast_one, abs_of_pos hrec] using hlim))
  have heq := div_roundFinite_of_decode I hone ha (ne_of_gt hap) hi
  norm_num only [Rat.cast_one] at heq
  have he := (I.format.roundFinite_abs_error (1 / (a : ℝ))).trans
    (I.format.half_quantum_le_relative (by simpa only [abs_of_pos hrec] using hnormal))
  rw [← heq] at he
  obtain ⟨delta, zeta, hform, hd, hz⟩ := relative_absolute_decomposition (q := (ir : ℝ)) (x := 1 / (a : ℝ))
    I.format.unitRoundoff_pos.le (le_refl (0 : ℝ)) (by simpa using he)
  have hz0 : zeta = 0 := by simpa using hz
  exact ⟨ir, delta, hi, by simpa [hz0] using hform, hd⟩

/-- Mixed decomposition of a finite decoded word multiplication. -/
theorem word_multiplication_decomposition (I : Interchange) [I.Valid]
    {aw bw : I.Word} {a b p : ℚ}
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hp : value? I (IEEEAlgorithm.mul I aw bw) = some p) :
    ∃ delta zeta : ℝ, (p : ℝ) = ((a : ℝ) * (b : ℝ)) * (1 + delta) + zeta ∧
      |delta| ≤ I.format.unitRoundoff ∧ |zeta| ≤ I.format.minSubnormal / 2 := by
  have heq := Software.binary_even_roundFinite_of_decode I .mul aw bw a b p ha hb hp
  simp only [Software.binaryExact, Rat.cast_mul] at heq
  have he := I.format.roundFinite_mixed_error ((a : ℝ) * (b : ℝ))
  rw [← heq] at he
  apply relative_absolute_decomposition I.format.unitRoundoff_pos.le _ he
  unfold FP.IEEE.Format.minSubnormal
  positivity

/-- Mixed decomposition of a finite decoded word FMA. -/
theorem word_fma_decomposition (I : Interchange) [I.Valid]
    {aw bw cw : I.Word} {a b c p : ℚ}
    (ha : value? I aw = some a) (hb : value? I bw = some b) (hc : value? I cw = some c)
    (hp : value? I (IEEEAlgorithm.fma I aw bw cw) = some p) :
    ∃ delta zeta : ℝ, (p : ℝ) = ((a : ℝ) * (b : ℝ) + (c : ℝ)) * (1 + delta) + zeta ∧
      |delta| ≤ I.format.unitRoundoff ∧ |zeta| ≤ I.format.minSubnormal / 2 := by
  have heq := Determinant.fma_roundFinite_of_decode I ha hb hc hp
  have he := I.format.roundFinite_mixed_error ((a : ℝ) * (b : ℝ) + (c : ℝ))
  rw [← heq] at he
  apply relative_absolute_decomposition I.format.unitRoundoff_pos.le _ he
  unfold FP.IEEE.Format.minSubnormal
  positivity

end DistanceAccuracy.ProjectionRounding

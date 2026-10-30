import DistanceAccuracy.WordProjectionRounding

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds

lemma clamp_infinity (I : Interchange) [I.Valid]
    (hone : value? I (one I) = some 1) (sign : Bool) :
    value? I (clamp01nan I (Datum.infinity sign).encode) = some (if sign then 0 else 1) := by
  have hz := Software.orderedValue_of_toRat (Datum.decode I (zero I)) 0 (zero_value I)
  have ho := Software.orderedValue_of_toRat (Datum.decode I (one I)) 1 hone
  have hzlt : lt I (zero I) (one I) = true := (lt_finite I (zero_value I) hone).mpr (by norm_num)
  have hg : gt I (Datum.infinity sign).encode (zero I) = !sign := by
    simp only [gt, Software.compare, Datum.decode_encode, Software.compareDatum]
    rw [hz]
    cases sign <;> simp [Software.orderedValue, Software.Relation.gt,
      Software.Relation.holds, compareOfLessAndEq, ← WithTop.coe_zero, ← WithTop.coe_one]
  have hl : lt I (Datum.infinity sign).encode (one I) = sign := by
    simp only [lt, Software.compare, Datum.decode_encode, Software.compareDatum]
    rw [ho]
    cases sign <;> simp [Software.orderedValue, Software.Relation.lt,
      Software.Relation.holds, compareOfLessAndEq, ← WithTop.coe_zero, ← WithTop.coe_one]
  cases sign <;> simp [clamp01nan, hg, hl, hzlt, hone, zero_value]

/-- An overflowing finite quotient clamps to the same endpoint as its exact
quotient. Infinity does not create an unaccounted parameter error. -/
theorem overflowing_division_clamp (I : Interchange) [I.Valid]
    {a b : I.Word} {x y : ℚ}
    (hone : value? I (one I) = some 1)
    (ha : value? I a = some x) (hb : value? I b = some y) (hy : y ≠ 0)
    (hlim : (1 : ℝ) < I.format.overflowThreshold)
    (hover : Software.overflowWithMode I.format .nearestEven (x/y) = true) :
    value? I (clamp01nan I (IEEEAlgorithm.div I a b)) = some (max 0 (min 1 (x/y))) := by
  have hdiv := Software.mixedDiv_finite I I I .nearestEven a b x y ha hb hy
  have hov := (Software.overflowWithMode_spec I.format .nearestEven (x/y)).mp hover
  have habs : I.format.overflowThreshold ≤ |((x/y : ℚ) : ℝ)| := by
    exact le_of_not_gt ((Software.overflow_even_real_iff I.format (x/y)).mp hov)
  have hmag : (1 : ℚ) < |x/y| := by
    have h : (1 : ℝ) < |((x/y : ℚ) : ℝ)| := hlim.trans_le habs
    exact_mod_cast h
  change value? I (clamp01nan I (Software.mixedDiv I I I .nearestEven a b).value) = _
  rw [hdiv]
  simp only [Software.roundWithMode, hover, dite_true, Software.overflowResult,
    Software.overflowToInfinity, Bool.true_eq, ite_true]
  rw [clamp_infinity I hone]
  by_cases hn : x/y < 0
  · have hq : x/y ≤ 1 := by linarith
    simp [Software.valueSign, ne_of_lt hn, hn, min_eq_right hq, max_eq_left hn.le]
  · have hq : 1 ≤ x/y := by rw [abs_of_nonneg (le_of_not_gt hn)] at hmag; exact hmag.le
    have hz : x/y ≠ 0 := by linarith
    simp [Software.valueSign, hn, hz, min_eq_left hq]

/-- The clamped negative quotient KKT holds also when the quotient overflows.
Only the denominator's finite positivity is required. -/
theorem clamped_negative_division_optimal_total (I : Interchange) [I.Valid]
    {aw bw : I.Word} {a b t : ℚ} {x : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hap : 0 < a) (hr : I.format.unitRoundoff < 1)
    (hlim : (1 : ℝ) < I.format.overflowThreshold)
    (ht : value? I (clamp01nan I (IEEEAlgorithm.div I (IEEEAlgorithm.neg I bw) aw)) = some t)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ delta zeta : ℝ, |delta| ≤ I.format.unitRoundoff ∧ |zeta| ≤ I.format.minSubnormal/2 ∧
      0 ≤ (((a : ℝ)/(1+delta))*(t : ℝ)+((b : ℝ)-(a : ℝ)/(1+delta)*zeta))*(x-(t : ℝ)) := by
  by_cases hover : Software.overflowWithMode I.format .nearestEven (-b/a) = true
  · have hc := overflowing_division_clamp I hone (Determinant.neg_value I hb) ha (ne_of_gt hap) hlim hover
    rw [ht] at hc
    have htq := Option.some.inj hc
    have htr : (t : ℝ) = max 0 (min 1 (-(b : ℝ)/(a : ℝ))) := by exact_mod_cast htq
    refine ⟨0,0,by simpa using I.format.unitRoundoff_pos.le,?_,?_⟩
    · simp only [abs_zero]
      unfold FP.IEEE.Format.minSubnormal; positivity
    · simp only [add_zero,div_one,mul_zero,sub_zero]
      rw [htr]
      apply clamp_optimal (by exact_mod_cast hap) (by norm_num) hx0 hx1
  · have ho : Software.overflowWithMode I.format .nearestEven (-b/a) = false := Bool.eq_false_iff.mpr hover
    obtain ⟨q,hq,_⟩ := div_exists_error I (Determinant.neg_value I hb) ha (ne_of_gt hap) ho
    exact clamped_negative_division_optimal I hone ha hb hap hr hq ht hx0 hx1

/-- For finite operands and nonzero denominator, clamping a rounded quotient
has a relative/absolute error representation even when division overflows. -/
theorem clamped_division_representation (I : Interchange) [I.Valid]
    {aw bw : I.Word} {a b t : ℚ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b) (hb0 : b ≠ 0)
    (hlim : (1 : ℝ) < I.format.overflowThreshold)
    (ht : value? I (clamp01nan I (IEEEAlgorithm.div I aw bw)) = some t) :
    ∃ delta zeta : ℝ, |delta| ≤ I.format.unitRoundoff ∧ |zeta| ≤ I.format.minSubnormal/2 ∧
      (t : ℝ) = max 0 (min 1 (((a : ℝ)/(b : ℝ))*(1+delta)+zeta)) := by
  by_cases ho : Software.overflowWithMode I.format .nearestEven (a/b) = true
  · have hc := overflowing_division_clamp I hone ha hb hb0 hlim ho
    rw [ht] at hc
    have he := Option.some.inj hc
    refine ⟨0,0,by simpa using I.format.unitRoundoff_pos.le,?_,?_⟩
    · simp only [abs_zero]; unfold FP.IEEE.Format.minSubnormal; positivity
    · simp only [add_zero,mul_one]
      exact_mod_cast he
  · obtain ⟨q,hq,_⟩ := div_exists_error I ha hb hb0 (Bool.eq_false_iff.mpr ho)
    obtain ⟨delta,zeta,he,hd,hz⟩ := word_division_decomposition I ha hb hb0 hq
    have hc := clamp01nan_finite I hone hq
    rw [ht] at hc
    have htc : (t : ℝ) = max 0 (min 1 (q : ℝ)) := by exact_mod_cast Option.some.inj hc
    exact ⟨delta,zeta,hd,hz,by simpa only [he] using htc⟩

/-- Plane-crossing variational condition for the actual divided-and-clamped
word. A zero denominator is harmless: the effective affine function is constant. -/
theorem clamped_affine_division_optimal_total (I : Interchange) [I.Valid]
    {aw bw : I.Word} {a b t : ℚ} {v : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hlim : (1 : ℝ) < I.format.overflowThreshold)
    (ht : value? I (clamp01nan I (IEEEAlgorithm.div I aw bw)) = some t)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ∃ delta zeta : ℝ, |delta| ≤ I.format.unitRoundoff ∧ |zeta| ≤ I.format.minSubnormal/2 ∧
      0 ≤ ((b : ℝ)^2*(t : ℝ)-((a : ℝ)*(1+delta)+(b : ℝ)*zeta)*(b : ℝ))*(v-(t : ℝ)) := by
  by_cases hb0 : b = 0
  · refine ⟨0,0,by simpa using I.format.unitRoundoff_pos.le,?_,?_⟩
    · simp only [abs_zero]; unfold FP.IEEE.Format.minSubnormal; positivity
    · simp [hb0]
  · obtain ⟨delta,zeta,hd,hz,hte⟩ := clamped_division_representation I hone ha hb hb0 hlim ht
    have hbr : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
    have heq : -(-((a : ℝ)*(1+delta)+(b : ℝ)*zeta)*(b : ℝ))/(b : ℝ)^2 =
        ((a : ℝ)/(b : ℝ))*(1+delta)+zeta := by field_simp <;> ring
    have h := clamp_optimal (a := (b : ℝ)^2)
      (b := -((a : ℝ)*(1+delta)+(b : ℝ)*zeta)*(b : ℝ))
      (sq_pos_of_ne_zero hbr) (by norm_num : (0:ℝ) ≤ 1) hv0 hv1
    rw [heq, ← hte] at h
    refine ⟨delta,zeta,hd,hz,?_⟩
    nlinarith only [h]

end DistanceAccuracy.ProjectionRounding

import DistanceAccuracy.IEEEBridge

/-! Finite-value and order facts for the concrete IEEE operations. -/
namespace DistanceAccuracy.OperationBounds
open FP.IEEE FP.IEEE.Interchange
open IEEEAlgorithm IEEEBridge
variable (I : Interchange) [I.Valid]

lemma rat_of_real {w : I.Word} {r : ℝ} (h : I.decode? w = some r) :
    ∃ q : ℚ, value? I w = some q ∧ (q : ℝ) = r := by
  have hd := Datum.toRat?_decode I w
  cases hv : value? I w with
  | none =>
    change (value? I w).map (fun q : ℚ => (q : ℝ)) = I.decode? w at hd
    rw [hv, h] at hd
    contradiction
  | some q =>
    refine ⟨q, rfl, ?_⟩
    have hr := real_decode I hv
    exact Option.some.inj (hr.symm.trans h)

lemma zero_value : value? I (zero I) = some 0 := by
  simp [value?, zero]

lemma one_value_of_representable (hr : I.format.Representable 1)
    (hlim : (1 : ℝ) < I.format.overflowThreshold) : value? I (one I) = some 1 := by
  have h : I.decode? (one I) = some 1 := by
    rw [one, Software.roundWithMode_even_cast]
    norm_num only [Rat.cast_one]
    rw [FP.IEEE.Format.round?, if_pos (by simpa using hlim), I.format.roundFinite_exact hr]
  obtain ⟨q, hq, he⟩ := rat_of_real I h
  have hq1 : q = 1 := by exact_mod_cast he
  simpa [hq1] using hq

omit [I.Valid] in
lemma lt_finite {a b : I.Word} {x y : ℚ}
    (ha : value? I a = some x) (hb : value? I b = some y) :
    lt I a b = true ↔ x < y := by
  simp only [lt, Software.compare, Software.compareDatum_finite _ _ x y ha hb]
  by_cases hxy : x < y
  · simp [Software.Relation.lt, Software.Relation.holds, compareOfLessAndEq, hxy]
  · by_cases he : x = y <;>
      simp [Software.Relation.lt, Software.Relation.holds, compareOfLessAndEq, hxy, he]

omit [I.Valid] in
lemma gt_finite {a b : I.Word} {x y : ℚ}
    (ha : value? I a = some x) (hb : value? I b = some y) :
    gt I a b = true ↔ y < x := by
  simp only [gt, Software.compare, Software.compareDatum_finite _ _ x y ha hb]
  by_cases hxy : x < y
  · simp [Software.Relation.gt, Software.Relation.holds, compareOfLessAndEq, hxy, not_lt.mpr (le_of_lt hxy)]
  · by_cases he : x = y
    · simp [Software.Relation.gt, Software.Relation.holds, compareOfLessAndEq, he]
    · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) (Ne.symm he)
      simp [Software.Relation.gt, Software.Relation.holds, compareOfLessAndEq, hxy, he, hyx]

/-- No prior finiteness assumption on x: infinities and NaNs are excluded by
being strictly between the finite endpoints. -/
lemma finite_between_zero_one {x : I.Word} (hone : value? I (one I) = some 1)
    (hgt : gt I x (zero I) = true) (hlt : lt I x (one I) = true) :
    ∃ t : ℚ, value? I x = some t ∧ 0 < t ∧ t < 1 := by
  have hz := Software.orderedValue_of_toRat (Datum.decode I (zero I)) 0 (zero_value I)
  have ho := Software.orderedValue_of_toRat (Datum.decode I (one I)) 1 hone
  have hgt0 := hgt
  have hlt0 := hlt
  change Software.Relation.gt.holds
    (Software.compareDatum (Datum.decode I x) (Datum.decode I (zero I))) = true at hgt
  change Software.Relation.lt.holds
    (Software.compareDatum (Datum.decode I x) (Datum.decode I (one I))) = true at hlt
  unfold Software.compareDatum at hgt hlt
  rw [hz] at hgt
  rw [ho] at hlt
  have hfinite : ∃ t : ℚ, value? I x = some t := by
    cases hd : Datum.decode I x with
    | zero sign => exact ⟨0, by simp [value?, hd]⟩
    | subnormal sign frac hn =>
      exact ⟨(Datum.decode I x).fields.rationalValue, by simp [value?, hd, Datum.toRat?, Datum.isFinite]⟩
    | normal sign exp frac hn hm =>
      exact ⟨(Datum.decode I x).fields.rationalValue, by simp [value?, hd, Datum.toRat?, Datum.isFinite]⟩
    | infinity sign =>
      cases sign <;>
        simp [hd, Software.orderedValue, Software.Relation.gt, Software.Relation.lt,
          Software.Relation.holds, compareOfLessAndEq] at hgt hlt
      all_goals split_ifs at hgt hlt
    | quietNaN sign frac hn hq =>
      simp [hd, Software.orderedValue, Software.Relation.gt, Software.Relation.holds] at hgt
    | signalingNaN sign frac hn hq =>
      simp [hd, Software.orderedValue, Software.Relation.gt, Software.Relation.holds] at hgt
  obtain ⟨t, ht⟩ := hfinite
  exact ⟨t, ht, (gt_finite I ht (zero_value I)).mp hgt0, (lt_finite I ht hone).mp hlt0⟩

/-- `clamp01nan` always yields a finite parameter in [0,1]. -/
theorem clamp01nan_bounded (hone : value? I (one I) = some 1) (x : I.Word) :
    ∃ t : ℚ, value? I (clamp01nan I x) = some t ∧ 0 ≤ t ∧ t ≤ 1 := by
  by_cases hg : gt I x (zero I) = true
  · by_cases hl : lt I x (one I) = true
    · obtain ⟨t, ht, ht0, ht1⟩ := finite_between_zero_one I hone hg hl
      exact ⟨t, by simpa [clamp01nan, hg, hl] using ht, ht0.le, ht1.le⟩
    · exact ⟨1, by simpa [clamp01nan, hg, hl] using hone, by norm_num, le_rfl⟩
  · have hz : lt I (zero I) (one I) = true := (lt_finite I (zero_value I) hone).mpr (by norm_num)
    exact ⟨0, by simpa [clamp01nan, hg, hz] using zero_value I, le_rfl, by norm_num⟩

lemma one_fp32 : value? fp32 (one fp32) = some 1 := by
  apply one_value_of_representable
  · refine ⟨1, 0, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [fp32, FP.IEEE.binary32, FP.IEEE.Format.precision]
  · norm_num [fp32, FP.IEEE.binary32, FP.IEEE.Format.overflowThreshold]

set_option exponentiation.threshold 2048 in
lemma one_fp64 : value? fp64 (one fp64) = some 1 := by
  apply one_value_of_representable
  · refine ⟨1, 0, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [fp64, FP.IEEE.binary64, FP.IEEE.Format.precision]
  · norm_num [fp64, FP.IEEE.binary64, FP.IEEE.Format.overflowThreshold]

/-- Finite inputs plus an operation-range proof give a finite result and its
local mixed error bound; no result-decoding hypothesis is required. -/
theorem binary_exists_error (op : BinaryOp) {a b : I.Word} {x y : ℚ}
    (ha : value? I a = some x) (hb : value? I b = some y)
    (ho : Software.overflowWithMode I.format .nearestEven (Software.binaryExact op x y) = false) :
    ∃ z : ℚ, value? I (Software.binary I op .nearestEven a b).value = some z ∧
      |(z : ℝ) - (Software.binaryExact op x y : ℝ)| ≤
        I.format.unitRoundoff * |(Software.binaryExact op x y : ℝ)| + I.format.minSubnormal / 2 := by
  obtain ⟨r, hr, he⟩ := Software.binary_even_mixed_error I op a b x y ha hb ho
  obtain ⟨z, hz, hzr⟩ := rat_of_real I hr
  exact ⟨z, hz, by simpa [hzr] using he⟩

theorem fma_exists_error {a b c : I.Word} {x y z : ℚ}
    (ha : value? I a = some x) (hb : value? I b = some y) (hc : value? I c = some z)
    (ho : Software.overflowWithMode I.format .nearestEven (x * y + z) = false) :
    ∃ r : ℚ, value? I (fma I a b c) = some r ∧
      |(r : ℝ) - (x * y + z : ℚ)| ≤
        I.format.unitRoundoff * |((x * y + z : ℚ) : ℝ)| + I.format.minSubnormal / 2 := by
  obtain ⟨v, hv, he⟩ := Software.mixedFma_even_mixed_error I I I I a b c x y z ha hb hc ho
  obtain ⟨r, hr, hrv⟩ := rat_of_real I hv
  exact ⟨r, hr, by simpa [hrv] using he⟩

theorem div_exists_error {a b : I.Word} {x y : ℚ}
    (ha : value? I a = some x) (hb : value? I b = some y) (hy : y ≠ 0)
    (ho : Software.overflowWithMode I.format .nearestEven (x / y) = false) :
    ∃ z : ℚ, value? I (div I a b) = some z ∧
      |(z : ℝ) - (x / y : ℚ)| ≤
        I.format.unitRoundoff * |((x / y : ℚ) : ℝ)| + I.format.minSubnormal / 2 := by
  obtain ⟨r, hr, he⟩ := Software.mixedDiv_even_mixed_error I I I a b x y ha hb hy ho
  obtain ⟨z, hz, hzr⟩ := rat_of_real I hr
  exact ⟨z, hz, by simpa [hzr] using he⟩

omit [I.Valid] in
lemma no_overflow_of_lt (x : ℚ) (h : |(x : ℝ)| < I.format.overflowThreshold) :
    Software.overflowWithMode I.format .nearestEven x = false := by
  cases he : Software.overflowWithMode I.format .nearestEven x with
  | false => rfl
  | true =>
    have ho := (Software.overflowWithMode_spec I.format .nearestEven x).mp he
    exact False.elim (((Software.overflow_even_real_iff I.format x).mp ho) h)

omit [I.Valid] in
lemma not_nan_of_value {w : I.Word} {x : ℚ} (h : value? I w = some x) :
    Software.isNaN I w = false := by
  cases hd : Datum.decode I w <;>
    simp_all [value?, Datum.toRat?, Datum.isFinite, Software.isNaN, Datum.isNaN]

omit [I.Valid] in
/-- The actual NaN-preserving selection is an ordinary minimum when both
candidate squared distances are finite. -/
lemma choose_value {best cand : Candidate I} {a b : ℚ}
    (ha : value? I best.q = some a) (hb : value? I cand.q = some b) :
    value? I (choose I best cand).q = some (min a b) := by
  have hn := not_nan_of_value I hb
  by_cases hlt : b < a
  · have h := (lt_finite I hb ha).mpr hlt
    simpa [choose, h, hn, min_eq_right hlt.le] using hb
  · have h : lt I cand.q best.q ≠ true := by
      intro hc
      exact hlt ((lt_finite I hb ha).mp hc)
    have hc : lt I cand.q best.q = false := Bool.eq_false_iff.mpr h
    simpa [choose, hc, hn, min_eq_left (le_of_not_gt hlt)] using ha

lemma roundFinite_nonneg (F : FP.IEEE.Format) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ F.roundFinite x := by
  have h := F.roundFinite_nearest x 0 F.representable_zero
  rw [zero_sub, abs_neg, abs_of_nonneg hx] at h
  have hlo := (abs_le.mp h).1
  linarith

lemma roundFinite_le_one (F : FP.IEEE.Format) (hone : F.Representable 1)
    {x : ℝ} (hx : x ≤ 1) : F.roundFinite x ≤ 1 := by
  have h := F.roundFinite_nearest x 1 hone
  rw [abs_of_nonneg (sub_nonneg.mpr hx)] at h
  have hhi := (abs_le.mp h).2
  linarith

lemma binary_value_eq_round (op : BinaryOp) {a b : I.Word} {x y z : ℚ}
    (ha : value? I a = some x) (hb : value? I b = some y)
    (hz : value? I (Software.binary I op .nearestEven a b).value = some z)
    (hlim : |(Software.binaryExact op x y : ℝ)| < I.format.overflowThreshold) :
    (z : ℝ) = I.format.roundFinite (Software.binaryExact op x y : ℝ) := by
  have hr := Software.binary_even_cast I op a b x y ha hb
  rw [← Software.binaryExact_cast] at hr
  rw [FP.IEEE.Format.round?, if_pos hlim] at hr
  exact Option.some.inj ((real_decode I hz).symm.trans hr)

/-- Rounded complement is finite and stays inside [0,1], and its error has the
usual mixed bound. No Sterbenz lemma is needed for this weaker estimate. -/
theorem complement_bounded {u : I.Word} {t : ℚ}
    (hone : value? I (one I) = some 1) (hrep : I.format.Representable 1)
    (hlim : (1 : ℝ) < I.format.overflowThreshold)
    (hu : value? I u = some t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ w : ℚ, value? I (sub I (one I) u) = some w ∧ 0 ≤ w ∧ w ≤ 1 ∧
      |(w : ℝ) - (1 - (t : ℝ))| ≤ I.format.unitRoundoff + I.format.minSubnormal / 2 := by
  have ht0r : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht0
  have ht1r : (t : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hsafe : |(Software.binaryExact .sub 1 t : ℝ)| < I.format.overflowThreshold := by
    simp only [Software.binaryExact, Rat.cast_sub, Rat.cast_one]
    rw [abs_of_nonneg (by linarith)]
    linarith
  obtain ⟨w, hw, he⟩ := binary_exists_error I .sub hone hu
    (no_overflow_of_lt I _ hsafe)
  have hwr := binary_value_eq_round I .sub hone hu hw hsafe
  simp only [Software.binaryExact, Rat.cast_sub, Rat.cast_one] at hwr he
  have hn := roundFinite_nonneg I.format (show 0 ≤ 1 - (t : ℝ) by linarith)
  have hh := roundFinite_le_one I.format hrep (show 1 - (t : ℝ) ≤ 1 by linarith)
  have hw0 : (0 : ℝ) ≤ (w : ℝ) := by rw [hwr]; exact hn
  have hw1 : (w : ℝ) ≤ 1 := by rw [hwr]; exact hh
  refine ⟨w, hw, by exact_mod_cast hw0, by exact_mod_cast hw1, ?_⟩
  rw [abs_of_nonneg (by linarith : 0 ≤ 1 - (t : ℝ))] at he
  have hm := mul_nonneg I.format.unitRoundoff_pos.le ht0r
  nlinarith

/-- The triangular cap is finite even when the two parameter solves produce
NaNs or infinities. The only excess over an exact simplex is complement rounding. -/
theorem capped_clamps_bounded (a b : I.Word)
    (hone : value? I (one I) = some 1) (hrep : I.format.Representable 1)
    (hlim : (1 : ℝ) < I.format.overflowThreshold) :
    let u := clamp01nan I a
    let v := clamp01nan I b
    let w := sub I (one I) u
    ∃ s t : ℚ, value? I u = some s ∧
      value? I (if lt I v w then v else w) = some t ∧
      0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧
      (s : ℝ) + (t : ℝ) ≤ 1 + I.format.unitRoundoff + I.format.minSubnormal / 2 := by
  dsimp only
  obtain ⟨s, hs, hs0, hs1⟩ := clamp01nan_bounded I hone a
  obtain ⟨v, hv, hv0, hv1⟩ := clamp01nan_bounded I hone b
  obtain ⟨w, hw, hw0, hw1, he⟩ := complement_bounded I hone hrep hlim hs hs0 hs1
  have hwupper := (abs_le.mp he).2
  by_cases hc : lt I (clamp01nan I b) (sub I (one I) (clamp01nan I a)) = true
  · have hvw := (lt_finite I hv hw).mp hc
    have hvwr : (v : ℝ) ≤ (w : ℝ) := by exact_mod_cast hvw.le
    refine ⟨s, v, hs, by simpa [hc] using hv, hs0, hs1, hv0, hv1, ?_⟩
    linarith
  · refine ⟨s, w, hs, by simpa [hc] using hw, hs0, hs1, hw0, hw1, ?_⟩
    linarith

end DistanceAccuracy.OperationBounds

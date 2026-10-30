import DistanceAccuracy.Projection

namespace DistanceAccuracy.ProjectionRounding

/-- A rounded quotient is an exact minimizer for coefficients obtained by
absorbing its relative and absolute rounding errors. -/
theorem quotient_effective_optimal {ah bh delta zeta q x lo hi : ℝ}
    (ha : 0 < ah) (hd : 0 < 1 + delta)
    (hq : q = (-bh / ah) * (1 + delta) + zeta)
    (hlohi : lo ≤ hi) (hxlo : lo ≤ x) (hxhi : x ≤ hi) :
    0 ≤ ((ah / (1 + delta)) * max lo (min hi q) +
      (bh - ah / (1 + delta) * zeta)) * (x - max lo (min hi q)) := by
  have hae : 0 < ah / (1 + delta) := div_pos ha hd
  have hquot : q = -(bh - ah / (1 + delta) * zeta) / (ah / (1 + delta)) := by
    rw [hq]
    field_simp
    <;> ring
  rw [hquot]
  exact DistanceAccuracy.clamp_optimal hae hlohi hxlo hxhi

/-- Denominator rounding and quotient relative error combine into one
coefficient error, with an explicit 1/(1-rho) amplification. -/
theorem effective_denominator_error {a ah delta rho ea : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ rho) (hr1 : rho < 1)
    (hd : |delta| ≤ rho) (he : |ah - a| ≤ ea) :
    |ah / (1 + delta) - a| ≤ (ea + a * rho) / (1 - rho) := by
  have hdl := (abs_le.mp hd).1
  have hpos : 0 < 1 + delta := by linarith
  have hbase : |ah - a * (1 + delta)| ≤ ea + a * rho := by
    calc
      |ah - a * (1 + delta)| = |(ah - a) - a * delta| := by congr 1; ring
      _ ≤ |ah - a| + |a * delta| := abs_sub _ _
      _ ≤ ea + a * rho := by rw [abs_mul, abs_of_nonneg ha]; gcongr
  have heapos : 0 ≤ ea := le_trans (abs_nonneg _) he
  calc
    |ah / (1 + delta) - a| = |ah - a * (1 + delta)| / (1 + delta) := by
      rw [show ah / (1 + delta) - a = (ah - a * (1 + delta)) / (1 + delta) by field_simp]
      rw [abs_div, abs_of_pos hpos]
    _ ≤ (ea + a * rho) / (1 + delta) := div_le_div_of_nonneg_right hbase hpos.le
    _ ≤ (ea + a * rho) / (1 - rho) := by
      apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- Gradient error for the quotient's effective coefficients, before taking
an absolute-error squared-loss budget. -/
theorem effective_gradient_error {a b ah bh delta rho ea eb t : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ rho) (hr1 : rho < 1)
    (hd : |delta| ≤ rho) (he : |ah - a| ≤ ea)
    (hb : |bh - b| ≤ eb) (ht : 0 ≤ t) :
    |(ah / (1 + delta) - a) * t + (bh - b)| ≤
      ((ea + a * rho) / (1 - rho)) * t + eb := by
  calc
    _ ≤ |(ah / (1 + delta) - a) * t| + |bh - b| := abs_add_le _ _
    _ = |ah / (1 + delta) - a| * t + |bh - b| := by rw [abs_mul, abs_of_nonneg ht]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right
      (effective_denominator_error ha hr hr1 hd he) ht) hb

/-- Explicit relative/absolute gradient split for the squared-loss theorem.
Dot-product underflow and quotient underflow remain in the absolute part. -/
theorem effective_gradient_split {a b ah bh delta zeta t daR daA dbR dbA : ℝ}
    (hd : 1 + delta ≠ 0) (ha : ah - a = daR + daA)
    (hb : bh - b = dbR + dbA) :
    (ah / (1 + delta) - a) * t +
      (bh - ah / (1 + delta) * zeta - b) =
    (((daR - a * delta) / (1 + delta)) * t + dbR) +
      ((daA / (1 + delta)) * t + dbA - ah / (1 + delta) * zeta) := by
  have ha' : ah = a + daR + daA := by linarith
  have hb' : bh = b + dbR + dbA := by linarith
  rw [ha', hb']
  field_simp
  <;> ring

/-- An explicit relative budget for the split above. -/
theorem relative_gradient_bound {a delta rho t daR dbR eA eB : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ rho) (hr1 : rho < 1)
    (hd : |delta| ≤ rho) (hda : |daR| ≤ eA) (hdb : |dbR| ≤ eB)
    (ht : 0 ≤ t) :
    |((daR - a * delta) / (1 + delta)) * t + dbR| ≤
      ((eA + a * rho) / (1 - rho)) * t + eB := by
  have hcoeff := effective_denominator_error (ah := a + daR) ha hr hr1 hd
    (by simpa using hda)
  have hdl := (abs_le.mp hd).1
  have hpos : 0 < 1 + delta := by linarith
  have heq : (a + daR) / (1 + delta) - a =
      (daR - a * delta) / (1 + delta) := by field_simp; ring
  rw [heq] at hcoeff
  calc
    _ ≤ |((daR - a * delta) / (1 + delta)) * t| + |dbR| := abs_add_le _ _
    _ = |(daR - a * delta) / (1 + delta)| * t + |dbR| := by rw [abs_mul, abs_of_nonneg ht]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hcoeff ht) hdb

/-- The non-asymptotic reduced-projection relative envelope is below 7.02.
All constants are checked over the full binary32 unit-roundoff interval. -/
theorem reduced_relative_envelope {rho : ℝ} (hr : 0 ≤ rho)
    (hrmax : rho ≤ 1 / 16777216) :
    (3 * (1 + rho) ^ 2 + (3 * (1 + rho) ^ 2 + 1) / (1 - rho)) *
      (1 + 4 * rho) ≤ (351 / 50 : ℝ) := by
  have hr2 : rho ^ 2 ≤ rho / 16777216 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrmax)]
  have hu : (1 + rho) ^ 2 ≤ (1000001 / 1000000 : ℝ) := by nlinarith
  have hv : 1 / (1 - rho) ≤ (1000001 / 1000000 : ℝ) := by
    apply (div_le_iff₀ (by linarith)).2
    linarith
  have hs : 1 + 4 * rho ≤ (1000001 / 1000000 : ℝ) := by linarith
  have hp : 0 ≤ 1 / (1 - rho) := div_nonneg (by norm_num) (by linarith)
  rw [div_eq_mul_inv, ← one_div]
  calc
    _ ≤ (3 * (1000001 / 1000000 : ℝ) +
        (3 * (1000001 / 1000000 : ℝ) + 1) * (1000001 / 1000000 : ℝ)) *
        (1000001 / 1000000 : ℝ) := by gcongr
    _ ≤ _ := by norm_num

/-- Absolute gradient error from two dot products and quotient underflow.
Its doubled value is the 12eta + 4eta*a squared-loss budget. -/
theorem absolute_gradient_bound {a ae delta rho eta t daA dbA zeta : ℝ}
    (ha : 0 ≤ a) (hae : 0 ≤ ae) (haemax : ae ≤ 4 * a)
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1 / 2) (heta : 0 ≤ eta)
    (hd : |delta| ≤ rho) (hda : |daA| ≤ 2 * eta)
    (hdb : |dbA| ≤ 2 * eta) (hz : |zeta| ≤ eta / 2)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |(daA / (1 + delta)) * t + dbA - ae * zeta| ≤ 6 * eta + 2 * eta * a := by
  have hdl := (abs_le.mp hd).1
  have hpos : 0 < 1 + delta := by linarith
  have hdiv : |daA / (1 + delta)| ≤ 4 * eta := by
    rw [abs_div, abs_of_pos hpos]
    apply (div_le_iff₀ hpos).2
    nlinarith [mul_nonneg heta (show 0 ≤ delta + 1 / 2 by linarith)]
  have htbound : |daA / (1 + delta) * t| ≤ 4 * eta := by
    rw [abs_mul, abs_of_nonneg ht]
    exact (mul_le_mul_of_nonneg_right hdiv ht).trans (by nlinarith)
  have hzbound : |ae * zeta| ≤ 2 * eta * a := by
    rw [abs_mul, abs_of_nonneg hae]
    have hz' := mul_le_mul_of_nonneg_left hz hae
    have ha' := mul_le_mul_of_nonneg_right haemax (show 0 ≤ eta / 2 by positivity)
    nlinarith
  have h1 := abs_sub ((daA / (1 + delta)) * t + dbA) (ae * zeta)
  have h2 := abs_add_le ((daA / (1 + delta)) * t) dbA
  linarith

/-- A mixed error estimate admits separate relative and absolute errors;
this is a proved decomposition, not an additional floating-point assumption. -/
theorem split_mixed_error {e R A : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A)
    (he : |e| ≤ R + A) :
    ∃ er ea : ℝ, e = er + ea ∧ |er| ≤ R ∧ |ea| ≤ A := by
  rcases abs_le.mp he with ⟨hel, her⟩
  by_cases hl : e < -R
  · refine ⟨-R, e + R, by ring, by simp [abs_of_nonneg hR], ?_⟩
    rw [abs_le]
    constructor <;> linarith
  · by_cases hh : R < e
    · refine ⟨R, e - R, by ring, by simp [abs_of_nonneg hR], ?_⟩
      rw [abs_le]
      constructor <;> linarith
    · refine ⟨e, 0, by ring, ?_, by simpa⟩
      rw [abs_le]
      constructor <;> linarith

/-- Turn a mixed rounding bound into the familiar multiplicative-plus-additive
form, including exact arguments equal to zero. -/
theorem relative_absolute_decomposition {q x rho eta : ℝ}
    (hr : 0 ≤ rho) (he : 0 ≤ eta)
    (hq : |q - x| ≤ rho * |x| + eta) :
    ∃ delta zeta : ℝ, q = x * (1 + delta) + zeta ∧
      |delta| ≤ rho ∧ |zeta| ≤ eta := by
  obtain ⟨er, ea, hs, her, hea⟩ := split_mixed_error (mul_nonneg hr (abs_nonneg x)) he hq
  by_cases hx : x = 0
  · subst x
    have hz : er = 0 := by simpa using her
    refine ⟨0, ea, ?_, by simpa, hea⟩
    simp only [hz, sub_zero, zero_add] at hs
    simpa using hs
  · refine ⟨er / x, ea, ?_, ?_, hea⟩
    · have hc : x * (er / x) = er := by field_simp
      nlinarith
    · rw [abs_div]
      apply (div_le_iff₀ (abs_pos.mpr hx)).2
      exact her

end DistanceAccuracy.ProjectionRounding

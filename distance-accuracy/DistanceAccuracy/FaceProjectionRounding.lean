import DistanceAccuracy.ProjectionRounding
import DistanceAccuracy.WeightedDotGeometry

namespace DistanceAccuracy.ProjectionRounding

/-- Exact effective quadratic for the face solver's reciprocal, two products,
and final FMA. Absolute product/FMA rounding is retained explicitly. The
interval is the shortened simplex interval [0,1-v]. -/
theorem face_effective_optimal
    {a b d ia c m q v x di dc dm dq zc zm zq : ℝ}
    (ha : 0 < a) (hi : 0 < 1 + di) (hqpos : 0 < 1 + dq)
    (hia : ia = (1 / a) * (1 + di))
    (hc : c = (b * ia) * (1 + dc) + zc)
    (hm : m = (-d * ia) * (1 + dm) + zm)
    (hq : q = (-v * c + m) * (1 + dq) + zq)
    (hv : v ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 - v) :
    let ae := a / ((1 + di) * (1 + dq))
    let be := d * (1 + dm) + v * b * (1 + dc) -
      ae * ((zm - v * zc) * (1 + dq) + zq)
    0 ≤ (ae * max 0 (min (1 - v) q) + be) *
      (x - max 0 (min (1 - v) q)) := by
  dsimp only
  have hae : 0 < a / ((1 + di) * (1 + dq)) := div_pos ha (mul_pos hi hqpos)
  have heq : q = -(d * (1 + dm) + v * b * (1 + dc) -
      a / ((1 + di) * (1 + dq)) * ((zm - v * zc) * (1 + dq) + zq)) /
      (a / ((1 + di) * (1 + dq))) := by
    rw [hq, hc, hm, hia]
    field_simp
    <;> ring
  rw [heq]
  exact DistanceAccuracy.clamp_optimal hae (by linarith) hx0 hx1

/-- The two multiplicative factors in a face denominator are one effective
factor, with an explicit error budget. -/
lemma two_factor_error {di dq rho : ℝ} (hr : 0 ≤ rho)
    (hi : |di| ≤ rho) (hq : |dq| ≤ rho) :
    |(1 + di) * (1 + dq) - 1| ≤ 2 * rho + rho ^ 2 := by
  have heq : (1 + di) * (1 + dq) - 1 = di + dq + di * dq := by ring
  rw [heq]
  have hsum := abs_add_le (di + dq) (di * dq)
  have hs := abs_add_le di dq
  have hp : |di * dq| ≤ rho ^ 2 := by rw [abs_mul]; nlinarith [mul_le_mul hi hq (abs_nonneg dq) hr]
  linarith

/-- A strict non-asymptotic face gradient envelope, exploiting u+v≤1.
The slightly coarser two-factor denominator estimate still fits 7.22. -/
theorem face_relative_envelope {rho kappa lambda u v : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1 / 16777216)
    (hk : 0 ≤ kappa) (hkmax : kappa ≤ 2161 / 1000)
    (hl : 0 ≤ lambda) (hlmax : lambda ≤ 2042 / 1000)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) :
    (kappa * (1 + rho) ^ 3 + 1) * (1 + v) +
      ((lambda * (1 + rho) ^ 2 + 2 + rho) / (1 - (2 * rho + rho ^ 2))) * u ≤
        (361 / 50 : ℝ) := by
  have hr2 : rho ^ 2 ≤ rho / 16777216 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrmax)]
  have hU : (1 + rho) ^ 2 ≤ (1000001 / 1000000 : ℝ) := by nlinarith
  have hU3 : (1 + rho) ^ 3 ≤ (1000001 / 1000000 : ℝ) := by
    have h3 := mul_le_mul_of_nonneg_left hr2 hr
    nlinarith
  have hkU := mul_le_mul hkmax hU3 (show 0 ≤ (1 + rho) ^ 3 by positivity) (by norm_num : (0 : ℝ) ≤ 2161 / 1000)
  have hlU := mul_le_mul hlmax hU (sq_nonneg (1 + rho)) (by norm_num : (0 : ℝ) ≤ 2042 / 1000)
  have hden : 0 < 1 - (2 * rho + rho ^ 2) := by nlinarith
  have hfirst : kappa * (1 + rho) ^ 3 + 1 ≤ 3162 / 1000 := by nlinarith
  have hsecond : (lambda * (1 + rho) ^ 2 + 2 + rho) / (1 - (2 * rho + rho ^ 2)) ≤ 4044 / 1000 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hfirst (show 0 ≤ 1 + v by linarith)
  have h2 := mul_le_mul_of_nonneg_right hsecond hu
  linarith

/-- Propagate a coefficient perturbation through one rounded product factor. -/
lemma coefficient_product_error {d dd delta rho E : ℝ}
    (hr : 0 ≤ rho) (hdd : |dd| ≤ E) (hd : |delta| ≤ rho) :
    |(d + dd) * (1 + delta) - d| ≤ E * (1 + rho) + |d| * rho := by
  have heq : (d + dd) * (1 + delta) - d = dd * (1 + delta) + d * delta := by ring
  rw [heq]
  have hd1 : |1 + delta| ≤ 1 + rho := by
    have h := abs_add_le (1 : ℝ) delta
    norm_num only [abs_one] at h
    linarith
  calc
    _ ≤ |dd * (1 + delta)| + |d * delta| := abs_add_le _ _
    _ = |dd| * |1 + delta| + |d| * |delta| := by rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add (mul_le_mul hdd hd1 (abs_nonneg _) (le_trans (abs_nonneg _) hdd))
      (mul_le_mul_of_nonneg_left hd (abs_nonneg _))

/-- Relative part of a face numerator: the same estimate applies independently
to its d and b dot products, followed by the two scalar multiplications. -/
lemma face_numerator_relative {d b dd db dm dc rho E S v : ℝ}
    (hr : 0 ≤ rho) (hdd : |dd| ≤ E) (hdb : |db| ≤ E)
    (hd : |d| ≤ S) (hb : |b| ≤ S)
    (hdm : |dm| ≤ rho) (hdc : |dc| ≤ rho) (hv : 0 ≤ v) :
    |(d + dd) * (1 + dm) + v * (b + db) * (1 + dc) - (d + v * b)| ≤
      (E * (1 + rho) + S * rho) * (1 + v) := by
  have heq : (d + dd) * (1 + dm) + v * (b + db) * (1 + dc) - (d + v * b) =
      ((d + dd) * (1 + dm) - d) + v * ((b + db) * (1 + dc) - b) := by ring
  rw [heq]
  have h1 := coefficient_product_error (d := d) hr hdd hdm
  have h2 := coefficient_product_error (d := b) hr hdb hdc
  have hdS := mul_le_mul_of_nonneg_right hd hr
  have hbS := mul_le_mul_of_nonneg_right hb hr
  have h2' : |(b + db) * (1 + dc) - b| ≤ E * (1 + rho) + S * rho := by linarith
  have hsum := abs_add_le ((d + dd) * (1 + dm) - d) (v * ((b + db) * (1 + dc) - b))
  rw [abs_mul, abs_of_nonneg hv] at hsum
  have hvb := mul_le_mul_of_nonneg_left h2' hv
  nlinarith

/-- The face denominator perturbation from its dot error and the reciprocal
and final FMA multiplicative errors. -/
lemma face_denominator_error {a da di dq rho E : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ rho) (hrmax : rho ≤ 1 / 16777216)
    (hda : |da| ≤ E) (hdi : |di| ≤ rho) (hdq : |dq| ≤ rho) :
    |(a + da) / ((1 + di) * (1 + dq)) - a| ≤
      (E + a * (2 * rho + rho ^ 2)) / (1 - (2 * rho + rho ^ 2)) := by
  have hfac := two_factor_error hr hdi hdq
  have hr2 : rho ^ 2 ≤ rho / 16777216 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrmax)]
  have he := effective_denominator_error (ah := a + da) ha
    (show 0 ≤ 2 * rho + rho ^ 2 by positivity)
    (show 2 * rho + rho ^ 2 < 1 by nlinarith) hfac (by simpa using hda)
  simpa only [add_sub_cancel] using he

/-- The complete relative face-gradient estimate from dot-product and scalar
rounding errors. This supplies 7.22 rho A D after taking S=A D. -/
theorem face_relative_gradient {a b d da db dd di dc dm dq rho S kappa lambda u v : ℝ}
    (ha : 0 ≤ a) (haS : a ≤ S) (hS : 0 ≤ S)
    (hbS : |b| ≤ S) (hdS : |d| ≤ S)
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1 / 16777216)
    (hk : 0 ≤ kappa) (hkmax : kappa ≤ 2161 / 1000)
    (hl : 0 ≤ lambda) (hlmax : lambda ≤ 2042 / 1000)
    (hda : |da| ≤ lambda * rho * S * (1 + rho) ^ 2)
    (hdb : |db| ≤ kappa * rho * S * (1 + rho) ^ 2)
    (hdd : |dd| ≤ kappa * rho * S * (1 + rho) ^ 2)
    (hdi : |di| ≤ rho) (hdc : |dc| ≤ rho) (hdm : |dm| ≤ rho) (hdq : |dq| ≤ rho)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) :
    |((a + da) / ((1 + di) * (1 + dq)) - a) * u +
      ((d + dd) * (1 + dm) + v * (b + db) * (1 + dc) - (d + v * b))| ≤
        (361 / 50) * rho * S := by
  have hn := face_numerator_relative hr hdd hdb hdS hbS hdm hdc hv
  have hden := face_denominator_error ha hr hrmax hda hdi hdq
  have hr2 : rho ^ 2 ≤ rho / 16777216 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrmax)]
  have hdpos : 0 < 1 - (2 * rho + rho ^ 2) := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right haS (show 0 ≤ 2 * rho + rho ^ 2 by positivity)
  have hnum : lambda * rho * S * (1 + rho) ^ 2 + a * (2 * rho + rho ^ 2) ≤
      (rho * S) * (lambda * (1 + rho) ^ 2 + 2 + rho) := by nlinarith
  have hd' := div_le_div_of_nonneg_right hnum hdpos.le
  have hdu := mul_le_mul_of_nonneg_right (hden.trans hd') hu
  have henv := face_relative_envelope hr hrmax hk hkmax hl hlmax hu hv huv
  have henv' := mul_le_mul_of_nonneg_left henv (show 0 ≤ rho * S by positivity)
  have hsum := abs_add_le (((a + da) / ((1 + di) * (1 + dq)) - a) * u)
    ((d + dd) * (1 + dm) + v * (b + db) * (1 + dc) - (d + v * b))
  rw [abs_mul, abs_of_nonneg hu] at hsum
  rw [mul_div_assoc] at hdu
  nlinarith

/-- Absolute face-gradient terms fit the 64eta(1+a) squared-loss budget.
The multiplicative factors are bounded by two, and their inverse product by
two; these weak estimates hold comfortably at binary32 precision. -/
theorem face_absolute_gradient {a ae fi fq fm fc eta u v daA dbA ddA zm zc zq : ℝ}
    (ha : 0 ≤ a) (hae : 0 ≤ ae) (hae4 : ae ≤ 4 * a)
    (heta : 0 ≤ eta) (hfiq : |1 / (fi * fq)| ≤ 2)
    (hfm : |fm| ≤ 2) (hfc : |fc| ≤ 2) (hfq : |fq| ≤ 2)
    (hda : |daA| ≤ 2 * eta) (hdb : |dbA| ≤ 2 * eta) (hdd : |ddA| ≤ 2 * eta)
    (hzm : |zm| ≤ eta / 2) (hzc : |zc| ≤ eta / 2) (hzq : |zq| ≤ eta / 2)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    |(daA / (fi * fq)) * u + ddA * fm + v * dbA * fc -
      ae * ((zm - v * zc) * fq + zq)| ≤ 32 * eta * (1 + a) := by
  have hdai : |daA / (fi * fq) * u| ≤ 4 * eta := by
    rw [div_eq_mul_inv, abs_mul, abs_mul, abs_of_nonneg hu, ← one_div]
    have h1 := mul_le_mul hda hfiq (abs_nonneg _) (by positivity : 0 ≤ 2 * eta)
    have h2 := mul_le_mul_of_nonneg_right h1 hu
    nlinarith
  have hddi : |ddA * fm| ≤ 4 * eta := by
    rw [abs_mul]
    nlinarith [mul_le_mul hdd hfm (abs_nonneg _) (show 0 ≤ 2 * eta by positivity)]
  have hdbi : |v * dbA * fc| ≤ 4 * eta := by
    rw [abs_mul, abs_mul, abs_of_nonneg hv]
    have h1 := mul_le_mul hdb hfc (abs_nonneg _) (show 0 ≤ 2 * eta by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 hv
    nlinarith
  have hzci : |v * zc| ≤ eta / 2 := by
    rw [abs_mul, abs_of_nonneg hv]
    have h1 := mul_le_mul_of_nonneg_left hzc hv
    nlinarith
  have hzmi : |zm - v * zc| ≤ eta := by
    have h1 := abs_sub zm (v * zc)
    linarith
  have hzi : |(zm - v * zc) * fq + zq| ≤ (5 / 2) * eta := by
    have h1 := abs_add_le ((zm - v * zc) * fq) zq
    rw [abs_mul] at h1
    have h2 := mul_le_mul hzmi hfq (abs_nonneg _) heta
    linarith
  have hazi : |ae * ((zm - v * zc) * fq + zq)| ≤ 10 * a * eta := by
    rw [abs_mul, abs_of_nonneg hae]
    have h1 := mul_le_mul_of_nonneg_left hzi hae
    have h2 := mul_le_mul_of_nonneg_right hae4 (show 0 ≤ (5 / 2) * eta by positivity)
    nlinarith
  have h1 := abs_add_le (daA / (fi * fq) * u) (ddA * fm)
  have h2 := abs_add_le (daA / (fi * fq) * u + ddA * fm) (v * dbA * fc)
  have h3 := abs_sub (daA / (fi * fq) * u + ddA * fm + v * dbA * fc)
    (ae * ((zm - v * zc) * fq + zq))
  nlinarith [mul_nonneg ha heta]

/-- Exact split connecting the concrete face effective coefficients to the
proved relative and absolute gradient estimates. -/
theorem face_gradient_split
    {a b d ah bh dh di dc dm dq daR daA dbR dbA ddR ddA u v zm zc zq : ℝ}
    (ha : ah - a = daR + daA) (hb : bh - b = dbR + dbA) (hd : dh - d = ddR + ddA) :
    let ae := ah / ((1 + di) * (1 + dq))
    let be := dh * (1 + dm) + v * bh * (1 + dc) -
      ae * ((zm - v * zc) * (1 + dq) + zq)
    (ae - a) * u + (be - (d + v * b)) =
      (((a + daR) / ((1 + di) * (1 + dq)) - a) * u +
        ((d + ddR) * (1 + dm) + v * (b + dbR) * (1 + dc) - (d + v * b))) +
      ((daA / ((1 + di) * (1 + dq))) * u + ddA * (1 + dm) + v * dbA * (1 + dc) -
        ae * ((zm - v * zc) * (1 + dq) + zq)) := by
  have ha' : ah = a + daR + daA := by linarith
  have hb' : bh = b + dbR + dbA := by linarith
  have hd' : dh = d + ddR + ddA := by linarith
  dsimp only
  rw [ha', hb', hd']
  simp only [div_eq_mul_inv]
  ring

/-- Small IEEE relative factors satisfy the weak bounds used by the absolute
face-error lemma. -/
lemma face_factor_bounds {di dq dm dc rho : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1 / 16)
    (hi : |di| ≤ rho) (hq : |dq| ≤ rho) (hm : |dm| ≤ rho) (hc : |dc| ≤ rho) :
    0 < (1 + di) * (1 + dq) ∧ |1 / ((1 + di) * (1 + dq))| ≤ 2 ∧
      |1 + dm| ≤ 2 ∧ |1 + dc| ≤ 2 ∧ |1 + dq| ≤ 2 := by
  have hil := (abs_le.mp hi).1
  have hql := (abs_le.mp hq).1
  have hi0 : (15 / 16 : ℝ) ≤ 1 + di := by linarith
  have hq0 : (15 / 16 : ℝ) ≤ 1 + dq := by linarith
  have hprod := mul_le_mul hi0 hq0 (by norm_num : (0 : ℝ) ≤ 15 / 16)
    (show 0 ≤ 1 + di by linarith)
  have hpos : 0 < (1 + di) * (1 + dq) := by nlinarith
  have hbound {d : ℝ} (hd : |d| ≤ rho) : |1 + d| ≤ 2 := by
    have h := abs_add_le (1 : ℝ) d
    norm_num only [abs_one] at h
    linarith
  refine ⟨hpos, ?_, hbound hm, hbound hc, hbound hq⟩
  rw [abs_of_pos (one_div_pos.mpr hpos)]
  apply (div_le_iff₀ hpos).2
  nlinarith

lemma face_effective_a_bound {a ah di dq : ℝ} (ha : 0 ≤ a) (hah : 0 ≤ ah)
    (herr : |ah - a| ≤ a) (hprod : 0 < (1 + di) * (1 + dq))
    (hinv : |1 / ((1 + di) * (1 + dq))| ≤ 2) :
    0 ≤ ah / ((1 + di) * (1 + dq)) ∧ ah / ((1 + di) * (1 + dq)) ≤ 4 * a := by
  have hahi := (abs_le.mp herr).2
  have hinv' : 1 / ((1 + di) * (1 + dq)) ≤ 2 := le_trans (le_abs_self _) hinv
  refine ⟨div_nonneg hah hprod.le, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hinv' hah
  rw [mul_one_div] at hmul
  linarith

end DistanceAccuracy.ProjectionRounding

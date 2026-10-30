import DistanceAccuracy.FaceStoredNorm

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant

/-- The actual two-FMA segment reconstruction costs (2rho+rho²)D, when the
exact partial and final separation vectors have norm at most D. -/
theorem segment_affine_evaluation (I : Interchange) [I.Valid]
    {sw tw : I.Word} {P Q R : Vec3 I} {s t : ℚ} {p q r : Fin 3 → ℚ} {D : ℝ}
    (hs : value? I sw = some s) (ht : value? I tw = some t)
    (hP : ∀ i, value? I (P i) = some (p i))
    (hQ : ∀ i, value? I (Q i) = some (q i))
    (hR : ∀ i, value? I (R i) = some (r i))
    (hD : 0 ≤ D)
    (hpartial : ‖(t : ℝ) • realVec q + realVec r‖ ≤ D)
    (hfinal : ‖-(s : ℝ) • realVec p + ((t : ℝ) • realVec q + realVec r)‖ ≤ D)
    (hrho : I.format.unitRoundoff ≤ 1 / 16) (heta : I.format.minSubnormal ≤ 1)
    (hlim : 4 * (D + 1) < I.format.overflowThreshold) :
    ∃ out : Fin 3 → ℚ,
      (∀ i, value? I (fma3 I (neg I sw) P (fma3 I tw Q R) i) = some (out i)) ∧
      ‖realVec out - (-(s : ℝ) • realVec p + ((t : ℝ) • realVec q + realVec r))‖ ≤
        (2 * I.format.unitRoundoff + I.format.unitRoundoff ^ 2) * D +
        (2 + I.format.unitRoundoff) * I.format.minSubnormal := by
  have hr := I.format.unitRoundoff_pos.le
  have heta0 : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  obtain ⟨w, hw, hwe⟩ := fma3_finite_norm_error I ht hQ hR (by linarith only [hpartial, hlim, hD])
  have hwD : ‖realVec w - ((t : ℝ) • realVec q + realVec r)‖ ≤
      I.format.unitRoundoff * D + I.format.minSubnormal :=
    hwe.trans (add_le_add (mul_le_mul_of_nonneg_left hpartial hr) (le_refl _))
  let Z := -(s : ℝ) • realVec p + realVec w
  let Z0 := -(s : ℝ) • realVec p + ((t : ℝ) • realVec q + realVec r)
  have hdiff : ‖Z - Z0‖ ≤ I.format.unitRoundoff * D + I.format.minSubnormal := by
    have heq : Z - Z0 = realVec w - ((t : ℝ) • realVec q + realVec r) := by dsimp [Z, Z0]; module
    rw [heq]
    exact hwD
  have hZ : ‖Z‖ ≤ D + I.format.unitRoundoff * D + I.format.minSubnormal := by
    have h := norm_le_norm_add_norm_sub Z0 Z
    rw [norm_sub_rev] at h
    change ‖Z0‖ ≤ D at hfinal
    linarith only [h, hdiff, hfinal]
  have hZlim : ‖Z‖ < I.format.overflowThreshold := by
    have hh := mul_le_mul_of_nonneg_right hrho hD
    linarith only [hZ, hh, heta, hlim, hD]
  obtain ⟨out, hout, houtE⟩ := fma3_finite_norm_error I (neg_value I hs) hP hw
    (by simpa only [Rat.cast_neg] using hZlim)
  refine ⟨out, hout, ?_⟩
  have htri : ‖realVec out - Z0‖ ≤ ‖realVec out - Z‖ + ‖Z - Z0‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (realVec out - Z) (Z - Z0)
  have hscale := mul_le_mul_of_nonneg_left hZ hr
  simp only [Rat.cast_neg] at houtE
  change ‖realVec out - Z‖ ≤ I.format.unitRoundoff * ‖Z‖ + I.format.minSubnormal at houtE
  change ‖realVec out - Z0‖ ≤ _
  nlinarith only [htri, houtE, hscale, hdiff]

lemma segment_stored_error_budget {rho eta D r n q : ℝ}
    (hrho : 0 ≤ rho) (hrhomax : rho ≤ 1 / 16777216)
    (heta : 0 ≤ eta) (hD : 0 ≤ D) (hrD : r ≤ D)
    (hrecon : n ≤ r + (2 * rho + rho ^ 2) * D + (2 + rho) * eta)
    (heval : q ≤ n + (151 / 100) * rho * n + Real.sqrt (2 * eta)) :
    q ≤ r + (353 / 100) * rho * D + 3 * eta + Real.sqrt (2 * eta) := by
  have hr2 : rho ^ 2 ≤ rho / 16777216 := by nlinarith only [mul_nonneg hrho (sub_nonneg.mpr hrhomax)]
  have hcoef : (2 + rho) * (1 + (151 / 100) * rho) + 151 / 100 ≤ (353 / 100 : ℝ) := by
    nlinarith only [hrhomax, hr2]
  have habs : (1 + (151 / 100) * rho) * (2 + rho) ≤ (3 : ℝ) := by
    nlinarith only [hrhomax, hr2]
  have h1 := mul_le_mul_of_nonneg_left hrecon (show 0 ≤ 1 + (151 / 100) * rho by positivity)
  have h2 := mul_le_mul_of_nonneg_left hrD (show 0 ≤ (151 / 100) * rho by positivity)
  have h3 := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hrho hD)
  have h4 := mul_le_mul_of_nonneg_right habs heta
  nlinarith only [heval, h1, h2, h3, h4]

/-- Coordinate subtraction lifted to a normwise mixed bound. -/
theorem vsub_finite_norm_error (I : Interchange) [I.Valid]
    {A B : Vec3 I} {a b : Fin 3 → ℚ}
    (ha : ∀ i, value? I (A i) = some (a i)) (hb : ∀ i, value? I (B i) = some (b i))
    (hlim : ‖realVec a - realVec b‖ < I.format.overflowThreshold) :
    ∃ out : Fin 3 → ℚ, (∀ i, value? I (vsub I A B i) = some (out i)) ∧
      ‖realVec out - (realVec a - realVec b)‖ ≤
        I.format.unitRoundoff * ‖realVec a - realVec b‖ + I.format.minSubnormal := by
  have hcoord (i : Fin 3) : |(a i : ℝ) - (b i : ℝ)| < I.format.overflowThreshold := by
    have h := PiLp.norm_apply_le (realVec a - realVec b) i
    simp only [PiLp.sub_apply, realVec, WithLp.ofLp_toLp, Real.norm_eq_abs] at h
    exact h.trans_lt hlim
  have hex (i : Fin 3) := OperationBounds.binary_exists_error I .sub (ha i) (hb i)
    (OperationBounds.no_overflow_of_lt I _ (by simpa only [FP.IEEE.Software.binaryExact, Rat.cast_sub] using hcoord i))
  choose out hout herr using hex
  refine ⟨out, hout, ?_⟩
  have hr := I.format.unitRoundoff_pos.le
  have heta : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hv := vector_mixed_bound hr (le_refl (0 : ℝ))
    (show 0 ≤ I.format.minSubnormal / 2 by positivity)
    (r := realVec out - (realVec a - realVec b))
    (n := realVec a - realVec b) (p := (0 : E3))
    (by intro i; simpa [realVec, FP.IEEE.Software.binaryExact, Rat.cast_sub] using herr i)
  have hs : Real.sqrt (3 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hm := mul_le_mul_of_nonneg_right hs heta
  simp only [zero_mul, add_zero] at hv
  nlinarith only [hv, hm]

/-- Endpoint reconstruction includes the actual rounded R-P subtraction and
one vector FMA; it has the same evaluation budget as the interior candidate. -/
theorem endpoint_affine_evaluation (I : Interchange) [I.Valid]
    {tw : I.Word} {P Q R : Vec3 I} {t : ℚ} {p q r : Fin 3 → ℚ} {D : ℝ}
    (ht : value? I tw = some t)
    (hP : ∀ i, value? I (P i) = some (p i))
    (hQ : ∀ i, value? I (Q i) = some (q i))
    (hR : ∀ i, value? I (R i) = some (r i))
    (hD : 0 ≤ D) (hpartial : ‖realVec r - realVec p‖ ≤ D)
    (hfinal : ‖(t : ℝ) • realVec q + (realVec r - realVec p)‖ ≤ D)
    (hrho : I.format.unitRoundoff ≤ 1 / 16) (heta : I.format.minSubnormal ≤ 1)
    (hlim : 4 * (D + 1) < I.format.overflowThreshold) :
    ∃ out : Fin 3 → ℚ,
      (∀ i, value? I (fma3 I tw Q (vsub I R P) i) = some (out i)) ∧
      ‖realVec out - ((t : ℝ) • realVec q + (realVec r - realVec p))‖ ≤
        (2 * I.format.unitRoundoff + I.format.unitRoundoff ^ 2) * D +
        (2 + I.format.unitRoundoff) * I.format.minSubnormal := by
  have hr := I.format.unitRoundoff_pos.le
  obtain ⟨w, hw, hwe⟩ := vsub_finite_norm_error I hR hP (by linarith only [hpartial, hlim, hD])
  have hwD : ‖realVec w - (realVec r - realVec p)‖ ≤
      I.format.unitRoundoff * D + I.format.minSubnormal :=
    hwe.trans (add_le_add (mul_le_mul_of_nonneg_left hpartial hr) (le_refl _))
  let Z := (t : ℝ) • realVec q + realVec w
  let Z0 := (t : ℝ) • realVec q + (realVec r - realVec p)
  have hdiff : ‖Z - Z0‖ ≤ I.format.unitRoundoff * D + I.format.minSubnormal := by
    have heq : Z - Z0 = realVec w - (realVec r - realVec p) := by dsimp [Z, Z0]; module
    rw [heq]
    exact hwD
  have hZ : ‖Z‖ ≤ D + I.format.unitRoundoff * D + I.format.minSubnormal := by
    have h := norm_le_norm_add_norm_sub Z0 Z
    rw [norm_sub_rev] at h
    change ‖Z0‖ ≤ D at hfinal
    linarith only [h, hdiff, hfinal]
  have hZlim : ‖Z‖ < I.format.overflowThreshold := by
    have hh := mul_le_mul_of_nonneg_right hrho hD
    linarith only [hZ, hh, heta, hlim, hD]
  obtain ⟨out, hout, houtE⟩ := fma3_finite_norm_error I ht hQ hw hZlim
  refine ⟨out, hout, ?_⟩
  have htri : ‖realVec out - Z0‖ ≤ ‖realVec out - Z‖ + ‖Z - Z0‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (realVec out - Z) (Z - Z0)
  have hscale := mul_le_mul_of_nonneg_left hZ hr
  change ‖realVec out - Z‖ ≤ I.format.unitRoundoff * ‖Z‖ + I.format.minSubnormal at houtE
  change ‖realVec out - Z0‖ ≤ _
  nlinarith only [htri, houtE, hscale, hdiff]

lemma direct_stored_error_budget {rho eta D r n q : ℝ}
    (hrho : 0 ≤ rho) (hrhomax : rho ≤ 1 / 16777216)
    (heta : 0 ≤ eta) (hD : 0 ≤ D) (hrD : r ≤ D)
    (hrecon : n ≤ r + rho * D + eta)
    (heval : q ≤ n + (151 / 100) * rho * n + Real.sqrt (2 * eta)) :
    q ≤ r + (253 / 100) * rho * D + 2 * eta + Real.sqrt (2 * eta) := by
  have hcoef : 1 + (151 / 100) * rho + 151 / 100 ≤ (253 / 100 : ℝ) := by linarith only [hrhomax]
  have habs : 1 + (151 / 100) * rho ≤ (2 : ℝ) := by linarith only [hrhomax]
  have h1 := mul_le_mul_of_nonneg_left hrecon (show 0 ≤ 1 + (151 / 100) * rho by positivity)
  have h2 := mul_le_mul_of_nonneg_left hrD (show 0 ≤ (151 / 100) * rho by positivity)
  have h3 := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hrho hD)
  have h4 := mul_le_mul_of_nonneg_right habs heta
  nlinarith only [heval, h1, h2, h3, h4]

end DistanceAccuracy.ProjectionRounding

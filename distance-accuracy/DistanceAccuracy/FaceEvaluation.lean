import DistanceAccuracy.FaceLocal

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds Determinant

/-- A concrete vector FMA has a normwise mixed error. The exact affine result
range suffices to prove all three output coordinates finite. -/
theorem fma3_finite_norm_error (I : Interchange) [I.Valid]
    {tw : I.Word} {A B : Vec3 I} {t : ℚ} {a b : Fin 3 → ℚ}
    (ht : value? I tw = some t)
    (ha : ∀ i, value? I (A i) = some (a i)) (hb : ∀ i, value? I (B i) = some (b i))
    (hlim : ‖(t : ℝ) • realVec a + realVec b‖ < I.format.overflowThreshold) :
    ∃ out : Fin 3 → ℚ, (∀ i, value? I (fma3 I tw A B i) = some (out i)) ∧
      ‖realVec out - ((t : ℝ) • realVec a + realVec b)‖ ≤
        I.format.unitRoundoff * ‖(t : ℝ) • realVec a + realVec b‖ + I.format.minSubnormal := by
  have hcoord (i : Fin 3) : |(t : ℝ) * (a i : ℝ) + (b i : ℝ)| < I.format.overflowThreshold := by
    have h := PiLp.norm_apply_le ((t : ℝ) • realVec a + realVec b) i
    simp [realVec, Real.norm_eq_abs] at h
    exact h.trans_lt hlim
  have hex (i : Fin 3) := fma_exists_error I ht (ha i) (hb i)
    (no_overflow_of_lt I _ (by simpa only [Rat.cast_add, Rat.cast_mul] using hcoord i))
  choose out hout herr using hex
  refine ⟨out, hout, ?_⟩
  have hr := I.format.unitRoundoff_pos.le
  have heta : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hv := vector_mixed_bound hr (le_refl (0 : ℝ))
    (show 0 ≤ I.format.minSubnormal / 2 by positivity)
    (r := realVec out - ((t : ℝ) • realVec a + realVec b))
    (n := (t : ℝ) • realVec a + realVec b) (p := (0 : E3))
    (by intro i; simpa [realVec, Rat.cast_add, Rat.cast_mul] using herr i)
  have hs : Real.sqrt (3 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hm := mul_le_mul_of_nonneg_right hs heta
  simp only [zero_mul, add_zero] at hv
  nlinarith only [hv, hm]

/-- The actual rounded-complement cap is finite and close to the exact cap. -/
theorem face_cap_decoded (I : Interchange) [I.Valid]
    {uw vw : I.Word} {u v : ℚ}
    (hone : value? I (one I) = some 1) (hrep : I.format.Representable 1)
    (hlim : (1 : ℝ) < I.format.overflowThreshold)
    (hu : value? I uw = some u) (hv : value? I vw = some v)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ∃ vc : ℚ, value? I (if lt I vw (sub I (one I) uw) then vw else sub I (one I) uw) = some vc ∧
      0 ≤ vc ∧ vc ≤ 1 ∧
      |(vc : ℝ) - min (v : ℝ) (1 - (u : ℝ))| ≤ I.format.unitRoundoff + I.format.minSubnormal / 2 := by
  obtain ⟨w, hw, hw0, hw1, he⟩ := complement_bounded I hone hrep hlim hu hu0 hu1
  have hmin : |min (v : ℝ) (w : ℝ) - min (v : ℝ) (1 - (u : ℝ))| ≤
      I.format.unitRoundoff + I.format.minSubnormal / 2 := by
    have h := abs_min_sub_min_le_max (v : ℝ) (w : ℝ) (v : ℝ) (1 - (u : ℝ))
    simp only [sub_self, abs_zero] at h
    rw [max_eq_right (abs_nonneg ((w : ℝ) - (1 - (u : ℝ))))] at h
    exact h.trans he
  by_cases hlt : lt I vw (sub I (one I) uw) = true
  · have hvw := (lt_finite I hv hw).mp hlt
    have hvwr : (v : ℝ) ≤ (w : ℝ) := by exact_mod_cast hvw.le
    refine ⟨v, by simpa [hlt] using hv, hv0, hv1, ?_⟩
    simpa only [min_eq_left hvwr] using hmin
  · have hwv : w ≤ v := by
      by_contra hn
      exact hlt ((lt_finite I hv hw).mpr (lt_of_not_ge hn))
    have hwvr : (w : ℝ) ≤ (v : ℝ) := by exact_mod_cast hwv
    refine ⟨w, by simpa [hlt] using hw, hw0, hw1, ?_⟩
    simpa only [min_eq_right hwvr] using hmin

lemma simplex_residual_norm {R E F : E3} {u v D : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1)
    (hR : ‖R‖ ≤ D) (hE : ‖R + E‖ ≤ D) (hF : ‖R + F‖ ≤ D) :
    ‖R + u • E + v • F‖ ≤ D := by
  have heq : R + u • E + v • F = (1 - u - v) • R + u • (R + E) + v • (R + F) := by module
  rw [heq]
  have h1 := norm_add_le ((1 - u - v) • R + u • (R + E)) (v • (R + F))
  have h2 := norm_add_le ((1 - u - v) • R) (u • (R + E))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu, abs_of_nonneg hv,
    abs_of_nonneg (show 0 ≤ 1 - u - v by linarith)] at h1 h2
  have h3 := mul_le_mul_of_nonneg_left hR (show 0 ≤ 1 - u - v by linarith)
  have h4 := mul_le_mul_of_nonneg_left hE hu
  have h5 := mul_le_mul_of_nonneg_left hF hv
  nlinarith only [h1, h2, h3, h4, h5]

/-- Actual capped two-FMA face reconstruction. Its error is measured against
the exact capped candidate used by KernelCoverage, not against a surrogate
floating-point certificate. -/
theorem face_affine_evaluation (I : Interchange) [I.Valid]
    {uw vw : I.Word} {E F R : Vec3 I} {u v : ℚ} {e f r : Fin 3 → ℚ} {D : ℝ}
    (hone : value? I (one I) = some 1) (hrep : I.format.Representable 1)
    (hlim1 : (1 : ℝ) < I.format.overflowThreshold)
    (hu : value? I uw = some u) (hv : value? I vw = some v)
    (hE : ∀ i, value? I (E i) = some (e i))
    (hF : ∀ i, value? I (F i) = some (f i))
    (hR : ∀ i, value? I (R i) = some (r i))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hD : 0 ≤ D) (hFn : ‖realVec f‖ ≤ D)
    (hRn : ‖realVec r‖ ≤ D) (hRE : ‖realVec r + realVec e‖ ≤ D)
    (hRF : ‖realVec r + realVec f‖ ≤ D)
    (hrho : I.format.unitRoundoff ≤ 1 / 16) (heta1 : I.format.minSubnormal ≤ 1)
    (hlim : 4 * (D + 1) < I.format.overflowThreshold) :
    let vcw := if lt I vw (sub I (one I) uw) then vw else sub I (one I) uw
    ∃ out : Fin 3 → ℚ,
      (∀ i, value? I (fma3 I vcw F (fma3 I uw E R) i) = some (out i)) ∧
      ‖realVec out - (min (v : ℝ) (1 - (u : ℝ)) • realVec f + ((u : ℝ) • realVec e + realVec r))‖ ≤
        (3 * I.format.unitRoundoff + 2 * I.format.unitRoundoff ^ 2) * D +
        I.format.minSubnormal * ((1 + I.format.unitRoundoff) * D / 2 + 2 + I.format.unitRoundoff) := by
  dsimp only
  have hur0 : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu0
  have hur1 : (u : ℝ) ≤ 1 := by exact_mod_cast hu1
  have hvr0 : (0 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv0
  have hvr1 : (v : ℝ) ≤ 1 := by exact_mod_cast hv1
  have hr := I.format.unitRoundoff_pos.le
  have heta0 : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  let vc := min (v : ℝ) (1 - (u : ℝ))
  have hvc0 : 0 ≤ vc := le_min hvr0 (by linarith)
  have hvc1 : (u : ℝ) + vc ≤ 1 := by have := min_le_right (v : ℝ) (1 - (u : ℝ)); dsimp [vc]; linarith
  have hW : ‖(u : ℝ) • realVec e + realVec r‖ ≤ D := by
    have h := simplex_residual_norm (E := realVec e) (F := realVec f) hur0 (le_refl (0 : ℝ))
      (by linarith) hRn hRE hRF
    simpa [add_comm] using h
  have hZ0 : ‖vc • realVec f + ((u : ℝ) • realVec e + realVec r)‖ ≤ D := by
    have h := simplex_residual_norm hur0 hvc0 hvc1 hRn hRE hRF
    convert h using 1 <;> congr 1 <;> module
  obtain ⟨vcq, hcap, hcap0, hcap1, hcape⟩ := face_cap_decoded I hone hrep hlim1 hu hv hu0 hu1 hv0 hv1
  obtain ⟨w, hw, hwe⟩ := fma3_finite_norm_error I hu hE hR (by linarith only [hW, hlim, hD])
  have hwD : ‖realVec w - ((u : ℝ) • realVec e + realVec r)‖ ≤ I.format.unitRoundoff * D + I.format.minSubnormal :=
    hwe.trans (add_le_add (mul_le_mul_of_nonneg_left hW hr) (le_refl _))
  let Z := (vcq : ℝ) • realVec f + realVec w
  let Z0 := vc • realVec f + ((u : ℝ) • realVec e + realVec r)
  have hdiff : ‖Z - Z0‖ ≤ (I.format.unitRoundoff + I.format.minSubnormal / 2) * D +
      I.format.unitRoundoff * D + I.format.minSubnormal := by
    have heq : Z - Z0 = ((vcq : ℝ) - vc) • realVec f +
        (realVec w - ((u : ℝ) • realVec e + realVec r)) := by dsimp [Z, Z0]; module
    rw [heq]
    have h1 := norm_add_le (((vcq : ℝ) - vc) • realVec f)
      (realVec w - ((u : ℝ) • realVec e + realVec r))
    rw [norm_smul, Real.norm_eq_abs] at h1
    have h2 := mul_le_mul hcape hFn (norm_nonneg _) (show 0 ≤ I.format.unitRoundoff + I.format.minSubnormal / 2 by positivity)
    nlinarith only [h1, h2, hwD]
  have hZn : ‖Z‖ ≤ D + (I.format.unitRoundoff + I.format.minSubnormal / 2) * D +
      I.format.unitRoundoff * D + I.format.minSubnormal := by
    have h := norm_le_norm_add_norm_sub Z0 Z
    rw [norm_sub_rev] at h
    change ‖Z0‖ ≤ D at hZ0
    linarith only [h, hdiff, hZ0]
  have hZlim : ‖Z‖ < I.format.overflowThreshold := by
    have h1 := mul_le_mul_of_nonneg_right hrho hD
    have h2 := mul_le_mul_of_nonneg_right heta1 hD
    nlinarith only [hZn, h1, h2, heta1, hlim, hD]
  obtain ⟨out, hout, houtE⟩ := fma3_finite_norm_error I hcap hF hw hZlim
  refine ⟨out, hout, ?_⟩
  have htri : ‖realVec out - Z0‖ ≤ ‖realVec out - Z‖ + ‖Z - Z0‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (realVec out - Z) (Z - Z0)
  have hscale := mul_le_mul_of_nonneg_left hZn hr
  change ‖realVec out - Z‖ ≤ I.format.unitRoundoff * ‖Z‖ + I.format.minSubnormal at houtE
  change ‖realVec out - Z0‖ ≤ _
  nlinarith only [htri, houtE, hscale, hdiff]

def faceV (I : Interchange) [I.Valid] (R E N : Vec3 I) : I.Word :=
  clamp01nan I (IEEEAlgorithm.div I (neg I (dot3 I N (cross3 I E R))) (dot3 I N N))

/-- Identification of the actual face candidate's vector reconstruction. -/
lemma face_r_schedule (I : Interchange) [I.Valid] (R E F N : Vec3 I) :
    (face I R E F N).r =
      let vw := faceV I R E N
      let uw := clamp01nan I (faceRaw I E F R vw)
      let vcw := if lt I vw (sub I (one I) uw) then vw else sub I (one I) uw
      fma3 I vcw F (fma3 I uw E R) := rfl

/-- Reconstruction error for the actual face candidate, expressed using the
exact capped parameters appearing in the coverage theorem. -/
theorem face_candidate_reconstruction (I : Interchange) [I.Valid]
    {E F R N : Vec3 I} {v q : ℚ} {e f r : Fin 3 → ℚ} {D : ℝ}
    (hone : value? I (one I) = some 1) (hrep : I.format.Representable 1)
    (hlim1 : (1 : ℝ) < I.format.overflowThreshold)
    (hE : ∀ i, value? I (E i) = some (e i))
    (hF : ∀ i, value? I (F i) = some (f i))
    (hR : ∀ i, value? I (R i) = some (r i))
    (hv : value? I (faceV I R E N) = some v) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hq : value? I (faceRaw I E F R (faceV I R E N)) = some q)
    (hD : 0 ≤ D) (hFn : ‖realVec f‖ ≤ D)
    (hRn : ‖realVec r‖ ≤ D) (hRE : ‖realVec r + realVec e‖ ≤ D)
    (hRF : ‖realVec r + realVec f‖ ≤ D)
    (hrho : I.format.unitRoundoff ≤ 1 / 16) (heta1 : I.format.minSubnormal ≤ 1)
    (hlim : 4 * (D + 1) < I.format.overflowThreshold) :
    ∃ out : Fin 3 → ℚ, (∀ i, value? I ((face I R E F N).r i) = some (out i)) ∧
      let u := max 0 (min 1 (q : ℝ))
      ‖realVec out - (min (v : ℝ) (1 - u) • realVec f + (u • realVec e + realVec r))‖ ≤
        (3 * I.format.unitRoundoff + 2 * I.format.unitRoundoff ^ 2) * D +
        I.format.minSubnormal * ((1 + I.format.unitRoundoff) * D / 2 + 2 + I.format.unitRoundoff) := by
  have hu := clamp01nan_finite I hone hq
  have hu0 : (0 : ℚ) ≤ max 0 (min 1 q) := le_max_left _ _
  have hu1 : max (0 : ℚ) (min 1 q) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  obtain ⟨out, hout, he⟩ := face_affine_evaluation I hone hrep hlim1 hu hv hE hF hR
    hu0 hu1 hv0 hv1 hD hFn hRn hRE hRF hrho heta1 hlim
  refine ⟨out, ?_, ?_⟩
  · intro i
    rw [face_r_schedule]
    exact hout i
  · simpa only [Rat.cast_max, Rat.cast_min, Rat.cast_zero, Rat.cast_one] using he

end DistanceAccuracy.ProjectionRounding

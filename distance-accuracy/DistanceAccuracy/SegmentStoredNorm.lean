import DistanceAccuracy.SegmentEvaluation

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant

/-- Attach the actual stored squared norm to a proved two-rounding vector
reconstruction bound. -/
theorem two_rounding_stored_score (I : Interchange) [I.Valid]
    {rw : Vec3 I} {out : Fin 3 → ℚ} {target : E3} {D : ℝ}
    (hout : ∀ i, value? I (rw i) = some (out i))
    (hD : 0 ≤ D) (htarget : ‖target‖ ≤ D)
    (hrho : I.format.unitRoundoff ≤ 1 / 16777216) (heta : I.format.minSubnormal ≤ 1)
    (herr : ‖realVec out - target‖ ≤ (2 * I.format.unitRoundoff + I.format.unitRoundoff ^ 2) * D +
      (2 + I.format.unitRoundoff) * I.format.minSubnormal)
    (hlim : 8 * (4 * (D + 1)) * (4 * (D + 1)) + 4 < I.format.overflowThreshold) :
    ∃ score : ℚ, value? I (dot3 I rw rw) = some score ∧ 0 ≤ score ∧
      Real.sqrt (score : ℝ) ≤ ‖target‖ + (353 / 100) * I.format.unitRoundoff * D +
        3 * I.format.minSubnormal + Real.sqrt (2 * I.format.minSubnormal) := by
  have hr := I.format.unitRoundoff_pos.le
  have heta0 : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hn : ‖realVec out‖ ≤ ‖target‖ + (2 * I.format.unitRoundoff + I.format.unitRoundoff ^ 2) * D +
      (2 + I.format.unitRoundoff) * I.format.minSubnormal := by
    have h := norm_le_norm_add_norm_sub target (realVec out)
    rw [norm_sub_rev] at h
    linarith only [h, herr]
  have hc : 2 * I.format.unitRoundoff + I.format.unitRoundoff ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hrho, hr, mul_nonneg hr (sub_nonneg.mpr hrho)]
  have hcD := mul_le_mul_of_nonneg_right hc hD
  have heta3 : (2 + I.format.unitRoundoff) * I.format.minSubnormal ≤ 3 := by
    have h := mul_le_mul (show 2 + I.format.unitRoundoff ≤ 3 by linarith only [hrho]) heta heta0 (by norm_num : (0 : ℝ) ≤ 3)
    linarith only [h]
  have hK : ‖realVec out‖ ≤ 4 * (D + 1) := by linarith only [hn, htarget, hcD, heta3, hD]
  obtain ⟨score, hscore, hscore0, hscoreE⟩ := stored_norm_upper I hout (by positivity) hK
    (by linarith only [hrho]) heta hlim
  exact ⟨score, hscore, hscore0, segment_stored_error_budget hr hrho heta0 hD htarget hn hscoreE⟩

theorem segment_candidate_score (I : Interchange) [I.Valid]
    {sw tw : I.Word} {P Q R : Vec3 I} {s t : ℚ} {p q r : Fin 3 → ℚ} {D : ℝ}
    (hs : value? I sw = some s) (ht : value? I tw = some t)
    (hP : ∀ i, value? I (P i) = some (p i))
    (hQ : ∀ i, value? I (Q i) = some (q i))
    (hR : ∀ i, value? I (R i) = some (r i))
    (hD : 0 ≤ D) (hpartial : ‖(t : ℝ) • realVec q + realVec r‖ ≤ D)
    (hfinal : ‖-(s : ℝ) • realVec p + ((t : ℝ) • realVec q + realVec r)‖ ≤ D)
    (hrho : I.format.unitRoundoff ≤ 1 / 16777216) (heta : I.format.minSubnormal ≤ 1)
    (hlim : 4 * (D + 1) < I.format.overflowThreshold)
    (hqlim : 8 * (4 * (D + 1)) * (4 * (D + 1)) + 4 < I.format.overflowThreshold) :
    let rw := fma3 I (neg I sw) P (fma3 I tw Q R)
    ∃ score : ℚ, value? I (dot3 I rw rw) = some score ∧ 0 ≤ score ∧
      Real.sqrt (score : ℝ) ≤ ‖-(s : ℝ) • realVec p + ((t : ℝ) • realVec q + realVec r)‖ +
        (353 / 100) * I.format.unitRoundoff * D +
        3 * I.format.minSubnormal + Real.sqrt (2 * I.format.minSubnormal) := by
  obtain ⟨out, hout, herr⟩ := segment_affine_evaluation I hs ht hP hQ hR hD hpartial hfinal
    (by linarith only [hrho]) heta hlim
  exact two_rounding_stored_score I hout hD hfinal hrho heta herr hqlim

theorem endpoint_candidate_score (I : Interchange) [I.Valid]
    {tw : I.Word} {P Q R : Vec3 I} {t : ℚ} {p q r : Fin 3 → ℚ} {D : ℝ}
    (ht : value? I tw = some t)
    (hP : ∀ i, value? I (P i) = some (p i))
    (hQ : ∀ i, value? I (Q i) = some (q i))
    (hR : ∀ i, value? I (R i) = some (r i))
    (hD : 0 ≤ D) (hpartial : ‖realVec r - realVec p‖ ≤ D)
    (hfinal : ‖(t : ℝ) • realVec q + (realVec r - realVec p)‖ ≤ D)
    (hrho : I.format.unitRoundoff ≤ 1 / 16777216) (heta : I.format.minSubnormal ≤ 1)
    (hlim : 4 * (D + 1) < I.format.overflowThreshold)
    (hqlim : 8 * (4 * (D + 1)) * (4 * (D + 1)) + 4 < I.format.overflowThreshold) :
    let rw := fma3 I tw Q (vsub I R P)
    ∃ score : ℚ, value? I (dot3 I rw rw) = some score ∧ 0 ≤ score ∧
      Real.sqrt (score : ℝ) ≤ ‖(t : ℝ) • realVec q + (realVec r - realVec p)‖ +
        (353 / 100) * I.format.unitRoundoff * D +
        3 * I.format.minSubnormal + Real.sqrt (2 * I.format.minSubnormal) := by
  obtain ⟨out, hout, herr⟩ := endpoint_affine_evaluation I ht hP hQ hR hD hpartial hfinal
    (by linarith only [hrho]) heta hlim
  exact two_rounding_stored_score I hout hD hfinal hrho heta herr hqlim

/-- One-FMA point/edge or BC candidate, including its stored squared norm. -/
theorem direct_candidate_score (I : Interchange) [I.Valid]
    {tw : I.Word} {E R : Vec3 I} {t : ℚ} {e r : Fin 3 → ℚ} {D : ℝ}
    (ht : value? I tw = some t)
    (hE : ∀ i, value? I (E i) = some (e i))
    (hR : ∀ i, value? I (R i) = some (r i))
    (hD : 0 ≤ D) (hfinal : ‖(t : ℝ) • realVec e + realVec r‖ ≤ D)
    (hrho : I.format.unitRoundoff ≤ 1 / 16777216) (heta : I.format.minSubnormal ≤ 1)
    (hlim : 4 * (D + 1) < I.format.overflowThreshold)
    (hqlim : 8 * (4 * (D + 1)) * (4 * (D + 1)) + 4 < I.format.overflowThreshold) :
    let rw := fma3 I tw E R
    ∃ score : ℚ, value? I (dot3 I rw rw) = some score ∧ 0 ≤ score ∧
      Real.sqrt (score : ℝ) ≤ ‖(t : ℝ) • realVec e + realVec r‖ +
        (253 / 100) * I.format.unitRoundoff * D +
        2 * I.format.minSubnormal + Real.sqrt (2 * I.format.minSubnormal) := by
  have hr := I.format.unitRoundoff_pos.le
  have heta0 : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  obtain ⟨out, hout, herr⟩ := fma3_finite_norm_error I ht hE hR (by linarith only [hfinal, hlim, hD])
  have herrD : ‖realVec out - ((t : ℝ) • realVec e + realVec r)‖ ≤ I.format.unitRoundoff * D + I.format.minSubnormal :=
    herr.trans (add_le_add (mul_le_mul_of_nonneg_left hfinal hr) (le_refl _))
  have hn : ‖realVec out‖ ≤ ‖(t : ℝ) • realVec e + realVec r‖ + I.format.unitRoundoff * D + I.format.minSubnormal := by
    have h := norm_le_norm_add_norm_sub ((t : ℝ) • realVec e + realVec r) (realVec out)
    rw [norm_sub_rev] at h
    linarith only [h, herrD]
  have hK : ‖realVec out‖ ≤ 4 * (D + 1) := by
    have h := mul_le_mul_of_nonneg_right hrho hD
    linarith only [hn, hfinal, h, heta, hD]
  obtain ⟨score, hscore, hscore0, hscoreE⟩ := stored_norm_upper I hout (by positivity) hK
    (by linarith only [hrho]) heta hqlim
  exact ⟨score, hscore, hscore0, direct_stored_error_budget hr hrho heta0 hD hfinal hn hscoreE⟩

end DistanceAccuracy.ProjectionRounding

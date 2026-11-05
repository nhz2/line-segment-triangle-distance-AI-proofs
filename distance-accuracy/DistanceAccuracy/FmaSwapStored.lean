import DistanceAccuracy.ReprojectStored
import DistanceAccuracy.InteriorCandidateUpper
namespace DistanceAccuracy.FmaSwapStored
open DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant
set_option maxHeartbeats 1500000
theorem segment_affine_evaluation_sharp (I : Interchange) [I.Valid]
    {sw tw : I.Word} {P Q R : Vec3 I} {s t : ℚ} {p q r : Fin 3 → ℚ} {D : ℝ}
    (hs : value? I sw = some s) (ht : value? I tw = some t)
    (hP : ∀ i, value? I (P i) = some (p i))
    (hQ : ∀ i, value? I (Q i) = some (q i))
    (hR : ∀ i, value? I (R i) = some (r i))
    (hD : 0 ≤ D)
    (hpartial : ‖-(s : ℝ) • realVec p + realVec r‖ ≤ D)
    (hfinal : ‖(t : ℝ) • realVec q + (-(s : ℝ) • realVec p + realVec r)‖ ≤ D)
    (hrho : I.format.unitRoundoff ≤ 1 / 16) (heta : I.format.minSubnormal ≤ 1)
    (hlim : 4 * (D + 1) < I.format.overflowThreshold) :
    ∃ out : Fin 3 → ℚ,
      (∀ i, value? I (fma3 I tw Q (fma3 I (neg I sw) P R) i) = some (out i)) ∧
      ‖realVec out - ((t : ℝ) • realVec q + (-(s : ℝ) • realVec p + realVec r))‖ ≤
        (I.format.unitRoundoff + I.format.unitRoundoff ^ 2) * D +
        I.format.unitRoundoff * ‖(t : ℝ) • realVec q + (-(s : ℝ) • realVec p + realVec r)‖ +
        (2 + I.format.unitRoundoff) * I.format.minSubnormal := by
  have hr := I.format.unitRoundoff_pos.le
  obtain ⟨w, hw, hwe⟩ := fma3_finite_norm_error I (neg_value I hs) hP hR
    (by simpa only [Rat.cast_neg] using
      (show ‖-(s:ℝ) • realVec p + realVec r‖ < I.format.overflowThreshold by
        linarith only [hpartial, hlim, hD]))
  simp only [Rat.cast_neg] at hwe
  have hwD : ‖realVec w - (-(s : ℝ) • realVec p + realVec r)‖ ≤
      I.format.unitRoundoff * D + I.format.minSubnormal :=
    hwe.trans (add_le_add (mul_le_mul_of_nonneg_left hpartial hr) (le_refl _))
  let Z := (t : ℝ) • realVec q + realVec w
  let Z0 := (t : ℝ) • realVec q + (-(s : ℝ) • realVec p + realVec r)
  have hdiff : ‖Z - Z0‖ ≤ I.format.unitRoundoff * D + I.format.minSubnormal := by
    have heq : Z - Z0 = realVec w - (-(s : ℝ) • realVec p + realVec r) := by dsimp [Z, Z0]; module
    rw [heq]
    exact hwD
  have hZ : ‖Z‖ ≤ ‖Z0‖ + I.format.unitRoundoff * D + I.format.minSubnormal := by
    have h := norm_le_norm_add_norm_sub Z0 Z
    rw [norm_sub_rev] at h
    change ‖Z0‖ ≤ D at hfinal
    linarith only [h, hdiff]
  have hZlim : ‖Z‖ < I.format.overflowThreshold := by
    have hh := mul_le_mul_of_nonneg_right hrho hD
    linarith only [hZ, hh, heta, hlim, hD, hfinal]
  obtain ⟨out, hout, houtE⟩ := fma3_finite_norm_error I ht hQ hw
    hZlim
  refine ⟨out, hout, ?_⟩
  have htri : ‖realVec out - Z0‖ ≤ ‖realVec out - Z‖ + ‖Z - Z0‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (realVec out - Z) (Z - Z0)
  have hscale := mul_le_mul_of_nonneg_left hZ hr
  change ‖realVec out - Z‖ ≤ I.format.unitRoundoff * ‖Z‖ + I.format.minSubnormal at houtE
  change ‖realVec out - Z0‖ ≤ _
  nlinarith only [htri, houtE, hscale, hdiff]
/-- Keep the dependence on the exact residual instead of charging both affine
roundings and the stored norm at the full coordinate scale. -/
theorem segment_candidate_score_sharp (I : Interchange) [I.Valid]
    {sw tw : I.Word} {P Q R : Vec3 I} {s t : ℚ} {p q r : Fin 3 → ℚ} {D : ℝ}
    (hs : value? I sw = some s) (ht : value? I tw = some t)
    (hP : ∀ i, value? I (P i) = some (p i))
    (hQ : ∀ i, value? I (Q i) = some (q i))
    (hR : ∀ i, value? I (R i) = some (r i))
    (hD : 0 ≤ D) (hpartial : ‖-(s:ℝ)•realVec p+realVec r‖ ≤ D)
    (hfinal : ‖(t:ℝ)•realVec q+(-(s:ℝ)•realVec p+realVec r)‖ ≤ D)
    (hrho : I.format.unitRoundoff ≤ 1/16777216) (heta : I.format.minSubnormal ≤ 1)
    (hlim : 4*(D+1) < I.format.overflowThreshold)
    (hqlim : 8*(4*(D+1))*(4*(D+1))+4 < I.format.overflowThreshold) :
    let rw := fma3 I tw Q (fma3 I (neg I sw) P R)
    ∃ score : ℚ, value? I (dot3 I rw rw) = some score ∧ 0 ≤ score ∧
      Real.sqrt (score:ℝ) ≤
        (1+(252/100)*I.format.unitRoundoff)*‖(t:ℝ)•realVec q+(-(s:ℝ)•realVec p+realVec r)‖+
        (1001/1000)*I.format.unitRoundoff*D+3*I.format.minSubnormal+Real.sqrt (2*I.format.minSubnormal) := by
  obtain ⟨out,hout,herr⟩ := segment_affine_evaluation_sharp I hs ht hP hQ hR hD hpartial hfinal
    (by linarith only [hrho]) heta hlim
  let Z := (t:ℝ)•realVec q+(-(s:ℝ)•realVec p+realVec r)
  have hr := I.format.unitRoundoff_pos.le
  have he : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hn : ‖realVec out‖ ≤ ‖Z‖+(I.format.unitRoundoff+I.format.unitRoundoff^2)*D+
      I.format.unitRoundoff*‖Z‖+(2+I.format.unitRoundoff)*I.format.minSubnormal := by
    have h := norm_le_norm_add_norm_sub Z (realVec out)
    rw [norm_sub_rev] at h
    change ‖realVec out-Z‖ ≤ _ at herr
    linarith only [h,herr]
  have hcoef : 2*I.format.unitRoundoff+I.format.unitRoundoff^2 ≤ 1 := by
    nlinarith only [hrho,hr,mul_nonneg hr (sub_nonneg.mpr hrho)]
  have hscale := mul_le_mul_of_nonneg_right hcoef hD
  have hη3 : (2+I.format.unitRoundoff)*I.format.minSubnormal ≤ 3 := by
    have h := mul_le_mul (show 2+I.format.unitRoundoff ≤ 3 by linarith only [hrho]) heta he (by norm_num : (0:ℝ) ≤ 3)
    linarith only [h]
  have hK : ‖realVec out‖ ≤ 4*(D+1) := by
    have h := mul_le_mul_of_nonneg_left hfinal hr
    change ‖Z‖ ≤ D at hfinal
    change I.format.unitRoundoff*‖Z‖ ≤ _ at h
    nlinarith only [hn,hfinal,h,hscale,hη3,hD]
  obtain ⟨score,hscore,hscore0,hscoreE⟩ := stored_norm_upper I hout (by positivity) hK
    (by linarith only [hrho]) heta hqlim
  exact ⟨score,hscore,hscore0,stored_sharp_budget hr hrho he hD (norm_nonneg _) hn hscoreE⟩
end DistanceAccuracy.FmaSwapStored

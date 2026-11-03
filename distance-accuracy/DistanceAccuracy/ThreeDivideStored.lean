import DistanceAccuracy.SegmentStoredNorm
import DistanceAccuracy.InteriorCandidateUpper
namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant
set_option maxHeartbeats 1500000
theorem segment_affine_evaluation_sharp (I : Interchange) [I.Valid]
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
        (I.format.unitRoundoff + I.format.unitRoundoff ^ 2) * D +
        I.format.unitRoundoff * ‖-(s : ℝ) • realVec p + ((t : ℝ) • realVec q + realVec r)‖ +
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
  have hZ : ‖Z‖ ≤ ‖Z0‖ + I.format.unitRoundoff * D + I.format.minSubnormal := by
    have h := norm_le_norm_add_norm_sub Z0 Z
    rw [norm_sub_rev] at h
    change ‖Z0‖ ≤ D at hfinal
    linarith only [h, hdiff]
  have hZlim : ‖Z‖ < I.format.overflowThreshold := by
    have hh := mul_le_mul_of_nonneg_right hrho hD
    linarith only [hZ, hh, heta, hlim, hD, hfinal]
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
lemma stored_sharp_budget {rho eta D n m q : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/16777216) (he : 0 ≤ eta)
    (hD : 0 ≤ D) (hn : 0 ≤ n)
    (hm : m ≤ n+(rho+rho^2)*D+rho*n+(2+rho)*eta)
    (hq : q ≤ m+(151/100)*rho*m+Real.sqrt (2*eta)) :
    q ≤ (1+(252/100)*rho)*n+(1001/1000)*rho*D+3*eta+Real.sqrt (2*eta) := by
  have hr2 : rho^2 ≤ rho/16777216 := by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hrmax)]
  have hc1 : (1+(151/100)*rho)*(1+rho) ≤ 1+(252/100)*rho := by nlinarith only [hr2,hr]
  have hc2 : (1+(151/100)*rho)*(1+rho) ≤ (1001/1000:ℝ) := by nlinarith only [hr2,hrmax]
  have hc3 : (1+(151/100)*rho)*(2+rho) ≤ (3:ℝ) := by nlinarith only [hr2,hrmax]
  have h := mul_le_mul_of_nonneg_left hm (show 0 ≤ 1+(151/100)*rho by positivity)
  have h1 := mul_le_mul_of_nonneg_right hc1 hn
  have h2 := mul_le_mul_of_nonneg_right hc2 (mul_nonneg hr hD)
  have h3 := mul_le_mul_of_nonneg_right hc3 he
  nlinarith only [hq,h,h1,h2,h3]

/-- Keep the dependence on the exact residual instead of charging both affine
roundings and the stored norm at the full coordinate scale. -/
theorem segment_candidate_score_sharp (I : Interchange) [I.Valid]
    {sw tw : I.Word} {P Q R : Vec3 I} {s t : ℚ} {p q r : Fin 3 → ℚ} {D : ℝ}
    (hs : value? I sw = some s) (ht : value? I tw = some t)
    (hP : ∀ i, value? I (P i) = some (p i))
    (hQ : ∀ i, value? I (Q i) = some (q i))
    (hR : ∀ i, value? I (R i) = some (r i))
    (hD : 0 ≤ D) (hpartial : ‖(t:ℝ)•realVec q+realVec r‖ ≤ D)
    (hfinal : ‖-(s:ℝ)•realVec p+((t:ℝ)•realVec q+realVec r)‖ ≤ D)
    (hrho : I.format.unitRoundoff ≤ 1/16777216) (heta : I.format.minSubnormal ≤ 1)
    (hlim : 4*(D+1) < I.format.overflowThreshold)
    (hqlim : 8*(4*(D+1))*(4*(D+1))+4 < I.format.overflowThreshold) :
    let rw := fma3 I (neg I sw) P (fma3 I tw Q R)
    ∃ score : ℚ, value? I (dot3 I rw rw) = some score ∧ 0 ≤ score ∧
      Real.sqrt (score:ℝ) ≤
        (1+(252/100)*I.format.unitRoundoff)*‖-(s:ℝ)•realVec p+((t:ℝ)•realVec q+realVec r)‖+
        (1001/1000)*I.format.unitRoundoff*D+3*I.format.minSubnormal+Real.sqrt (2*I.format.minSubnormal) := by
  obtain ⟨out,hout,herr⟩ := segment_affine_evaluation_sharp I hs ht hP hQ hR hD hpartial hfinal
    (by linarith only [hrho]) heta hlim
  let Z := -(s:ℝ)•realVec p+((t:ℝ)•realVec q+realVec r)
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
end DistanceAccuracy.ProjectionRounding

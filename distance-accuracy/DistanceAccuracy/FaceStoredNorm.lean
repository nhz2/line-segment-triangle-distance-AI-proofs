import DistanceAccuracy.FaceEvaluation
import DistanceAccuracy.NormUpper
import DistanceAccuracy.ReconstructionIEEE

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant

/-- Finite stored squared norm and its sharp upward error, directly from the
actual dot3 words. -/
theorem stored_norm_upper (I : Interchange) [I.Valid]
    {rw : Vec3 I} {r : Fin 3 → ℚ} {K : ℝ}
    (hr : ∀ i, value? I (rw i) = some (r i)) (hK : 0 ≤ K) (hrK : ‖realVec r‖ ≤ K)
    (hrho : I.format.unitRoundoff ≤ 1 / 1024) (heta : I.format.minSubnormal ≤ 1)
    (hlim : 8 * K * K + 4 < I.format.overflowThreshold) :
    ∃ q : ℚ, value? I (dot3 I rw rw) = some q ∧ 0 ≤ q ∧
      Real.sqrt (q : ℝ) ≤ ‖realVec r‖ + (151 / 100) * I.format.unitRoundoff * ‖realVec r‖ +
        Real.sqrt (2 * I.format.minSubnormal) := by
  have hcoord (i : Fin 3) : |(r i : ℝ)| ≤ K := by
    have h := PiLp.norm_apply_le (realVec r) i
    change ‖(r i : ℝ)‖ ≤ ‖realVec r‖ at h
    rw [Real.norm_eq_abs] at h
    exact h.trans hrK
  obtain ⟨q, hq, hq0, he⟩ := ReconstructionIEEE.dot3_self_finite_error I hr hK hcoord hrho heta hlim
  change |(q : ℝ) - scalarDot r r| ≤ _ at he
  rw [scalarDot_self] at he
  have hsum : (r 0 : ℝ) * (r 0 : ℝ) + (r 1 : ℝ) * (r 1 : ℝ) + (r 2 : ℝ) * (r 2 : ℝ) =
      ‖realVec r‖ ^ 2 := scalarDot_self r
  rw [hsum] at he
  have hh := NormUpper.norm_upper I.format.unitRoundoff_pos.le hrho
    (show 0 ≤ I.format.minSubnormal by unfold FP.IEEE.Format.minSubnormal; positivity)
    (norm_nonneg (realVec r)) ((abs_le.mp he).2)
  refine ⟨q, hq, hq0, ?_⟩
  linarith only [hh]

/-- Combining cap/two-FMA reconstruction with stored-norm evaluation costs
at most 4.53rhoD plus the displayed underflow terms. -/
lemma face_stored_error_budget {rho eta D r n q : ℝ}
    (hrho : 0 ≤ rho) (hrhomax : rho ≤ 1 / 16777216)
    (heta : 0 ≤ eta) (hD : 0 ≤ D) (hrD : r ≤ D)
    (hrecon : n ≤ r + (3 * rho + 2 * rho ^ 2) * D + eta * ((1 + rho) * D / 2 + 2 + rho))
    (heval : q ≤ n + (151 / 100) * rho * n + Real.sqrt (2 * eta)) :
    q ≤ r + (453 / 100) * rho * D + 4 * eta * (1 + D) + Real.sqrt (2 * eta) := by
  have hr2 : rho ^ 2 ≤ rho / 16777216 := by nlinarith only [mul_nonneg hrho (sub_nonneg.mpr hrhomax)]
  have hcoeff : (3 + 2 * rho) * (1 + (151 / 100) * rho) + 151 / 100 ≤ (453 / 100 : ℝ) := by
    nlinarith only [hrhomax, hr2]
  have habs0 : (1 + (151 / 100) * rho) * (2 + rho) ≤ (4 : ℝ) := by
    nlinarith only [hrhomax, hr2]
  have habsD : (1 + (151 / 100) * rho) * ((1 + rho) / 2) ≤ (4 : ℝ) := by
    nlinarith only [hrhomax, hr2]
  have h1 := mul_le_mul_of_nonneg_left hrecon (show 0 ≤ 1 + (151 / 100) * rho by positivity)
  have h2 := mul_le_mul_of_nonneg_left hrD (show 0 ≤ (151 / 100) * rho by positivity)
  have h3 := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hrho hD)
  have h4 := mul_le_mul_of_nonneg_right habs0 heta
  have h5 := mul_le_mul_of_nonneg_right habsD (mul_nonneg heta hD)
  nlinarith only [heval, h1, h2, h3, h4, h5]

/-- The actual face candidate score, including both vector evaluation and its
stored squared norm, measured against the exact capped candidate. -/
theorem face_candidate_score (I : Interchange) [I.Valid]
    {E F R N : Vec3 I} {v raw : ℚ} {e f r : Fin 3 → ℚ} {D : ℝ}
    (hone : value? I (one I) = some 1) (hrep : I.format.Representable 1)
    (hlim1 : (1 : ℝ) < I.format.overflowThreshold)
    (hE : ∀ i, value? I (E i) = some (e i))
    (hF : ∀ i, value? I (F i) = some (f i))
    (hR : ∀ i, value? I (R i) = some (r i))
    (hv : value? I (faceV I R E N) = some v) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hq : value? I (faceRaw I E F R (faceV I R E N)) = some raw)
    (hD : 0 ≤ D) (hFn : ‖realVec f‖ ≤ D)
    (hRn : ‖realVec r‖ ≤ D) (hRE : ‖realVec r + realVec e‖ ≤ D)
    (hRF : ‖realVec r + realVec f‖ ≤ D)
    (hrho : I.format.unitRoundoff ≤ 1 / 16777216) (heta1 : I.format.minSubnormal ≤ 1)
    (hlim : 4 * (D + 1) < I.format.overflowThreshold)
    (hqlim : 8 * (4 * (D + 1)) * (4 * (D + 1)) + 4 < I.format.overflowThreshold) :
    ∃ score : ℚ, value? I (face I R E F N).q = some score ∧ 0 ≤ score ∧
      let u := max 0 (min 1 (raw : ℝ))
      Real.sqrt (score : ℝ) ≤
        ‖min (v : ℝ) (1 - u) • realVec f + (u • realVec e + realVec r)‖ +
        (453 / 100) * I.format.unitRoundoff * D +
        4 * I.format.minSubnormal * (1 + D) + Real.sqrt (2 * I.format.minSubnormal) := by
  obtain ⟨out, hout, herr⟩ := face_candidate_reconstruction I hone hrep hlim1 hE hF hR hv hv0 hv1 hq
    hD hFn hRn hRE hRF (by linarith only [hrho]) heta1 hlim
  let u := max 0 (min 1 (raw : ℝ))
  let vc := min (v : ℝ) (1 - u)
  let target := vc • realVec f + (u • realVec e + realVec r)
  have hu0 : 0 ≤ u := le_max_left _ _
  have hu1 : u ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hv0r : (0 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv0
  have hvc0 : 0 ≤ vc := le_min hv0r (by linarith only [hu1])
  have hvc1 : u + vc ≤ 1 := by have := min_le_right (v : ℝ) (1-u); dsimp [vc]; linarith only [this]
  have htarget : ‖target‖ ≤ D := by
    have h := simplex_residual_norm hu0 hvc0 hvc1 hRn hRE hRF
    convert h using 1 <;> congr 1 <;> module
  have hr := I.format.unitRoundoff_pos.le
  have heta0 : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hn : ‖realVec out‖ ≤ ‖target‖ +
      (3 * I.format.unitRoundoff + 2 * I.format.unitRoundoff ^ 2) * D +
      I.format.minSubnormal * ((1 + I.format.unitRoundoff) * D / 2 + 2 + I.format.unitRoundoff) := by
    have h := norm_le_norm_add_norm_sub target (realVec out)
    rw [norm_sub_rev] at h
    change ‖realVec out - target‖ ≤ _ at herr
    linarith only [h, herr]
  have hcoef : 3 * I.format.unitRoundoff + 2 * I.format.unitRoundoff ^ 2 ≤ (1 / 2 : ℝ) := by
    nlinarith only [hrho, hr, mul_nonneg hr (sub_nonneg.mpr hrho)]
  have hcD := mul_le_mul_of_nonneg_right hcoef hD
  have hsub : (1 + I.format.unitRoundoff) * D / 2 + 2 + I.format.unitRoundoff ≤ D + 3 := by
    nlinarith only [hrho, hD, mul_le_mul_of_nonneg_right hrho hD]
  have haeta := mul_le_mul hsub heta1 heta0 (show 0 ≤ D + 3 by linarith only [hD])
  have hnorm : ‖realVec out‖ ≤ 4 * (D + 1) := by nlinarith only [hn, htarget, hcD, haeta, hD]
  obtain ⟨score, hscore, hscore0, heval⟩ := stored_norm_upper I hout (by positivity) hnorm
    (by linarith only [hrho]) heta1 hqlim
  have hqeq : (face I R E F N).q = dot3 I (face I R E F N).r (face I R E F N).r := rfl
  refine ⟨score, by rw [hqeq]; exact hscore, hscore0, ?_⟩
  exact face_stored_error_budget hr hrho heta0 hD htarget hn heval

end DistanceAccuracy.ProjectionRounding

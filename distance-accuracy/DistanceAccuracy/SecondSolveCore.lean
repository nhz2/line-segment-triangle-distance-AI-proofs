import DistanceAccuracy.SecondSolveRounding
import DistanceAccuracy.ReducedProjection

namespace DistanceAccuracy.ProjectionRounding
open Determinant

/-- Squared loss for a second segment projection after the rounded FMA
numerator. Mixed dot errors and scalar factors are composed explicitly. -/
theorem second_squared_loss {P Q R : E3} {D rho eta ah bh dh num delta zeta deltaQ zetaQ s t sstar : ℝ}
    (hP : P ≠ 0) (hD : 0 ≤ D) (hPD : ‖P‖ ≤ D) (hkD : ‖R + t • Q‖ ≤ D)
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1 / 16777216) (heta : 0 ≤ eta)
    (hAh : 0 ≤ ah) (hAerr : |ah - ‖P‖ ^ 2| ≤ ‖P‖ ^ 2)
    (hA : |ah - ‖P‖ ^ 2| ≤ (2042 / 1000) * rho * (‖P‖ * D) * (1 + rho) ^ 2 + 2 * eta)
    (hB : |bh - inner ℝ P Q| ≤ (2161 / 1000) * rho * (‖P‖ * D) * (1 + rho) ^ 2 + 2 * eta)
    (hDdot : |dh - inner ℝ P R| ≤ (2161 / 1000) * rho * (‖P‖ * D) * (1 + rho) ^ 2 + 2 * eta)
    (hd : |delta| ≤ rho) (hz : |zeta| ≤ eta / 2)
    (hdQ : |deltaQ| ≤ rho) (hzQ : |zetaQ| ≤ eta / 2)
    (hnum : num = (t * bh + dh) * (1 + delta) + zeta)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hstar0 : 0 ≤ sstar) (hstar1 : sstar ≤ 1)
    (hKKT : 0 ≤ ((ah / (1 + deltaQ)) * s + (-num - (ah / (1 + deltaQ)) * zetaQ)) * (sstar - s)) :
    ‖(R + t • Q) + s • (-P)‖ ^ 2 ≤ ‖(R + t • Q) + sstar • (-P)‖ ^ 2 +
      ((419 / 50) * rho * D) ^ 2 + 64 * eta * (1 + ‖P‖ ^ 2) := by
  have hnorm := norm_nonneg P
  have hS : 0 ≤ ‖P‖ * D := mul_nonneg hnorm hD
  obtain ⟨daR, daA, haSplit, hdaR, hdaA⟩ := split_mixed_error (by positivity) (by positivity) hA
  obtain ⟨dbR, dbA, hbSplit, hdbR, hdbA⟩ := split_mixed_error (by positivity) (by positivity) hB
  obtain ⟨ddR, ddA, hdSplit, hddR, hddA⟩ := split_mixed_error (by positivity) (by positivity) hDdot
  let B := t * inner ℝ P Q + inner ℝ P R
  let nr := (t * dbR + ddR) * (1 + delta) + B * delta
  let na := (t * dbA + ddA) * (1 + delta) + zeta
  have hBgeo : |B| ≤ ‖P‖ * D := by
    have heq : B = inner ℝ P (R + t • Q) := by simp [B, inner_add_right, inner_smul_right]; ring
    rw [heq]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hkD hnorm)
  have hnrel : |nr| ≤ rho * (‖P‖ * D) * (2 * (2161 / 1000) * (1 + rho) ^ 3 + 1) :=
    second_numerator_relative hr hS ht ht1 hd hBgeo hdbR hddR
  have hnabs : |na| ≤ 5 * eta :=
    second_numerator_absolute hr (by linarith only [hrmax]) heta ht ht1 hd hdbA hddA hz
  have hnSplit : (-num) - (-B) = (-nr) + (-na) := by
    have h := second_numerator_split hbSplit hdSplit hnum
    dsimp [nr, na, B]
    nlinarith only [h]
  have hdQlo := (abs_le.mp hdQ).1
  have hdenpos : 0 < 1 + deltaQ := by linarith only [hdQlo, hrmax]
  let ae := ah / (1 + deltaQ)
  let er := ((daR - ‖P‖ ^ 2 * deltaQ) / (1 + deltaQ)) * s - nr
  let ea := (daA / (1 + deltaQ)) * s - na - ae * zetaQ
  have hsplit : (ae - ‖-P‖ ^ 2) * s + (-num - ae * zetaQ - inner ℝ (-P) (R + t • Q)) = er + ea := by
    have h := effective_gradient_split (t := s) (zeta := zetaQ) hdenpos.ne' haSplit hnSplit
    simpa [ae, er, ea, B, inner_neg_left, inner_add_right, inner_smul_right, add_comm, sub_eq_add_neg] using h
  have hae0 : 0 ≤ ae := div_nonneg hAh hdenpos.le
  have hae4 : ae ≤ 4 * ‖P‖ ^ 2 := by
    apply (div_le_iff₀ hdenpos).2
    have hab := (abs_le.mp hAerr).2
    have hm := mul_le_mul_of_nonneg_right hdQlo (sq_nonneg ‖P‖)
    have hm' := mul_le_mul_of_nonneg_right hrmax (sq_nonneg ‖P‖)
    nlinarith only [hab, hm, hm']
  have hrel0 := relative_gradient_bound (sq_nonneg ‖P‖) hr (show rho < 1 by linarith only [hrmax])
    hdQ hdaR (show |(-nr)| ≤ rho * (‖P‖ * D) * (2 * (2161 / 1000) * (1 + rho) ^ 3 + 1) by simpa using hnrel) hs
  have haS : ‖P‖ ^ 2 ≤ ‖P‖ * D := by nlinarith only [mul_nonneg hnorm (sub_nonneg.mpr hPD)]
  have hcoefpos : 0 ≤ ((2042 / 1000) * (1 + rho) ^ 2 + 1) / (1 - rho) := by
    apply div_nonneg (by positivity) (by linarith only [hrmax])
  have hdenbound : ((2042 / 1000) * rho * (‖P‖ * D) * (1 + rho) ^ 2 + ‖P‖ ^ 2 * rho) / (1 - rho) ≤
      rho * (‖P‖ * D) * (((2042 / 1000) * (1 + rho) ^ 2 + 1) / (1 - rho)) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by linarith only [hrmax])
    nlinarith only [mul_le_mul_of_nonneg_right haS hr]
  have hdenS := mul_le_mul_of_nonneg_right hdenbound hs
  have hdenS1 := mul_le_mul_of_nonneg_right hs1 (show 0 ≤ rho * (‖P‖ * D) *
      (((2042 / 1000) * (1 + rho) ^ 2 + 1) / (1 - rho)) by positivity)
  have henv := mul_le_mul_of_nonneg_right (second_relative_envelope hr hrmax) (mul_nonneg hr hS)
  have her : |er| ≤ ‖-P‖ * ((419 / 50) * rho * D) := by
    dsimp [er]
    rw [norm_neg]
    simp only [← sub_eq_add_neg] at hrel0
    nlinarith only [hrel0, hdenS, hdenS1, henv]
  have hea0 := absolute_gradient_bound (a := ‖P‖ ^ 2) (sq_nonneg _) hae0 hae4 hr
    (show rho ≤ 1 / 2 by linarith only [hrmax]) (show 0 ≤ (5 / 2) * eta by positivity) hdQ
    (show |daA| ≤ 2 * ((5 / 2) * eta) by nlinarith only [hdaA, heta])
    (show |(-na)| ≤ 2 * ((5 / 2) * eta) by rw [abs_neg]; nlinarith only [hnabs])
    (show |zetaQ| ≤ ((5 / 2) * eta) / 2 by nlinarith only [hzQ, heta]) hs hs1
  have hea : |ea| ≤ 32 * eta * (1 + ‖P‖ ^ 2) := by
    dsimp [ea]
    simp only [← sub_eq_add_neg] at hea0
    nlinarith only [hea0, heta, mul_nonneg heta (sq_nonneg ‖P‖)]
  have hspan : |s - sstar| ≤ 1 := abs_le.mpr ⟨by linarith only [hs, hstar1], by linarith only [hs1, hstar0]⟩
  have hres := ReducedProjection.projected_residual_sq_le (k := R + t • Q) (n := -P)
    (neg_ne_zero.mpr hP) hKKT hsplit hspan (show 0 ≤ (419 / 50) * rho * D by positivity)
    (show 0 ≤ 32 * eta * (1 + ‖P‖ ^ 2) by positivity) her hea
  nlinarith only [hres]

end DistanceAccuracy.ProjectionRounding

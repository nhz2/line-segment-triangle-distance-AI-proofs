import DistanceAccuracy.ThreeDivideCoverage
import DistanceAccuracy.Constants
namespace DistanceAccuracy
set_option maxHeartbeats 1500000

noncomputable def G (z : ℝ) : ℝ := hypot (F z) 8.38

lemma F_lower_thirteen {z : ℝ} (hz : 0 ≤ z) : (13:ℝ) ≤ F z := by
  have hj : (10:ℝ) ≤ J 3.17 z := by
    have h := hypot_sq (z+3.17) 7.02
    have h0 := hypot_nonneg (z+3.17) 7.02
    dsimp [J]
    nlinarith [sq_nonneg (z+3.17)]
  have hf := hypot_sq (J 3.17 z) 8.38
  have hf0 := F_nonneg z
  change (13:ℝ) ≤ hypot (J 3.17 z) 8.38
  change 0 ≤ hypot (J 3.17 z) 8.38 at hf0
  nlinarith only [hj,hf,hf0]

lemma G_minus_F {z : ℝ} (hz : 0 ≤ z) : G z ≤ F z+2.5 := by
  apply hypot_le (by have := F_nonneg z; positivity)
  have := F_lower_thirteen hz
  nlinarith

lemma F_ge_input {z : ℝ} (hz : 0 ≤ z) : z ≤ F z := by
  have h1 := le_hypot (z+3.17) 7.02
  have h2 := le_hypot (J 3.17 z) 8.38
  dsimp [F,J] at *
  linarith

lemma G_minus_F_large {z : ℝ} (hz : 4096 ≤ z) : G z ≤ F z+0.01 := by
  apply hypot_le (by have := F_nonneg z; positivity)
  have := F_ge_input (show 0 ≤ z by linarith)
  nlinarith

lemma G_small {z : ℝ} (hz : 0 ≤ z) (hzmax : z ≤ 4096) : G z ≤ 4120 := by
  have hj : J 3.17 0 ≤ (11:ℝ) := by
    have h : hypot (0+3.17) 7.02 ≤ (7.83:ℝ) := hypot_le (by norm_num) (by norm_num)
    dsimp [J]; linarith
  have hf0 : F 0 ≤ (14:ℝ) := hypot_le_of_le (J_nonneg (by norm_num)) hj (by norm_num) (by norm_num)
  have hf := F_le_at_zero hz
  exact hypot_le_of_le (F_nonneg z) (show F z ≤ (4110:ℝ) by linarith)
    (by norm_num) (by norm_num)

/-- The extra projection fits the SAME segment envelope as the old kernel.
At small distances sharp reconstruction recovers its cost; at large distances
its additional squared loss is less than 0.01 rho D. -/
theorem three_score_envelope {rho D d h e n score : ℝ}
    (hr : 0 < rho) (hrmax : rho ≤ 1/16777216) (hD : 0 < D)
    (hd : 0 ≤ d) (hh : 0 ≤ h) (he : 0 ≤ e) (hn : 0 ≤ n) (hnD : n ≤ D)
    (habs : 100*Real.sqrt e*(1+D)+6*e+2*Real.sqrt (2*e) ≤ h+(1/1000)*rho*D)
    (hraw : n ≤ (rho*D)*G (d/(rho*D))+4*h+40*Real.sqrt e*(1+D)+(3/1000000)*rho*D)
    (hscore : score ≤ (1+(252/100)*rho)*n+(1001/1000)*rho*D+3*e+Real.sqrt (2*e)) :
    score ≤ (rho*D)*F (d/(rho*D))+3.55*rho*D+6*h := by
  let S := rho*D
  let z := d/S
  have hS : 0 < S := mul_pos hr hD
  have hz : 0 ≤ z := div_nonneg hd hS.le
  have hroot := Real.sqrt_nonneg e
  have hroot2 := Real.sqrt_nonneg (2*e)
  have hrootD : 0 ≤ Real.sqrt e*(1+D) := mul_nonneg hroot (by linarith)
  have hraw : n ≤ S*G z+4*h+40*Real.sqrt e*(1+D)+(3/1000000)*S := by simpa only [S,z,mul_assoc] using hraw
  have hscore : score ≤ (1+(252/100)*rho)*n+(1001/1000)*S+3*e+Real.sqrt (2*e) := by simpa only [S,mul_assoc] using hscore
  have habs : 100*Real.sqrt e*(1+D)+6*e+2*Real.sqrt (2*e) ≤ h+(1/1000)*S := by simpa only [S,mul_assoc] using habs
  suffices hout : score ≤ S*F z+3.55*S+6*h by simpa only [S,z,mul_assoc] using hout
  by_cases hzsmall : z ≤ 4096
  · have hg := G_small hz hzsmall
    have hgf := G_minus_F hz
    have hfactor : 1+(252/100)*rho ≤ 2 := by linarith
    have hfactorH : 4*(1+(252/100)*rho) ≤ (4.01:ℝ) := by linarith
    have hscaleH := mul_le_mul_of_nonneg_right hfactorH hh
    have hscaleE := mul_le_mul_of_nonneg_right hfactor hrootD
    have hscaleS := mul_le_mul_of_nonneg_right hfactor hS.le
    have hgρ : (252/100)*rho*G z ≤ (1/1000:ℝ) := by
      have h := mul_le_mul_of_nonneg_left hg (show 0 ≤ (252/100)*rho by positivity)
      nlinarith only [h,hrmax]
    have hgs := mul_le_mul_of_nonneg_right hgρ hS.le
    have hfs := mul_le_mul_of_nonneg_left hgf hS.le
    have h := mul_le_mul_of_nonneg_left hraw (show 0 ≤ 1+(252/100)*rho by positivity)
    nlinarith only [hscore,h,hscaleH,hscaleE,hscaleS,hgs,hfs,habs,hrootD,he,hroot2,hh,hS.le]
  · have hgf := G_minus_F_large (le_of_not_ge hzsmall)
    have hfs := mul_le_mul_of_nonneg_left hgf hS.le
    have h := mul_le_mul_of_nonneg_left hnD (show 0 ≤ (252/100)*rho by positivity)
    have h : (252/100)*rho*n ≤ (252/100)*S := by simpa only [S,mul_assoc] using h
    nlinarith only [hscore,h,hraw,hfs,habs,hrootD,he,hroot2,hh,hS.le]
end DistanceAccuracy

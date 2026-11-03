import DistanceAccuracy.ReprojectEnvelope
import DistanceAccuracy.InvMultiplyAdmissible
import DistanceAccuracy.EnvelopeBudget
namespace DistanceAccuracy
set_option maxHeartbeats 2000000
noncomputable def FI (z : ℝ) : ℝ := max (F z) 20
noncomputable def F9 (z : ℝ) : ℝ := hypot (J 3.17 z) 9.38
noncomputable def GI (z : ℝ) : ℝ := hypot (F9 z) 9.38
lemma FI_nonneg (z : ℝ) : 0 ≤ FI z := (F_nonneg z).trans (le_max_left _ _)
lemma FI_ge_F (z : ℝ) : F z ≤ FI z := le_max_left _ _
lemma FI_ge_twenty (z : ℝ) : (20:ℝ) ≤ FI z := le_max_right _ _
lemma FI_eq_F {z : ℝ} (hz : 20 ≤ z) : FI z = F z :=
  max_eq_left (hz.trans (F_ge_input (by linarith)))
lemma FI_mono {z w : ℝ} (hz : 0 ≤ z) (hzw : z ≤ w) : FI z ≤ FI w :=
  max_le_max_right _ (F_mono hz hzw)
lemma FI_add_le {z t : ℝ} (hz : 0 ≤ z) (ht : 0 ≤ t) : FI (z+t) ≤ FI z+t := by
  apply max_le
  · exact (F_add_le hz ht).trans (by have := FI_ge_F z; linarith)
  · have := FI_ge_twenty z; linarith
lemma scaled_FI_bound {S d b e : ℝ} (hS : 0 < S) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (he : 0 ≤ e) (hbound : d ≤ S*b+e) : S*FI (d/S) ≤ S*FI b+e := by
  have hn : d/S ≤ b+e/S := by
    apply (div_le_iff₀ hS).mpr
    rw [add_mul, div_mul_cancel₀ e (ne_of_gt hS), mul_comm b S]
    exact hbound
  have hm := FI_mono (div_nonneg hd hS.le) hn
  have ha := FI_add_le hb (div_nonneg he hS.le)
  have ht := mul_le_mul_of_nonneg_left (hm.trans ha) hS.le
  have hid : S*(e/S)=e := mul_div_cancel₀ e (ne_of_gt hS)
  nlinarith only [ht,hid]
lemma F9_nonneg (z : ℝ) : 0 ≤ F9 z := hypot_nonneg _ _
lemma F9_ge_input {z : ℝ} (hz : 0 ≤ z) : z ≤ F9 z := by
  have h1 := le_hypot (z+3.17) 7.02
  have h2 := le_hypot (J 3.17 z) 9.38
  dsimp [F9,J] at *; linarith
lemma GI_sq (z : ℝ) : (GI z)^2 = (F z)^2+(105.7444:ℝ) := by
  have h1 := hypot_sq (J 3.17 z) 8.38
  have h2 := hypot_sq (J 3.17 z) 9.38
  have h3 := hypot_sq (F9 z) 9.38
  dsimp [GI,F9,F] at *; nlinarith only [h1,h2,h3]
lemma GI_minus_FI {z : ℝ} (hz : 0 ≤ z) : GI z ≤ FI z+2.5 := by
  have h := GI_sq z
  have hF := FI_ge_F z
  have h20 := FI_ge_twenty z
  have hs := (sq_le_sq₀ (F_nonneg z) (FI_nonneg z)).2 hF
  have hp : 0 ≤ GI z := hypot_nonneg _ _
  nlinarith
lemma GI_minus_FI_large {z : ℝ} (hz : 4096 ≤ z) : GI z ≤ FI z+0.02 := by
  have h := GI_sq z
  have hf := F_ge_input (show 0 ≤ z by linarith)
  have hm := FI_ge_F z
  have hp : 0 ≤ GI z := hypot_nonneg _ _
  have hF := F_nonneg z
  have hs := (sq_le_sq₀ hF (FI_nonneg z)).2 hm
  nlinarith
lemma GI_small {z : ℝ} (hz : 0 ≤ z) (hzmax : z ≤ 4096) : GI z ≤ 4120 := by
  have hj : J 3.17 0 ≤ (11:ℝ) := by
    have h : hypot (0+3.17) 7.02 ≤ (7.83:ℝ) := hypot_le (by norm_num) (by norm_num)
    dsimp [J]; linarith
  have hf0 : F 0 ≤ (14:ℝ) := hypot_le_of_le (J_nonneg (by norm_num)) hj (by norm_num) (by norm_num)
  have hf := F_le_at_zero hz
  have hs := GI_sq z
  have hF := F_nonneg z
  have hm : (F z)^2 ≤ (4110:ℝ)^2 := (sq_le_sq₀ hF (by norm_num)).2 (by linarith)
  have hg : 0 ≤ GI z := hypot_nonneg _ _
  nlinarith
theorem inv_score_envelope {rho D d h e n score : ℝ}
    (hr : 0 < rho) (hrmax : rho ≤ 1/16777216) (hD : 0 < D)
    (hd : 0 ≤ d) (hh : 0 ≤ h) (he : 0 ≤ e) (hn : 0 ≤ n) (hnD : n ≤ D)
    (habs : 100*Real.sqrt e*(1+D)+6*e+2*Real.sqrt (2*e) ≤ h+(1/1000)*rho*D)
    (hraw : n ≤ (rho*D)*GI (d/(rho*D))+4*h+40*Real.sqrt e*(1+D)+(3/1000000)*rho*D)
    (hscore : score ≤ (1+(252/100)*rho)*n+(1001/1000)*rho*D+3*e+Real.sqrt (2*e)) :
    score ≤ (rho*D)*FI (d/(rho*D))+3.55*rho*D+6*h := by
  let S := rho*D
  let z := d/S
  have hS : 0 < S := mul_pos hr hD
  have hz : 0 ≤ z := div_nonneg hd hS.le
  have hroot := Real.sqrt_nonneg e
  have hroot2 := Real.sqrt_nonneg (2*e)
  have hrootD : 0 ≤ Real.sqrt e*(1+D) := mul_nonneg hroot (by linarith)
  have hraw : n ≤ S*GI z+4*h+40*Real.sqrt e*(1+D)+(3/1000000)*S := by simpa only [S,z,mul_assoc] using hraw
  have hscore : score ≤ (1+(252/100)*rho)*n+(1001/1000)*S+3*e+Real.sqrt (2*e) := by simpa only [S,mul_assoc] using hscore
  have habs : 100*Real.sqrt e*(1+D)+6*e+2*Real.sqrt (2*e) ≤ h+(1/1000)*S := by simpa only [S,mul_assoc] using habs
  suffices hout : score ≤ S*FI z+3.55*S+6*h by simpa only [S,z,mul_assoc] using hout
  by_cases hzsmall : z ≤ 4096
  · have hg := GI_small hz hzsmall
    have hgf := GI_minus_FI hz
    have hfactor : 1+(252/100)*rho ≤ 2 := by linarith
    have hfactorH : 4*(1+(252/100)*rho) ≤ (4.01:ℝ) := by linarith
    have hscaleH := mul_le_mul_of_nonneg_right hfactorH hh
    have hscaleE := mul_le_mul_of_nonneg_right hfactor hrootD
    have hscaleS := mul_le_mul_of_nonneg_right hfactor hS.le
    have hgρ : (252/100)*rho*GI z ≤ (1/1000:ℝ) := by
      have h := mul_le_mul_of_nonneg_left hg (show 0 ≤ (252/100)*rho by positivity)
      nlinarith only [h,hrmax]
    have hgs := mul_le_mul_of_nonneg_right hgρ hS.le
    have hfs := mul_le_mul_of_nonneg_left hgf hS.le
    have h := mul_le_mul_of_nonneg_left hraw (show 0 ≤ 1+(252/100)*rho by positivity)
    nlinarith only [hscore,h,hscaleH,hscaleE,hscaleS,hgs,hfs,habs,hrootD,he,hroot2,hh,hS.le]
  · have hgf := GI_minus_FI_large (le_of_not_ge hzsmall)
    have hfs := mul_le_mul_of_nonneg_left hgf hS.le
    have h := mul_le_mul_of_nonneg_left hnD (show 0 ≤ (252/100)*rho by positivity)
    have h : (252/100)*rho*n ≤ (252/100)*S := by simpa only [S,mul_assoc] using h
    nlinarith only [hscore,h,hraw,hfs,habs,hrootD,he,hroot2,hh,hS.le]

lemma inv_projection_norm_budget {rho eta D A n b : ℝ}
    (hr : 0 ≤ rho) (he : 0 ≤ eta) (hD : 0 ≤ D) (hA : 0 ≤ A) (hAD : A ≤ D) (hn : 0 ≤ n)
    (h : n^2 ≤ b^2+((469/50)*rho*D)^2+64*eta*(1+A^2)) :
    n ≤ hypot b ((469/50)*rho*D)+8*Real.sqrt eta*(1+D) := by
  have hh := hypot_sq b ((469/50)*rho*D)
  have hh0 := hypot_nonneg b ((469/50)*rho*D)
  have heS := Real.sq_sqrt he
  have hADsq : A^2 ≤ D^2 := (sq_le_sq₀ hA hD).2 hAD
  have hmul := mul_le_mul_of_nonneg_left hADsq (show 0 ≤ 64*eta by positivity)
  have heD := mul_nonneg he hD
  have hn0 : 0 ≤ 8*Real.sqrt eta*(1+D) := by positivity
  have hs : n^2 ≤ (hypot b ((469/50)*rho*D))^2+(8*Real.sqrt eta*(1+D))^2 := by
    nlinarith
  nlinarith [mul_nonneg hh0 hn0]


end DistanceAccuracy

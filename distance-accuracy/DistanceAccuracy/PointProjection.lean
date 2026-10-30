import DistanceAccuracy.WordProjectionRounding
import DistanceAccuracy.ReducedProjection

namespace DistanceAccuracy.PointProjection
open FP.IEEE FP.IEEE.Interchange
open IEEEAlgorithm IEEEBridge ProjectionRounding
open DistanceAccuracy.Geometry

/-- A small direction makes every feasible parameter nearly optimal, including
parameters produced from zero, infinite, or NaN quotients. -/
theorem short_direction {p n : E3} {t v eta : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (heta : 0 ≤ eta) (hn : ‖n‖^2 ≤ 4*eta) :
    ‖p+t • n‖ ≤ ‖p+v • n‖+2*Real.sqrt eta := by
  have he : p+t • n = (p+v • n)+(t-v) • n := by module
  have hspan : |t-v| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hs : ‖n‖ ≤ 2*Real.sqrt eta := by
    nlinarith [Real.sq_sqrt heta,Real.sqrt_nonneg eta,norm_nonneg n]
  rw [he]
  calc
    ‖(p+v • n)+(t-v) • n‖ ≤ ‖p+v • n‖+‖(t-v) • n‖ := norm_add_le _ _
    _ ≤ ‖p+v • n‖+2*Real.sqrt eta := by
      rw [norm_smul,Real.norm_eq_abs]
      nlinarith [norm_nonneg n]

/-- IEEE finite-quotient solve: the dot errors and quotient rounding yield a
squared residual loss. The denominator is large enough that its absolute
rounding error can be separated without division by a tiny direction norm. -/
theorem finite_word_projection_loss (I : Interchange) [I.Valid]
    {aw bw : I.Word} {a b q t : ℚ} {p n : E3} {v D : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hap : 0 < a) (hquot : value? I (IEEEAlgorithm.div I (neg I bw) aw) = some q)
    (ht : value? I (clamp01nan I (IEEEAlgorithm.div I (neg I bw) aw)) = some t)
    (ht0 : 0 ≤ (t:ℝ)) (ht1 : (t:ℝ) ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hn : n ≠ 0) (hD : 0 ≤ D) (hnD : ‖n‖ ≤ D) (hpD : ‖p‖ ≤ D)
    (hrmax : I.format.unitRoundoff ≤ 1/16777216)
    (hlarge : 4*I.format.minSubnormal ≤ ‖n‖^2)
    (hea : |(a:ℝ)-‖n‖^2| ≤
      3*I.format.unitRoundoff*(1+I.format.unitRoundoff)^2*‖n‖^2+2*I.format.minSubnormal)
    (heb : |(b:ℝ)-inner ℝ n p| ≤
      3*I.format.unitRoundoff*(1+I.format.unitRoundoff)^2*‖n‖*‖p‖+2*I.format.minSubnormal) :
    ‖p+(t:ℝ) • n‖^2 ≤ ‖p+v • n‖^2+
      (8*I.format.unitRoundoff*D)^2+12*I.format.minSubnormal+
      4*I.format.minSubnormal*‖n‖^2 := by
  let rho := I.format.unitRoundoff
  let eta := I.format.minSubnormal
  have hr : 0 ≤ rho := I.format.unitRoundoff_pos.le
  have he : 0 ≤ eta := by dsimp [eta]; unfold FP.IEEE.Format.minSubnormal; positivity
  have hr1 : rho < 1 := by dsimp [rho]; linarith
  obtain ⟨delta,zeta,hd,hz,hKKT⟩ := clamped_negative_division_optimal I hone ha hb hap hr1 hquot ht hv0 hv1
  obtain ⟨daR,daA,haeq,hdaR,hdaA⟩ := split_mixed_error
    (show 0 ≤ 3*rho*(1+rho)^2*‖n‖^2 by positivity) (by positivity : 0 ≤ 2*eta) hea
  obtain ⟨dbR,dbA,hbeq,hdbR,hdbA⟩ := split_mixed_error
    (show 0 ≤ 3*rho*(1+rho)^2*‖n‖*‖p‖ by positivity) (by positivity : 0 ≤ 2*eta) heb
  have hdpos : 0 < 1+delta := by have := (abs_le.mp hd).1; dsimp [rho] at hr1; linarith
  let ae := (a:ℝ)/(1+delta)
  let er := ((daR-‖n‖^2*delta)/(1+delta))*(t:ℝ)+dbR
  let ea := (daA/(1+delta))*(t:ℝ)+dbA-ae*zeta
  have hsplit : (ae-‖n‖^2)*(t:ℝ)+((b:ℝ)-ae*zeta-inner ℝ n p)=er+ea :=
    effective_gradient_split (ne_of_gt hdpos) haeq hbeq
  have hsmall : (1+rho)^2 ≤ (1001/1000:ℝ) := by
    have hh := mul_nonneg hr (show 0 ≤ 1/16777216-rho by exact sub_nonneg.mpr hrmax)
    nlinarith only [hh,hrmax,hr]
  have hae0 : 0 ≤ ae := div_nonneg (by exact_mod_cast hap.le) hdpos.le
  have haemax : ae ≤ 4*‖n‖^2 := by
    dsimp [ae]
    apply (div_le_iff₀ hdpos).2
    have hahi := (abs_le.mp hea).2
    have hdelta := (abs_le.mp hd).1
    have hm := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ 3*rho*‖n‖^2 by positivity)
    have hm' := mul_le_mul_of_nonneg_right hrmax (sq_nonneg ‖n‖)
    have hm'' := mul_le_mul_of_nonneg_right hdelta (sq_nonneg ‖n‖)
    dsimp [rho,eta] at *
    nlinarith only [hahi,hm,hm',hm'',hlarge,sq_nonneg ‖n‖]
  have habs : |ea| ≤ 6*eta+2*eta*‖n‖^2 :=
    absolute_gradient_bound (sq_nonneg _) hae0 haemax hr (by linarith : rho ≤ 1/2)
      he hd hdaA hdbA hz ht0 ht1
  have hrel0 := relative_gradient_bound (sq_nonneg ‖n‖) hr hr1 hd hdaR hdbR ht0
  have hcoeff : (3*(1+rho)^2+1)/(1-rho) ≤ (401/100:ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < 1-rho)).2
    linarith only [hsmall,hrmax]
  have hrel : |er| ≤ ‖n‖*(8*rho*D) := by
    have hrewrite : ((3*rho*(1+rho)^2*‖n‖^2+‖n‖^2*rho)/(1-rho))*(t:ℝ) =
        ((3*(1+rho)^2+1)/(1-rho))*rho*‖n‖^2*(t:ℝ) := by ring
    rw [hrewrite] at hrel0
    have hca := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ rho*‖n‖^2*(t:ℝ) by positivity)
    have hcb := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ 3*rho*‖n‖*‖p‖ by positivity)
    have hnt : ‖n‖*(t:ℝ) ≤ D := by nlinarith only [norm_nonneg n,ht1,hnD]
    have hnt' := mul_le_mul_of_nonneg_left hnt (show 0 ≤ (401/100:ℝ)*rho*‖n‖ by positivity)
    have hp' := mul_le_mul_of_nonneg_left hpD (show 0 ≤ (3003/1000:ℝ)*rho*‖n‖ by positivity)
    dsimp [er]
    nlinarith only [hrel0,hca,hcb,hnt',hp',mul_nonneg hr (mul_nonneg (norm_nonneg n) hD)]
  have hspan : |(t:ℝ)-v| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hresult := ReducedProjection.projected_residual_sq_le hn hKKT hsplit hspan
    (by positivity : 0 ≤ 8*rho*D) (by positivity : 0 ≤ 6*eta+2*eta*‖n‖^2) hrel habs
  dsimp [rho,eta] at hresult
  linarith only [hresult]

/-- Outside the tiny-direction branch, the rounded squared direction is
strictly positive and bounded below by one third of its exact value. -/
lemma large_denominator {a n rho eta : ℝ} (hn : 0 < n)
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/16777216)
    (he : 0 ≤ eta) (hlarge : 4*eta ≤ n^2)
    (herr : |a-n^2| ≤ 3*rho*(1+rho)^2*n^2+2*eta) : n^2/3 ≤ a := by
  have hs : (1+rho)^2 ≤ (1001/1000:ℝ) := by
    nlinarith only [hr,hrmax,mul_nonneg hr (sub_nonneg.mpr hrmax)]
  have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ 3*rho*n^2 by positivity)
  have hm' := mul_le_mul_of_nonneg_right hrmax (sq_nonneg n)
  have hlo := (abs_le.mp herr).1
  nlinarith only [hm,hm',hlo,hlarge,sq_nonneg n]

/-- Admissible coordinates make the quotient finite outside the tiny-direction
branch. This avoids case analysis on overflowing quotient encodings. -/
lemma large_quotient_range {a b n p D rho eta T : ℝ}
    (hn : 0 < n) (hp : 0 ≤ p) (hpD : p ≤ D)
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/16777216)
    (he : 0 < eta) (he1 : eta ≤ 1) (hlarge : 4*eta ≤ n^2)
    (ha : n^2/3 ≤ a)
    (hb : |b| ≤ (1+3*rho*(1+rho)^2)*n*p+2*eta)
    (hrange : 16*D+4 < T*Real.sqrt eta) : |b/a| < T := by
  have hs := Real.sq_sqrt he.le
  have hs0 := Real.sqrt_nonneg eta
  have hspos := Real.sqrt_pos.mpr he
  have hs1 : Real.sqrt eta ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith only [he1]⟩
  have hD : 0 ≤ D := hp.trans hpD
  have hT : 3 < T := by nlinarith only [hrange,hs1,hs0,hD]
  have hnroot : 2*Real.sqrt eta ≤ n := by nlinarith only [hlarge,hs,hn,hs0]
  have hTn : 12*D < T*n := by
    have hm := mul_le_mul_of_nonneg_left hnroot (show 0 ≤ T by linarith only [hT])
    nlinarith only [hm,hrange,hD]
  have hcoef : 1+3*rho*(1+rho)^2 ≤ 2 := by
    have hsq : (1+rho)^2 ≤ (1001/1000:ℝ) := by
      nlinarith only [hr,hrmax,mul_nonneg hr (sub_nonneg.mpr hrmax)]
    have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 3*rho by positivity)
    nlinarith only [hm,hrmax]
  have hb' : |b| ≤ 2*D*n+2*eta := by
    have hm := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hn.le hp)
    have hm' := mul_le_mul_of_nonneg_left hpD hn.le
    nlinarith only [hb,hm,hm']
  have ha0 : 0 < a := by nlinarith only [ha,hn]
  rw [abs_div,abs_of_pos ha0]
  apply (div_lt_iff₀ ha0).2
  have hTa := mul_le_mul_of_nonneg_left ha (show 0 ≤ T by linarith only [hT])
  have hTn' := mul_lt_mul_of_pos_right hTn hn
  have hT' := mul_lt_mul_of_pos_right hT (sq_pos_of_pos hn)
  nlinarith only [hb',hTa,hTn',hT',hlarge]

/-- Word-level clamped projection bound with no precondition on the quotient.
A short direction covers every exceptional quotient; the other branch proves
that division is finite before using the IEEE quotient KKT theorem. -/
theorem word_projection_norm_bound (I : Interchange) [I.Valid]
    {aw bw : I.Word} {a b t : ℚ} {p n : E3} {v D : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (ht : value? I (clamp01nan I (IEEEAlgorithm.div I (neg I bw) aw)) = some t)
    (ht0 : 0 ≤ (t:ℝ)) (ht1 : (t:ℝ) ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hD : 0 ≤ D) (hnD : ‖n‖ ≤ D) (hpD : ‖p‖ ≤ D)
    (hrmax : I.format.unitRoundoff ≤ 1/16777216)
    (hemax : I.format.minSubnormal ≤ 1)
    (hesmall : 2*Real.sqrt I.format.minSubnormal ≤ I.format.unitRoundoff)
    (hrange : 16*D+4 < I.format.overflowThreshold*Real.sqrt I.format.minSubnormal)
    (hea : |(a:ℝ)-‖n‖^2| ≤
      3*I.format.unitRoundoff*(1+I.format.unitRoundoff)^2*‖n‖^2+2*I.format.minSubnormal)
    (heb : |(b:ℝ)-inner ℝ n p| ≤
      3*I.format.unitRoundoff*(1+I.format.unitRoundoff)^2*‖n‖*‖p‖+2*I.format.minSubnormal) :
    ‖p+(t:ℝ) • n‖ ≤ ‖p+v • n‖+9*I.format.unitRoundoff*D+
      4*Real.sqrt I.format.minSubnormal := by
  let rho := I.format.unitRoundoff
  let eta := I.format.minSubnormal
  have hr : 0 ≤ rho := I.format.unitRoundoff_pos.le
  have he : 0 < eta := by dsimp [eta]; unfold FP.IEEE.Format.minSubnormal; positivity
  by_cases hshort : ‖n‖^2 ≤ 4*eta
  · have h := short_direction (p := p) ht0 ht1 hv0 hv1 he.le hshort
    nlinarith only [h,Real.sqrt_nonneg eta,mul_nonneg hr hD]
  have hlarge : 4*eta ≤ ‖n‖^2 := le_of_not_ge hshort
  have hnpos : 0 < ‖n‖ := by nlinarith only [norm_nonneg n,he,hlarge]
  have hadown := large_denominator hnpos hr hrmax he.le hlarge hea
  have hap : 0 < a := by
    have har : (0:ℝ) < (a:ℝ) := by nlinarith only [hadown,hnpos]
    exact_mod_cast har
  have hbmag : |(b:ℝ)| ≤ (1+3*rho*(1+rho)^2)*‖n‖*‖p‖+2*eta := by
    have hi := abs_real_inner_le_norm n p
    have hab := abs_add_le ((b:ℝ)-inner ℝ n p) (inner ℝ n p)
    have hid : (b:ℝ)-inner ℝ n p+inner ℝ n p = (b:ℝ) := by ring
    rw [hid] at hab
    nlinarith only [hab,hi,heb]
  have hqrange := large_quotient_range hnpos (norm_nonneg p) hpD hr hrmax he hemax
    hlarge hadown hbmag hrange
  obtain ⟨q,hq,_⟩ := OperationBounds.div_exists_error I (Determinant.neg_value I hb) ha (ne_of_gt hap)
    (OperationBounds.no_overflow_of_lt I _ (by
      simpa only [Rat.cast_div,Rat.cast_neg,neg_div,abs_neg] using hqrange))
  have hloss := finite_word_projection_loss I hone ha hb hap hq ht ht0 ht1 hv0 hv1
    (norm_pos_iff.mp hnpos) hD hnD hpD hrmax hlarge hea heb
  have hnDsq := mul_self_le_mul_self (norm_nonneg n) hnD
  have hηn := mul_le_mul_of_nonneg_left hnDsq (show 0 ≤ 4*eta by positivity)
  have hηsmall := mul_le_mul_of_nonneg_right hesmall hD
  have hηsq := Real.sq_sqrt he.le
  have hroot := Real.sqrt_nonneg eta
  have hηDsq : (Real.sqrt eta*D)^2 = eta*D^2 := by rw [mul_pow,hηsq]
  have hnorm : ‖p+(t:ℝ) • n‖ ≤ ‖p+v • n‖+8*rho*D+4*Real.sqrt eta+2*Real.sqrt eta*D := by
    have hprod1 := mul_nonneg (norm_nonneg (p+v • n))
      (show 0 ≤ 8*rho*D+4*Real.sqrt eta+2*Real.sqrt eta*D by positivity)
    have hprod2 := mul_nonneg (show 0 ≤ 8*rho*D by positivity)
      (show 0 ≤ 4*Real.sqrt eta+2*Real.sqrt eta*D by positivity)
    have hprod3 := mul_nonneg hroot hD
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    nlinarith only [hloss,hηn,hηsq,hroot,hnDsq,hprod1,hprod2,hprod3,hηDsq,mul_nonneg he.le hD,
      norm_nonneg (p+(t:ℝ) • n),norm_nonneg (p+v • n),sq_nonneg (rho*D)]
  dsimp [rho,eta] at hnorm
  linarith only [hnorm,hηsmall]

end DistanceAccuracy.PointProjection

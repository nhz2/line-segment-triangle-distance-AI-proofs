import DistanceAccuracy.PointProjection
import DistanceAccuracy.TotalProjection

namespace DistanceAccuracy.PointProjection
open FP.IEEE FP.IEEE.Interchange
open IEEEAlgorithm IEEEBridge ProjectionRounding
open DistanceAccuracy.Geometry

/-- The tight reduced projection loss, including overflowing quotient results.
The dot-error premises can be discharged by DotWordBounds; the clamped word's
variational condition is derived from actual IEEE division. -/
theorem reduced_word_projection_loss (I : Interchange) [I.Valid]
    {aw bw : I.Word} {a b t : ℚ} {p n : E3} {v D : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hap : 0 < a) (hlim1 : (1:ℝ) < I.format.overflowThreshold)
    (ht : value? I (clamp01nan I (IEEEAlgorithm.div I (neg I bw) aw)) = some t)
    (ht0 : 0 ≤ (t:ℝ)) (ht1 : (t:ℝ) ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hn : n ≠ 0) (hD : 0 ≤ D) (hnD : ‖n‖ ≤ (1+4*I.format.unitRoundoff)*D)
    (hpD : ‖p‖ ≤ (1+4*I.format.unitRoundoff)*D)
    (hrmax : I.format.unitRoundoff ≤ 1/16777216)
    (hlarge : 4*I.format.minSubnormal ≤ ‖n‖^2)
    (hea : |(a:ℝ)-‖n‖^2| ≤
      3*I.format.unitRoundoff*(1+I.format.unitRoundoff)^2*‖n‖^2+2*I.format.minSubnormal)
    (heb : |(b:ℝ)-inner ℝ n p| ≤
      3*I.format.unitRoundoff*(1+I.format.unitRoundoff)^2*‖n‖*‖p‖+2*I.format.minSubnormal) :
    ‖p+(t:ℝ) • n‖^2 ≤ ‖p+v • n‖^2+
      (7.02*I.format.unitRoundoff*D)^2+12*I.format.minSubnormal+
      4*I.format.minSubnormal*‖n‖^2 := by
  let rho := I.format.unitRoundoff
  let eta := I.format.minSubnormal
  have hr : 0 ≤ rho := I.format.unitRoundoff_pos.le
  have he : 0 ≤ eta := by dsimp [eta]; unfold FP.IEEE.Format.minSubnormal; positivity
  have hr1 : rho < 1 := by dsimp [rho]; linarith
  obtain ⟨delta,zeta,hd,hz,hKKT⟩ := clamped_negative_division_optimal_total I hone ha hb hap hr1 hlim1 ht hv0 hv1
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
  let c := (3*(1+rho)^2+1)/(1-rho)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hrel : |er| ≤ ‖n‖*(7.02*rho*D) := by
    have hrewrite : ((3*rho*(1+rho)^2*‖n‖^2+‖n‖^2*rho)/(1-rho))*(t:ℝ) =
        c*rho*‖n‖^2*(t:ℝ) := by dsimp [c]; ring
    rw [hrewrite] at hrel0
    have hnt : ‖n‖*(t:ℝ) ≤ (1+4*rho)*D := by
      nlinarith only [norm_nonneg n,ht1,hnD]
    have hnt' := mul_le_mul_of_nonneg_left hnt (show 0 ≤ c*rho*‖n‖ by positivity)
    have hp' := mul_le_mul_of_nonneg_left hpD (show 0 ≤ 3*(1+rho)^2*rho*‖n‖ by positivity)
    have hcoef := reduced_relative_envelope hr hrmax
    have hcoef' := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ rho*‖n‖*D by positivity)
    change (3*(1+rho)^2+c)*(1+4*rho)*(rho*‖n‖*D) ≤ _ at hcoef'
    dsimp [er]
    nlinarith only [hrel0,hnt',hp',hcoef']
  have hspan : |(t:ℝ)-v| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hresult := ReducedProjection.projected_residual_sq_le hn hKKT hsplit hspan
    (by positivity : 0 ≤ 7.02*rho*D) (by positivity : 0 ≤ 6*eta+2*eta*‖n‖^2) hrel habs
  dsimp [rho,eta] at hresult
  linarith only [hresult]

end DistanceAccuracy.PointProjection

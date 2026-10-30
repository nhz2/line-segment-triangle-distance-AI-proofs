import DistanceAccuracy.ReducedWordProjection
import DistanceAccuracy.NormalizedProjection

namespace DistanceAccuracy.PointProjection
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds
open DistanceAccuracy.Geometry

/-- Complete clamped reduced solve, including tiny directions and overflowing
quotients, transported back to the exact reduced geometry. -/
theorem reduced_geometry_bound (I : Interchange) [I.Valid]
    {aw bw : I.Word} {a b : ℚ} {k n kc nc : E3} {v A D d c : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hA : 0 < A) (hD : 0 < D) (hd : 0 ≤ d) (hc : 0 ≤ c)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hrmax : I.format.unitRoundoff ≤ 1/16777216)
    (hlim : (1:ℝ) < I.format.overflowThreshold)
    (hnD : ‖nc‖ ≤ (1+4*I.format.unitRoundoff)*(A*D))
    (hkD : ‖kc‖ ≤ (1+4*I.format.unitRoundoff)*(A*D))
    (he : ‖kc-k‖+‖nc-n‖ ≤ A*(c*I.format.unitRoundoff*D))
    (hstar : ‖k+v•n‖ ≤ A*d)
    (hea : |(a:ℝ)-‖nc‖^2| ≤
      3*I.format.unitRoundoff*(1+I.format.unitRoundoff)^2*‖nc‖^2+2*I.format.minSubnormal)
    (heb : |(b:ℝ)-inner ℝ nc kc| ≤
      3*I.format.unitRoundoff*(1+I.format.unitRoundoff)^2*‖nc‖*‖kc‖+2*I.format.minSubnormal) :
    ∃ t : ℚ, value? I (clamp01nan I (IEEEAlgorithm.div I (neg I bw) aw)) = some t ∧
      0 ≤ t ∧ t ≤ 1 ∧
      ‖k+(t:ℝ)•n‖/A ≤ I.format.unitRoundoff*D*J c (d/(I.format.unitRoundoff*D))+
        4*Real.sqrt I.format.minSubnormal/A+2*Real.sqrt I.format.minSubnormal*‖nc‖/A := by
  obtain ⟨t,ht,ht0,ht1⟩ := clamp01nan_bounded I hone (IEEEAlgorithm.div I (neg I bw) aw)
  refine ⟨t,ht,ht0,ht1,?_⟩
  have ht0r : (0:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht0
  have ht1r : (t:ℝ) ≤ 1 := by exact_mod_cast ht1
  let rho := I.format.unitRoundoff
  let eta := I.format.minSubnormal
  have hr : 0 < rho := I.format.unitRoundoff_pos
  have heta : 0 ≤ eta := by unfold eta FP.IEEE.Format.minSubnormal; positivity
  have hs := Real.sqrt_nonneg eta
  have hs2 := Real.sq_sqrt heta
  by_cases hsmall : ‖nc‖^2 ≤ 4*eta
  · have hsolve := short_direction (p := kc) ht0r ht1r hv0 hv1 heta hsmall
    have het := ReducedProjection.residual_perturbation ht0r ht1r he
    have hev := ReducedProjection.residual_perturbation hv0 hv1 he
    have h1 := norm_le_norm_add_norm_sub (kc+(t:ℝ)•nc) (k+(t:ℝ)•n)
    have h2 := norm_le_norm_add_norm_sub (k+v•n) (kc+v•nc)
    rw [norm_sub_rev] at h2
    have hraw : ‖k+(t:ℝ)•n‖ ≤ A*d+2*A*(c*rho*D)+2*Real.sqrt eta := by
      nlinarith only [hsolve,het,hev,h1,h2,hstar]
    have hj := le_hypot (d/(rho*D)+c) (7.02:ℝ)
    have hj' := mul_le_mul_of_nonneg_left hj (show 0 ≤ rho*D by positivity)
    have hid : rho*D*(d/(rho*D)+c)=d+c*rho*D := by field_simp <;> ring
    rw [hid] at hj'
    have hjbound : d+2*c*rho*D ≤ rho*D*J c (d/(rho*D)) := by dsimp [J]; nlinarith only [hj']
    have hjA := mul_le_mul_of_nonneg_left hjbound hA.le
    apply (div_le_iff₀ hA).mpr
    have hsqA : 4*Real.sqrt eta/A*A=4*Real.sqrt eta := div_mul_cancel₀ _ hA.ne'
    have hcrossA : 2*Real.sqrt eta*‖nc‖/A*A=2*Real.sqrt eta*‖nc‖ := div_mul_cancel₀ _ hA.ne'
    dsimp [rho,eta] at *
    nlinarith only [hraw,hjA,hsqA,hcrossA,hs,mul_nonneg hs (norm_nonneg nc)]
  · have hlarge : 4*eta ≤ ‖nc‖^2 := le_of_not_ge hsmall
    have hn : nc ≠ 0 := by
      intro hn
      rw [hn, norm_zero] at hsmall
      norm_num at hsmall
      linarith
    have hden := large_denominator (norm_pos_iff.mpr hn) hr.le hrmax heta hlarge hea
    have ha0 : (0:ℝ) < (a:ℝ) := by nlinarith [sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hn)]
    have hap : 0 < a := by exact_mod_cast ha0
    have hsolve := reduced_word_projection_loss I hone ha hb hap hlim ht ht0r ht1r hv0 hv1 hn
      (by positivity : 0 ≤ A*D) hnD hkD hrmax hlarge hea heb
    have he' : ‖kc-k‖+‖nc-n‖ ≤ A*(c*rho*D+0) := by simpa only [add_zero] using he
    have hsolve' : ‖kc+(t:ℝ)•nc‖^2 ≤ ‖kc+v•nc‖^2+(A*(7.02*rho*D))^2+
        2*(6*eta+2*eta*‖nc‖^2) := by dsimp [rho,eta]; nlinarith only [hsolve]
    have hbound := ReducedProjection.normalized_J_bound hA ht0r ht1r hv0 hv1 hd hr hD hc
      (le_refl (0:ℝ)) (by positivity : 0 ≤ 6*eta+2*eta*‖nc‖^2) he' hstar hsolve'
    have hsbound : Real.sqrt (2*(6*eta+2*eta*‖nc‖^2)) ≤ 4*Real.sqrt eta+2*Real.sqrt eta*‖nc‖ := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have hsnorm := congrArg (fun z : ℝ => z*‖nc‖^2) hs2
        have hslinear := congrArg (fun z : ℝ => z*‖nc‖) hs2
        nlinarith [mul_nonneg heta (norm_nonneg nc)]
    have hsdiv := div_le_div_of_nonneg_right hsbound hA.le
    dsimp [rho,eta] at *
    simp only [mul_zero,add_zero] at hbound
    rw [add_div] at hsdiv
    linarith

end DistanceAccuracy.PointProjection

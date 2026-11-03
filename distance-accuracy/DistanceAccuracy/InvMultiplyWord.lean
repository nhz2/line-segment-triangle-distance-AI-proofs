import DistanceAccuracy.InvMultiplyProjection
namespace DistanceAccuracy.InvProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant OperationBounds ProjectionRounding
set_option maxHeartbeats 2000000
theorem second_squared_loss {P Q R : E3} {D rho eta ah bh dh num delta zeta deltaQ zetaQ s t sstar : ℝ}
    (hP : P ≠ 0) (hD : 0 ≤ D) (hPD : ‖P‖ ≤ D) (hkD : ‖R + t • Q‖ ≤ D)
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1 / 16777216) (heta : 0 ≤ eta)
    (hAh : 0 ≤ ah) (hAerr : |ah - ‖P‖ ^ 2| ≤ ‖P‖ ^ 2)
    (hA : |ah - ‖P‖ ^ 2| ≤ (2042 / 1000) * rho * (‖P‖ * D) * (1 + rho) ^ 2 + 2 * eta)
    (hB : |bh - inner ℝ P Q| ≤ (2161 / 1000) * rho * (‖P‖ * D) * (1 + rho) ^ 2 + 2 * eta)
    (hDdot : |dh - inner ℝ P R| ≤ (2161 / 1000) * rho * (‖P‖ * D) * (1 + rho) ^ 2 + 2 * eta)
    (hd : |delta| ≤ rho) (hz : |zeta| ≤ eta / 2)
    (hdQ : |deltaQ| ≤ (2001/1000)*rho) (hzQ : |zetaQ| ≤ eta / 2)
    (hnum : num = (t * bh + dh) * (1 + delta) + zeta)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hstar0 : 0 ≤ sstar) (hstar1 : sstar ≤ 1)
    (hKKT : 0 ≤ ((ah / (1 + deltaQ)) * s + (-num - (ah / (1 + deltaQ)) * zetaQ)) * (sstar - s)) :
    ‖(R + t • Q) + s • (-P)‖ ^ 2 ≤ ‖(R + t • Q) + sstar • (-P)‖ ^ 2 +
      ((469 / 50) * rho * D) ^ 2 + 64 * eta * (1 + ‖P‖ ^ 2) := by
  obtain ⟨er,ea,he,her,hea⟩ := second_gradient_error hP hD hPD hkD hr hrmax heta hAh hAerr hA hB hDdot hd hz hdQ hzQ hnum hs hs1 ht ht1
  have hspan : |s-sstar| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hres := ReducedProjection.projected_residual_sq_le (k := R+t•Q) (n := -P)
    (neg_ne_zero.mpr hP) hKKT (by simpa only [norm_neg] using he) hspan
    (show 0 ≤ (469/50)*rho*D by positivity)
    (show 0 ≤ 32*eta*(1+‖P‖^2) by positivity)
    (by simpa only [norm_neg] using her) hea
  nlinarith only [hres]

theorem second_word_line_or_endpoint (I : Interchange) [I.Valid]
    {aw bw dw tw : I.Word} {a b d t s : ℚ} {P Q R : E3} {D T : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hd : value? I dw = some d) (ht : value? I tw = some t)
    (hs : value? I (clamp01nan I (rdiv I (fma I tw bw dw) aw)) = some s)
    (hap : 0 < a) (hP : P ≠ 0) (hD : 0 ≤ D) (hPD : ‖P‖ ≤ D)
    (hkD : ‖R + (t : ℝ) • Q‖ ≤ D)
    (ht0 : (0 : ℝ) ≤ (t : ℝ)) (ht1 : (t : ℝ) ≤ 1)
    (hs0 : (0 : ℝ) ≤ (s : ℝ)) (hs1 : (s : ℝ) ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1 / 16777216)
    (hlim1 : (1 : ℝ) < I.format.overflowThreshold)
    (hnumlim : |(t : ℝ) * (b : ℝ) + (d : ℝ)| < I.format.overflowThreshold)
    (hnormal : I.format.minNormal ≤ 1/(a:ℝ))
    (hrecip : 1/(a:ℝ) < I.format.overflowThreshold)
    (hT : 0 < T) (hbT : |(b:ℝ)| ≤ (a:ℝ)*T) (hdT : |(d:ℝ)| ≤ (a:ℝ)*T)
    (hetaT : I.format.minSubnormal ≤ (a:ℝ)*T)
    (hprodlim : 8*T < I.format.overflowThreshold)
    (hAerr : |(a : ℝ) - ‖P‖ ^ 2| ≤ ‖P‖ ^ 2)
    (hA : |(a : ℝ) - ‖P‖ ^ 2| ≤ (2042 / 1000) * I.format.unitRoundoff * (‖P‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal)
    (hB : |(b : ℝ) - inner ℝ P Q| ≤ (2161 / 1000) * I.format.unitRoundoff * (‖P‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal)
    (hDdot : |(d : ℝ) - inner ℝ P R| ≤ (2161 / 1000) * I.format.unitRoundoff * (‖P‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal) :
    let u := LineReduction.parameter (-P) R Q (t : ℝ)
    ((s : ℝ)=0 ∧ u≤0) ∨ ((s : ℝ)=1 ∧ 1≤u) ∨
      |(s : ℝ)-u| * ‖P‖ ≤ (469/50)*I.format.unitRoundoff*D+
        (32*I.format.minSubnormal*(1+‖P‖^2))/‖P‖ := by
  let u := LineReduction.parameter (-P) R Q (t : ℝ)
  obtain ⟨n,delta,zeta,dq,zq,hnum,hdelta,hzeta,hdq,hzq,hform⟩ := inv_fma_representation I hone ha hb hd ht hs hap
    (by rwa [abs_of_nonneg ht0]) hrho hnumlim hnormal hrecip hT hbT hdT hetaT hprodlim
  have hdp : 0 < 1+dq := by have := (abs_le.mp hdq).1; linarith only [this,hrho]
  have har : (0:ℝ) < (a:ℝ) := by exact_mod_cast hap
  have hk (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
      0 ≤ (((a:ℝ)/(1+dq))*(s:ℝ)+(-(n:ℝ)-((a:ℝ)/(1+dq))*zq))*(v-(s:ℝ)) := by
    rw [hform]
    apply quotient_effective_optimal (bh := -(n:ℝ)) har hdp _ (by norm_num) hv0 hv1
    simp
  rcases clamp_arbitrary_comparison (u := u) hs0 hs1 (hk 0 (by norm_num) (by norm_num))
      (hk 1 (by norm_num) (by norm_num)) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right
    obtain ⟨er,ea,he,her,hea⟩ := second_gradient_error hP hD hPD hkD
      I.format.unitRoundoff_pos.le hrho (by unfold FP.IEEE.Format.minSubnormal; positivity)
      har.le hAerr hA hB hDdot hdelta hzeta hdq hzq hnum hs0 hs1 ht0 ht1
    have hu := LineReduction.parameter_equation (R := R) (F := Q) (neg_ne_zero.mpr hP) (t:ℝ)
    change ‖-P‖^2*u+inner ℝ (-P) (R+(t:ℝ)•Q)=0 at hu
    rw [norm_neg] at hu
    have hr := I.format.unitRoundoff_pos.le
    apply line_displacement (norm_pos_iff.mpr hP) (by positivity)
      (by unfold FP.IEEE.Format.minSubnormal; positivity) _ h her hea
    nlinarith only [he,hu]

theorem second_word_projection_loss (I : Interchange) [I.Valid]
    {aw bw dw tw : I.Word} {a b d t s : ℚ} {P Q R : E3} {D T sstar : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hd : value? I dw = some d) (ht : value? I tw = some t)
    (hs : value? I (clamp01nan I (rdiv I (fma I tw bw dw) aw)) = some s)
    (hap : 0 < a) (hP : P ≠ 0) (hD : 0 ≤ D) (hPD : ‖P‖ ≤ D)
    (hkD : ‖R + (t : ℝ) • Q‖ ≤ D)
    (ht0 : (0 : ℝ) ≤ (t : ℝ)) (ht1 : (t : ℝ) ≤ 1)
    (hs0 : (0 : ℝ) ≤ (s : ℝ)) (hs1 : (s : ℝ) ≤ 1)
    (hstar0 : 0 ≤ sstar) (hstar1 : sstar ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1 / 16777216)
    (hlim1 : (1 : ℝ) < I.format.overflowThreshold)
    (hnumlim : |(t : ℝ) * (b : ℝ) + (d : ℝ)| < I.format.overflowThreshold)
    (hnormal : I.format.minNormal ≤ 1/(a:ℝ))
    (hrecip : 1/(a:ℝ) < I.format.overflowThreshold)
    (hT : 0 < T) (hbT : |(b:ℝ)| ≤ (a:ℝ)*T) (hdT : |(d:ℝ)| ≤ (a:ℝ)*T)
    (hetaT : I.format.minSubnormal ≤ (a:ℝ)*T)
    (hprodlim : 8*T < I.format.overflowThreshold)
    (hAerr : |(a : ℝ) - ‖P‖ ^ 2| ≤ ‖P‖ ^ 2)
    (hA : |(a : ℝ) - ‖P‖ ^ 2| ≤ (2042 / 1000) * I.format.unitRoundoff * (‖P‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal)
    (hB : |(b : ℝ) - inner ℝ P Q| ≤ (2161 / 1000) * I.format.unitRoundoff * (‖P‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal)
    (hDdot : |(d : ℝ) - inner ℝ P R| ≤ (2161 / 1000) * I.format.unitRoundoff * (‖P‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal) :
    ‖(R + (t : ℝ) • Q) + (s : ℝ) • (-P)‖ ^ 2 ≤ ‖(R + (t : ℝ) • Q) + sstar • (-P)‖ ^ 2 +
      ((469 / 50) * I.format.unitRoundoff * D) ^ 2 + 64 * I.format.minSubnormal * (1 + ‖P‖ ^ 2) := by
  obtain ⟨n,delta,zeta,dq,zq,hnum,hdelta,hzeta,hdq,hzq,hform⟩ := inv_fma_representation I hone ha hb hd ht hs hap
    (by rwa [abs_of_nonneg ht0]) hrho hnumlim hnormal hrecip hT hbT hdT hetaT hprodlim
  have hdp : 0 < 1+dq := by have := (abs_le.mp hdq).1; linarith only [this,hrho]
  have har : (0:ℝ) < (a:ℝ) := by exact_mod_cast hap
  have hKKT : 0 ≤ (((a:ℝ)/(1+dq))*(s:ℝ)+(-(n:ℝ)-((a:ℝ)/(1+dq))*zq))*(sstar-(s:ℝ)) := by
    rw [hform]
    apply quotient_effective_optimal (bh := -(n:ℝ)) har hdp _ (by norm_num) hstar0 hstar1
    simp
  exact second_squared_loss hP hD hPD hkD I.format.unitRoundoff_pos.le hrho
    (by unfold FP.IEEE.Format.minSubnormal; positivity) (by exact_mod_cast hap.le)
    hAerr hA hB hDdot hdelta hzeta hdq hzq hnum hs0 hs1 ht0 ht1 hstar0 hstar1 hKKT

end DistanceAccuracy.InvProjectionRounding

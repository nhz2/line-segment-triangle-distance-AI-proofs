import DistanceAccuracy.ThreeDivideProjection
import DistanceAccuracy.ThreeDivideDots
import DistanceAccuracy.SecondSolveAdmissible
namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant OperationBounds
set_option maxHeartbeats 1500000
theorem second_word_line_or_endpoint (I : Interchange) [I.Valid]
    {aw bw dw tw : I.Word} {a b d t s : ℚ} {P Q R : E3} {D : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hd : value? I dw = some d) (ht : value? I tw = some t)
    (hs : value? I (clamp01nan I (IEEEAlgorithm.div I (fma I tw bw dw) aw)) = some s)
    (hap : 0 < a) (hP : P ≠ 0) (hD : 0 ≤ D) (hPD : ‖P‖ ≤ D)
    (hkD : ‖R + (t : ℝ) • Q‖ ≤ D)
    (ht0 : (0 : ℝ) ≤ (t : ℝ)) (ht1 : (t : ℝ) ≤ 1)
    (hs0 : (0 : ℝ) ≤ (s : ℝ)) (hs1 : (s : ℝ) ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1 / 16777216)
    (hlim1 : (1 : ℝ) < I.format.overflowThreshold)
    (hnumlim : |(t : ℝ) * (b : ℝ) + (d : ℝ)| < I.format.overflowThreshold)
    (hAerr : |(a : ℝ) - ‖P‖ ^ 2| ≤ ‖P‖ ^ 2)
    (hA : |(a : ℝ) - ‖P‖ ^ 2| ≤ (2042 / 1000) * I.format.unitRoundoff * (‖P‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal)
    (hB : |(b : ℝ) - inner ℝ P Q| ≤ (2161 / 1000) * I.format.unitRoundoff * (‖P‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal)
    (hDdot : |(d : ℝ) - inner ℝ P R| ≤ (2161 / 1000) * I.format.unitRoundoff * (‖P‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal) :
    let u := LineReduction.parameter (-P) R Q (t : ℝ)
    ((s : ℝ)=0 ∧ u≤0) ∨ ((s : ℝ)=1 ∧ 1≤u) ∨
      |(s : ℝ)-u| * ‖P‖ ≤ (419/50)*I.format.unitRoundoff*D+
        (32*I.format.minSubnormal*(1+‖P‖^2))/‖P‖ := by
  let u := LineReduction.parameter (-P) R Q (t : ℝ)
  obtain ⟨n, hn, _⟩ := fma_exists_error I ht hb hd
    (no_overflow_of_lt I _ (by simpa only [Rat.cast_add, Rat.cast_mul] using hnumlim))
  obtain ⟨delta, zeta, hnum, hdelta, hzeta⟩ := word_fma_decomposition I ht hb hd hn
  obtain ⟨dq, zq, hdq, hzq, hform⟩ := clamped_division_representation I hone hn ha (ne_of_gt hap) hlim1 hs
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

end DistanceAccuracy.ProjectionRounding

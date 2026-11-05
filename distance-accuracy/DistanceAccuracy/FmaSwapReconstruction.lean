import DistanceAccuracy.ReconstructionIEEE

/-! Reconstruction in the order R - s*P, then + t*Q. -/
namespace DistanceAccuracy.FmaSwapReconstruction
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Reconstruction ReconstructionIEEE
theorem segment_scalar_error {rho eta L p₀ p₁ q₀ q₁ s t P Q AP W R : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/1024) (hL : 0 ≤ L) (heta : eta ≤ rho^2*L)
    (hp₀ : |p₀| ≤ L) (hp₁ : |p₁| ≤ L) (hq₀ : |q₀| ≤ L) (hq₁ : |q₁| ≤ L)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hP : RoundError rho eta (p₁-p₀) P) (hQ : RoundError rho eta (q₁-q₀) Q)
    (hAP : RoundError rho eta (q₀-p₀) AP)
    (hW : RoundError rho eta (AP-s*P) W) (hR : RoundError rho eta (W+t*Q) R) :
    |R-(((1-t)*q₀+t*q₁)-((1-s)*p₀+s*p₁))| ≤ 15*rho*L := by
  have hp := round_difference hr hrmax hL heta hp₁ hp₀ hP
  have hq := round_difference hr hrmax hL heta hq₁ hq₀ hQ
  have hap := round_difference hr hrmax hL heta hq₀ hp₀ hAP
  have ht : |t| ≤ 1 := by rwa [abs_of_nonneg ht0]
  have hs : |(-s)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hs0]; exact hs1
  have hX := interval_abs hL hp₀ hp₁ hs0 hs1
  have hY := interval_abs hL hq₀ hq₁ ht0 ht1
  have hwin : |(AP-s*P)-(q₀-((1-s)*p₀+s*p₁))| ≤ 6*rho*L := by
    have h := affine_input_error hr hL hs hap hp
    convert h using 1 <;> congr 1 <;> ring
  have hw : |W-(q₀-((1-s)*p₀+s*p₁))| ≤ 9*rho*L := by
    have h := round_propagate (C := 6) (K := 2) hr hL heta (by linarith) hwin
      (difference_abs hq₀ hX) hW
    norm_num at h ⊢; exact h
  have hrin : |(W+t*Q)-(((1-t)*q₀+t*q₁)-((1-s)*p₀+s*p₁))| ≤ 12*rho*L := by
    have h := affine_input_error hr hL ht hw hq
    convert h using 1 <;> congr 1 <;> ring
  have h := round_propagate (C := 12) (K := 2) hr hL heta (by linarith) hrin
    (difference_abs hY hX) hR
  norm_num at h ⊢; exact h


variable (I : Interchange) [I.Valid]
theorem segment_trace {p₀ p₁ q₀ q₁ s t : I.Word} {P₀ P₁ Q₀ Q₁ S T : ℚ} {L : ℝ}
    (hp0 : value? I p₀ = some P₀) (hp1 : value? I p₁ = some P₁)
    (hq0 : value? I q₀ = some Q₀) (hq1 : value? I q₁ = some Q₁)
    (hs : value? I s = some S) (ht : value? I t = some T)
    (hL : 0 ≤ L) (hP0 : |(P₀ : ℝ)| ≤ L) (hP1 : |(P₁ : ℝ)| ≤ L)
    (hQ0 : |(Q₀ : ℝ)| ≤ L) (hQ1 : |(Q₁ : ℝ)| ≤ L)
    (hs0 : 0 ≤ S) (hs1 : S ≤ 1) (ht0 : 0 ≤ T) (ht1 : T ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ∃ r : ℚ, value? I (fma I t (sub I q₁ q₀)
      (fma I (neg I s) (sub I p₁ p₀) (sub I q₀ p₀))) = some r ∧
      |(r : ℝ)-(((1-(T : ℝ))*(Q₀ : ℝ)+(T : ℝ)*(Q₁ : ℝ))-
        ((1-(S : ℝ))*(P₀ : ℝ)+(S : ℝ)*(P₁ : ℝ)))| ≤ 15*I.format.unitRoundoff*L := by
  have hr := I.format.unitRoundoff_pos.le
  have hsub : 3*L < I.format.overflowThreshold := by linarith
  have hS0 : (0 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hs0
  have hS1 : (S : ℝ) ≤ 1 := by exact_mod_cast hs1
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht0
  have hT1 : (T : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hS : |((-S : ℚ) : ℝ)| ≤ 1 := by simpa [abs_of_nonneg hS0] using hS1
  have hT : |(T : ℝ)| ≤ 1 := by rwa [abs_of_nonneg hT0]
  obtain ⟨p, hp, hpErr, hpB⟩ := sub_coordinates I hp1 hp0 hL hP1 hP0 hrho heta hsub
  obtain ⟨q, hq, hqErr, hqB⟩ := sub_coordinates I hq1 hq0 hL hQ1 hQ0 hrho heta hsub
  obtain ⟨ap, hap, hapErr, hapB⟩ := sub_coordinates I hq0 hp0 hL hQ0 hP0 hrho heta hsub
  have hr2 := mul_self_le_mul_self hr hrho
  obtain ⟨w, hw, hwErr, hwB⟩ := affine_step I (neg_value I hs) hp hap hL hS hpB hapB heta
    (by nlinarith) (by linarith)
  obtain ⟨r, hrr, hrErr, _⟩ := affine_step I ht hq hw hL hT hqB hwB heta
    (by nlinarith) (by linarith)
  refine ⟨r, hrr, ?_⟩
  exact segment_scalar_error hr hrho hL heta hP0 hP1 hQ0 hQ1
    hS0 hS1 hT0 hT1 hpErr hqErr hapErr
    (by simpa [Rat.cast_neg, sub_eq_add_neg, add_comm] using hwErr)
    (by simpa [add_comm] using hrErr)

end DistanceAccuracy.FmaSwapReconstruction

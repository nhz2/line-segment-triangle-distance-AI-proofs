import DistanceAccuracy.PlaneCrossing
import DistanceAccuracy.TotalProjection
import DistanceAccuracy.WeightedDotGeometry
import DistanceAccuracy.FaceLocal

/-! Height control for the actual divided-and-clamped crossing parameter. -/
namespace DistanceAccuracy.CrossingHeight
open Geometry
set_option maxHeartbeats 1000000

/-- Plane-root perturbation including the division's relative and subnormal
    errors. The true root may be arbitrarily close to a parallel crossing. -/
theorem perturbed_root_height {N M AP P : E3} {rho eta a Q D u v s t delta zeta : ℝ}
    (hr : 0 ≤ rho) (he : 0 ≤ eta) (ha : 0 ≤ a) (hQ : 0 ≤ Q) (hD : 0 < D)
    (hN : 0 < ‖N‖) (hnormal : ‖M-N‖ ≤ a*‖N‖)
    (hAP : ‖AP‖ ≤ D) (hP : ‖P‖ ≤ D) (hAX : ‖AP-s•P‖ ≤ D)
    (hnum : |u-inner ℝ M AP| ≤ Q) (hden : |v-inner ℝ M P| ≤ Q)
    (hd : |delta| ≤ rho) (hz : |zeta| ≤ eta/2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hroot : inner ℝ N (AP-t•P) = 0)
    (hopt : 0 ≤ (v^2*s-(u*(1+delta)+v*zeta)*v)*(t-s)) :
    |inner ℝ N (AP-s•P)|/‖N‖ ≤ a*D+
      ((2+rho)*Q+rho*((1+a)*‖N‖*D)+((1+a)*‖N‖*D+Q)*eta/2)/‖N‖ := by
  let B := (1+a)*‖N‖*D
  let E₀ := (1+rho)*Q+rho*B+(B+Q)*eta/2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 ≤ E₀ := by dsimp [E₀]; positivity
  have hM : ‖M‖ ≤ (1+a)*‖N‖ := by
    have hh := norm_add_le (M-N) N
    rw [sub_add_cancel] at hh
    nlinarith
  have huM : |inner ℝ M AP| ≤ B := by
    have hh := mul_le_mul hM hAP (norm_nonneg _) (by positivity : 0 ≤ (1+a)*‖N‖)
    exact (abs_real_inner_le_norm _ _).trans hh
  have hvM : |inner ℝ M P| ≤ B := by
    have hh := mul_le_mul hM hP (norm_nonneg _) (by positivity : 0 ≤ (1+a)*‖N‖)
    exact (abs_real_inner_le_norm _ _).trans hh
  have hv : |v| ≤ B+Q := by
    have hh := abs_add_le (v-inner ℝ M P) (inner ℝ M P)
    rw [sub_add_cancel] at hh
    linarith
  have h1d : |1+delta| ≤ 1+rho := by
    have hh := abs_add_le (1:ℝ) delta
    norm_num only [abs_one] at hh
    linarith
  have hg0 : |(u*(1+delta)+v*zeta)-inner ℝ M AP| ≤ E₀ := by
    have hid : (u*(1+delta)+v*zeta)-inner ℝ M AP =
        (u-inner ℝ M AP)*(1+delta)+(inner ℝ M AP)*delta+v*zeta := by ring
    rw [hid]
    have h0 := mul_le_mul hnum h1d (abs_nonneg _) hQ
    have h1 := mul_le_mul huM hd (abs_nonneg _) hB
    have h2 := mul_le_mul hv hz (abs_nonneg _) (by positivity : 0 ≤ B+Q)
    have hh := abs_add_le ((u-inner ℝ M AP)*(1+delta)) ((inner ℝ M AP)*delta)
    have hh' := abs_add_le ((u-inner ℝ M AP)*(1+delta)+(inner ℝ M AP)*delta) (v*zeta)
    simp only [abs_mul] at hh hh'
    dsimp [E₀]; nlinarith
  have hg1 : |-v+inner ℝ M P| ≤ Q := by
    have hid : -v+inner ℝ M P = -(v-inner ℝ M P) := by ring
    rw [hid, abs_neg]; exact hden
  have hUD : ‖N‖*D ≠ 0 := ne_of_gt (mul_pos hN hD)
  have hEid : E₀/(‖N‖*D)*‖N‖*D = E₀ := by field_simp
  have hQid : Q/(‖N‖*D)*‖N‖*D = Q := by field_simp
  have hop : 0 ≤ ((-v)^2*s+(u*(1+delta)+v*zeta)*(-v))*(t-s) := by
    nlinarith only [hopt]
  have hh := PlaneCrossing.plane_height ha (show 0 ≤ E₀/(‖N‖*D) by positivity)
    (show 0 ≤ Q/(‖N‖*D) by positivity) hD.le hs0 hs1 ht0 ht1 hN hnormal hP hAX
    (by simpa only [hEid] using hg0) (by simpa only [hQid] using hg1) hroot hop
  have hid : (a+E₀/(‖N‖*D)+Q/(‖N‖*D))*D = a*D+
      ((2+rho)*Q+rho*((1+a)*‖N‖*D)+((1+a)*‖N‖*D+Q)*eta/2)/‖N‖ := by
    dsimp [E₀, B]
    field_simp
    <;> ring
  simpa only [hid] using hh

/-- Numerical budget for the effective affine root before its final FMA. -/
lemma height_budget {rho eta h N D : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/16777216) (he : 0 ≤ eta)
    (heSmall : eta ≤ rho/1000000) (hN : 0 < N) (hD : 0 ≤ D)
    (heFloor : eta ≤ h^2*N) :
    ((2038/1000)*rho)*D+
      ((2+rho)*((2162/1000)*rho*N*D+2*eta)+rho*((1+(2038/1000)*rho)*N*D)+
        ((1+(2038/1000)*rho)*N*D+((2162/1000)*rho*N*D+2*eta))*eta/2)/N
      ≤ (737/100)*rho*D+5*h^2 := by
  have hr2 := mul_le_mul_of_nonneg_left hrmax hr
  have hcore : (2038/1000)*rho+(2+rho)*(2162/1000)*rho+rho*(1+(2038/1000)*rho)
      ≤ (7363/1000)*rho := by nlinarith
  have hcoef : 0 ≤ 1+(2038/1000)*rho+(2162/1000)*rho := by positivity
  have hcoef2 : 1+(2038/1000)*rho+(2162/1000)*rho ≤ 2 := by linarith
  have hepart := mul_le_mul_of_nonneg_right hcoef2 he
  have hsum : (2038/1000)*rho+(2+rho)*(2162/1000)*rho+rho*(1+(2038/1000)*rho)+
      (1+(2038/1000)*rho+(2162/1000)*rho)*eta/2 ≤ (737/100)*rho := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsum (mul_nonneg hN.le hD)
  have hfcoef : 4+2*rho+eta ≤ 5 := by linarith
  have hf := mul_le_mul_of_nonneg_right hfcoef he
  have hfloor : (4+2*rho+eta)*eta ≤ 5*h^2*N := by nlinarith
  apply (le_of_mul_le_mul_right (a := N) ?_ hN)
  field_simp
  nlinarith only [hm, hfloor]

lemma weighted_normal_coefficient {rho : ℝ} (hr : 0 ≤ rho) (hrmax : rho ≤ 1/16777216) :
    (2161/1000)*rho*(1+rho)^2*(1+(2038/1000)*rho) ≤ (2162/1000)*rho := by
  have hrs := mul_self_le_mul_self hr hrmax
  have hU : (1+rho)^2 ≤ 10001/10000 := by nlinarith
  have hV : 1+(2038/1000)*rho ≤ 10001/10000 := by linarith
  have hm := mul_le_mul hU hV (by positivity : 0 ≤ 1+(2038/1000)*rho) (by norm_num : (0:ℝ) ≤ 10001/10000)
  have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ (2161/1000)*rho by positivity)
  nlinarith

open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds
open Determinant DotWordBounds ProjectionRounding

/-- Actual dot products and divided-and-clamped parameter, including a zero
    denominator or an overflowing quotient, satisfy the plane-height bound. -/
theorem word_plane_height (I : Interchange) [I.Valid]
    {Mw APw Pw : Vec3 I} {m ap p : Fin 3 → ℚ} {N : Geometry.E3} {D B h t : ℝ}
    (hone : value? I (one I) = some 1)
    (hM : ∀ k, value? I (Mw k) = some (m k))
    (hAPw : ∀ k, value? I (APw k) = some (ap k))
    (hPw : ∀ k, value? I (Pw k) = some (p k))
    (hD : 0 < D) (hN : 0 < ‖N‖)
    (hnormal : ‖realVec m-N‖ ≤ (2038/1000)*I.format.unitRoundoff*‖N‖)
    (hAP : ‖realVec ap‖ ≤ D) (hP : ‖realVec p‖ ≤ D)
    (hAX : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ‖realVec ap-s•realVec p‖ ≤ D)
    (hAPC : ∀ k, |(ap k : ℝ)| ≤ D/Real.sqrt 3)
    (hPC : ∀ k, |(p k : ℝ)| ≤ D/Real.sqrt 3)
    (hB : 0 < B)
    (hprod0 : ∀ k, |(m k : ℝ)*(ap k : ℝ)| ≤ B)
    (hprod1 : ∀ k, |(m k : ℝ)*(p k : ℝ)| ≤ B)
    (hetaB : I.format.minSubnormal ≤ B)
    (hBmax : 6*B < I.format.overflowThreshold)
    (honeMax : (1:ℝ) < I.format.overflowThreshold)
    (hrho : I.format.unitRoundoff ≤ 1/16777216)
    (hetaSmall : I.format.minSubnormal ≤ I.format.unitRoundoff/1000000)
    (hetaFloor : I.format.minSubnormal ≤ h^2*‖N‖)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hroot : inner ℝ N (realVec ap-t•realVec p) = 0) :
    ∃ s : ℚ,
      value? I (clamp01nan I (div I (dot3 I Mw APw) (dot3 I Mw Pw))) = some s ∧
      0 ≤ s ∧ s ≤ 1 ∧
      |inner ℝ N (realVec ap-(s : ℝ)•realVec p)|/‖N‖ ≤
        (737/100)*I.format.unitRoundoff*D+5*h^2 := by
  have hr := I.format.unitRoundoff_pos.le
  have he : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hr16 : I.format.unitRoundoff ≤ 1/16 := by linarith
  obtain ⟨u, hu, huErr⟩ := dot3_finite_weighted I hM hAPw hB hprod0 hetaB hr16 hBmax
  obtain ⟨v, hv, hvErr⟩ := dot3_finite_weighted I hM hPw hB hprod1 hetaB hr16 hBmax
  obtain ⟨s, hs, hs0, hs1⟩ := clamp01nan_bounded I hone (div I (dot3 I Mw APw) (dot3 I Mw Pw))
  obtain ⟨delta, zeta, hd, hz, hopt⟩ := clamped_affine_division_optimal_total I hone hu hv honeMax hs ht0 ht1
  have hs0r : (0:ℝ) ≤ (s : ℝ) := by exact_mod_cast hs0
  have hs1r : (s : ℝ) ≤ 1 := by exact_mod_cast hs1
  have hMn : ‖realVec m‖ ≤ (1+(2038/1000)*I.format.unitRoundoff)*‖N‖ := by
    have hh := norm_add_le (realVec m-N) N
    rw [sub_add_cancel] at hh
    nlinarith
  have hcoef := weighted_normal_coefficient hr hrho
  have dot_budget (w : Fin 3 → ℚ) (z : ℚ)
      (hwC : ∀ k, |(w k : ℝ)| ≤ D/Real.sqrt 3)
      (hzErr : |(z : ℝ)-scalarDot m w| ≤ I.format.unitRoundoff*(1+I.format.unitRoundoff)^2*
        (3*|(m 0 : ℝ)*(w 0 : ℝ)|+2*|(m 1 : ℝ)*(w 1 : ℝ)|+|(m 2 : ℝ)*(w 2 : ℝ)|)+2*I.format.minSubnormal) :
      |(z : ℝ)-inner ℝ (realVec m) (realVec w)| ≤
        (2162/1000)*I.format.unitRoundoff*‖N‖*D+2*I.format.minSubnormal := by
    have hweighted := weighted_general_scaled (a := realVec m) (b := realVec w) hD.le hwC
    have hmul := mul_le_mul_of_nonneg_left hweighted
      (show 0 ≤ I.format.unitRoundoff*(1+I.format.unitRoundoff)^2 by positivity)
    have hmulM := mul_le_mul_of_nonneg_left hMn
      (show 0 ≤ (2161/1000)*I.format.unitRoundoff*(1+I.format.unitRoundoff)^2*D by positivity)
    have hcoefM := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hN.le hD.le)
    rw [scalarDot_inner] at hzErr
    dsimp [realVec] at hmul hmulM hcoefM hzErr ⊢
    nlinarith only [hzErr, hmul, hmulM, hcoefM]
  have huB := dot_budget ap u hAPC huErr
  have hvB := dot_budget p v hPC hvErr
  have hh := perturbed_root_height hr he
    (show 0 ≤ (2038/1000)*I.format.unitRoundoff by positivity)
    (show 0 ≤ (2162/1000)*I.format.unitRoundoff*‖N‖*D+2*I.format.minSubnormal by positivity)
    hD hN hnormal hAP hP (hAX (s : ℝ) hs0r hs1r) huB hvB hd hz hs0r hs1r ht0 ht1 hroot hopt
  refine ⟨s, hs, hs0, hs1, hh.trans ?_⟩
  exact height_budget hr hrho he hetaSmall hN hD.le hetaFloor

/-- One actual affine FMA evaluation adds at most ρD+η to plane height. -/
theorem affine_height (I : Interchange) [I.Valid]
    {APw Pw : Vec3 I} {ap p : Fin 3 → ℚ} {sword : I.Word} {s : ℚ}
    {N : Geometry.E3} {D H : ℝ}
    (hAP : ∀ k, value? I (APw k) = some (ap k))
    (hP : ∀ k, value? I (Pw k) = some (p k))
    (hs : value? I sword = some s) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hD : 0 < D) (hN : 0 < ‖N‖)
    (hAPC : ∀ k, |(ap k : ℝ)| ≤ D/Real.sqrt 3)
    (hPC : ∀ k, |(p k : ℝ)| ≤ D/Real.sqrt 3)
    (hAX : ‖realVec ap-(s : ℝ)•realVec p‖ ≤ D)
    (height : |inner ℝ N (realVec ap-(s : ℝ)•realVec p)|/‖N‖ ≤ H)
    (hlim : 2*D < I.format.overflowThreshold) :
    ∃ ax : Fin 3 → ℚ,
      (∀ k, value? I (fma3 I (neg I sword) Pw APw k) = some (ax k)) ∧
      |inner ℝ N (realVec ax)|/‖N‖ ≤ H+I.format.unitRoundoff*D+I.format.minSubnormal := by
  have hr := I.format.unitRoundoff_pos.le
  have he : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hs0r : (0:ℝ) ≤ (s : ℝ) := by exact_mod_cast hs0
  have hs1r : (s : ℝ) ≤ 1 := by exact_mod_cast hs1
  have hsabs : |(s : ℝ)| ≤ 1 := by rwa [abs_of_nonneg hs0r]
  have hsqrt : 1 ≤ Real.sqrt (3:ℝ) := by apply (Real.le_sqrt (by norm_num) (by norm_num)).2; norm_num
  have hdiv := div_le_self hD.le hsqrt
  have hbound (k : Fin 3) : |(((-s)*p k+ap k : ℚ) : ℝ)| < I.format.overflowThreshold := by
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_neg]
    have hh := abs_add_le (-(s : ℝ)*(p k : ℝ)) (ap k : ℝ)
    rw [abs_mul, abs_neg] at hh
    have hm := mul_le_mul hsabs ((hPC k).trans hdiv) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have ha := (hAPC k).trans hdiv
    nlinarith
  have hex k := fma_exists_error I (Determinant.neg_value I hs) (hP k) (hAP k)
    (no_overflow_of_lt I _ (hbound k))
  choose ax hax herr using hex
  let V := realVec ap-(s : ℝ)•realVec p
  have hrec : ∀ k, |(realVec ax-V) k| ≤ I.format.unitRoundoff*|V k|+I.format.minSubnormal/2 := by
    intro k
    have hh := herr k
    simpa [V, realVec, Rat.cast_add, Rat.cast_mul, Rat.cast_neg, sub_eq_add_neg, add_comm] using hh
  have hn := vector_mixed_bound (r := realVec ax-V) (n := V) (p := (0 : Geometry.E3))
    hr (by norm_num : (0:ℝ) ≤ 0) (show 0 ≤ I.format.minSubnormal/2 by positivity)
    (by simpa using hrec)
  have hsqrt2 : Real.sqrt (3:ℝ) ≤ 2 := by apply Real.sqrt_le_iff.mpr; norm_num
  have hm := mul_le_mul_of_nonneg_right hsqrt2 (show 0 ≤ I.format.minSubnormal/2 by positivity)
  have hρD := mul_le_mul_of_nonneg_left hAX hr
  have hrecNorm : ‖realVec ax-V‖ ≤ I.format.unitRoundoff*D+I.format.minSubnormal := by
    simp only [zero_mul, add_zero] at hn
    dsimp [V] at hn ⊢
    nlinarith
  have ht := abs_add_le (inner ℝ N V) (inner ℝ N (realVec ax-V))
  have hid : inner ℝ N V+inner ℝ N (realVec ax-V) = inner ℝ N (realVec ax) := by
    simp only [inner_sub_right]; ring
  rw [hid] at ht
  have hi := (abs_real_inner_le_norm N (realVec ax-V)).trans
    (mul_le_mul_of_nonneg_left hrecNorm hN.le)
  have hheight := (div_le_iff₀ hN).mp height
  refine ⟨ax, hax, (div_le_iff₀ hN).mpr ?_⟩
  change |inner ℝ N V| ≤ H*‖N‖ at hheight
  nlinarith

theorem word_crossing_height (I : Interchange) [I.Valid]
    {Mw APw Pw : Vec3 I} {m ap p : Fin 3 → ℚ} {N : Geometry.E3} {D B h t : ℝ}
    (hone : value? I (one I) = some 1)
    (hM : ∀ k, value? I (Mw k) = some (m k))
    (hAPw : ∀ k, value? I (APw k) = some (ap k))
    (hPw : ∀ k, value? I (Pw k) = some (p k))
    (hD : 0 < D) (hN : 0 < ‖N‖)
    (hnormal : ‖realVec m-N‖ ≤ (2038/1000)*I.format.unitRoundoff*‖N‖)
    (hAP : ‖realVec ap‖ ≤ D) (hP : ‖realVec p‖ ≤ D)
    (hAX : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ‖realVec ap-s•realVec p‖ ≤ D)
    (hAPC : ∀ k, |(ap k : ℝ)| ≤ D/Real.sqrt 3)
    (hPC : ∀ k, |(p k : ℝ)| ≤ D/Real.sqrt 3)
    (hB : 0 < B)
    (hprod0 : ∀ k, |(m k : ℝ)*(ap k : ℝ)| ≤ B)
    (hprod1 : ∀ k, |(m k : ℝ)*(p k : ℝ)| ≤ B)
    (hetaB : I.format.minSubnormal ≤ B)
    (hBmax : 6*B < I.format.overflowThreshold)
    (honeMax : (1:ℝ) < I.format.overflowThreshold)
    (hrho : I.format.unitRoundoff ≤ 1/16777216)
    (hetaSmall : I.format.minSubnormal ≤ I.format.unitRoundoff/1000000)
    (hetaFloor : I.format.minSubnormal ≤ h^2*‖N‖)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hroot : inner ℝ N (realVec ap-t•realVec p) = 0)
    (hlinear : 2*D < I.format.overflowThreshold)
    (hetaH : I.format.minSubnormal ≤ h^2) :
    ∃ s : ℚ, ∃ ax : Fin 3 → ℚ,
      value? I (clamp01nan I (div I (dot3 I Mw APw) (dot3 I Mw Pw))) = some s ∧
      (∀ k, value? I (fma3 I (neg I (clamp01nan I (div I (dot3 I Mw APw) (dot3 I Mw Pw)))) Pw APw k) = some (ax k)) ∧
      0 ≤ s ∧ s ≤ 1 ∧ |inner ℝ N (realVec ax)|/‖N‖ ≤
        (42/5)*I.format.unitRoundoff*D+6*h^2 := by
  obtain ⟨s, hs, hs0, hs1, height⟩ := word_plane_height I hone hM hAPw hPw hD hN
    hnormal hAP hP hAX hAPC hPC hB hprod0 hprod1 hetaB hBmax honeMax hrho hetaSmall hetaFloor ht0 ht1 hroot
  obtain ⟨ax, hax, hfinal⟩ := affine_height I hAPw hPw hs hs0 hs1 hD hN hAPC hPC
    (hAX (s : ℝ) (by exact_mod_cast hs0) (by exact_mod_cast hs1)) height hlinear
  refine ⟨s, ax, hs, hax, hs0, hs1, ?_⟩
  have hh := mul_nonneg I.format.unitRoundoff_pos.le hD.le
  nlinarith

end DistanceAccuracy.CrossingHeight

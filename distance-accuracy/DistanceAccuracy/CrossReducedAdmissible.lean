import DistanceAccuracy.CrossReduced
import DistanceAccuracy.FormatRange

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2048

namespace DistanceAccuracy.PointProjection
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds
open DistanceAccuracy.Determinant

noncomputable def crossCoefficient (accurate : Bool) : ℝ := if accurate then 3.60 else 3.17

/-- The complete first (cross-vector) projection from admissible rounded local
geometry. All operation-range and underflow premises are discharged here. -/
theorem cross_reduced_admissible (fmt : DistanceAccuracy.Format) (accurate : Bool)
    {e f r : Vec3 fmt.interchange} {E F R : Fin 3 → ℚ} {L u v d : ℝ}
    (he : ∀ k, value? fmt.interchange (e k) = some (E k))
    (hf : ∀ k, value? fmt.interchange (f k) = some (F k))
    (hr : ∀ k, value? fmt.interchange (r k) = some (R k))
    (hL0 : 0 ≤ L) (hL : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L)
    (hA : fourthRoot fmt.leastSubnormal < ‖realVec E‖)
    (hE : ‖realVec E‖ ≤ (7/2)*L) (hF : ‖realVec F‖ ≤ (7/2)*L) (hR : ‖realVec R‖ ≤ (7/2)*L)
    (hEc : ∀ k, |(E k:ℝ)| ≤ ((7/2)*L)/Real.sqrt 3)
    (hFc : ∀ k, |(F k:ℝ)| ≤ ((7/2)*L)/Real.sqrt 3)
    (hRc : ∀ k, |(R k:ℝ)| ≤ ((7/2)*L)/Real.sqrt 3)
    (hd : 0 ≤ d) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hwitness : ‖GeometryCoverage.residual (realVec R) (realVec E) (realVec F) u v‖ ≤ d) :
    let nw := if accurate then cross3Accurate fmt.interchange e f else cross3 fmt.interchange e f
    let kw := cross3 fmt.interchange e r
    ∃ t : ℚ, value? fmt.interchange (clamp01nan fmt.interchange
      (IEEEAlgorithm.div fmt.interchange (neg fmt.interchange (dot3 fmt.interchange nw kw))
        (dot3 fmt.interchange nw nw))) = some t ∧ 0 ≤ t ∧ t ≤ 1 ∧
      ‖GeometryCoverage.residual (realVec R) (realVec E) (realVec F)
        (LineReduction.parameter (realVec E) (realVec R) (realVec F) (t:ℝ)) (t:ℝ)‖ ≤
        fmt.rho*((7/2)*L)*J (crossCoefficient accurate) (d/(fmt.rho*((7/2)*L)))+
          4*fourthRoot fmt.leastSubnormal+(3/1000000)*fmt.rho*((7/2)*L) := by
  let I := fmt.interchange
  let D : ℝ := (7/2)*L
  let A := ‖realVec E‖
  have hρ : I.format.unitRoundoff = fmt.rho := by
    cases fmt with
    | binary32 => exact fp32_parameters.1
    | binary64 => exact fp64_parameters.1
  have hη : I.format.minSubnormal = fmt.leastSubnormal := by
    cases fmt with
    | binary32 => exact fp32_parameters.2.2
    | binary64 => exact fp64_parameters.2.2
  have hρ0 : 0 < I.format.unitRoundoff := I.format.unitRoundoff_pos
  have hη0 : 0 < I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hη1 : I.format.minSubnormal ≤ 1 := by rw [hη]; cases fmt <;> norm_num [DistanceAccuracy.Format.leastSubnormal]
  have hρmax : I.format.unitRoundoff ≤ 1/16777216 := by rw [hρ]; convert fmt.rho_le using 1 <;> norm_num
  have hA0 : 0 < A := lt_of_le_of_lt (fourthRoot_nonneg _) hA
  have hD : 0 < D := hA0.trans_le hE
  have hLD : L ≤ D := by dsimp [D]; linarith
  have hone : value? I (one I) = some 1 := by cases fmt <;> exact (by first | exact one_fp32 | exact one_fp64)
  have hs : 1 ≤ Real.sqrt (3:ℝ) := by apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr; norm_num
  have hcoord : D/Real.sqrt 3 ≤ D := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hD.le,hs]
  let Pc := D^2+I.format.minSubnormal
  have hPc : 0 < Pc := by dsimp [Pc]; positivity
  have prod_bound (V : Fin 3 → ℚ) (hVc : ∀ k, |(V k:ℝ)| ≤ D/Real.sqrt 3) :
      ∀ i j, |(E i:ℝ)*(V j:ℝ)| ≤ Pc := by
    intro i j
    rw [abs_mul]
    have hh := mul_le_mul ((hEc i).trans hcoord) ((hVc j).trans hcoord) (abs_nonneg _) hD.le
    dsimp [Pc]; nlinarith only [hh,hη0.le]
  have hPclim : 10*Pc < I.format.overflowThreshold := by
    have hlim := fmt.quadratic_range hL0 hL
    dsimp [Pc,D,I] at *
    nlinarith [sq_nonneg L]
  have habs : I.format.minSubnormal ≤ I.format.unitRoundoff*A*D/1000 := by
    have hh := fmt.large_eta_absorption hlarge
    have hm := mul_le_mul hA.le hLD hL0 hA0.le
    have hm' := mul_le_mul_of_nonneg_left hm fmt.rho_nonneg
    rw [hη,hρ]
    nlinarith only [hh,hm']
  let nw := if accurate then cross3Accurate I e f else cross3 I e f
  let kw := cross3 I e r
  have hpair : ∃ N K : Fin 3 → ℚ,
      (∀ k, value? I (nw k) = some (N k)) ∧ (∀ k, value? I (kw k) = some (K k)) ∧
      ‖realVec N-exactCross (realVec E) (realVec F)‖+‖realVec K-exactCross (realVec E) (realVec R)‖ ≤
        crossCoefficient accurate*I.format.unitRoundoff*A*D ∧
      ‖realVec N‖ ≤ (1+4*I.format.unitRoundoff)*(A*D) ∧ ‖realVec K‖ ≤ (1+4*I.format.unitRoundoff)*(A*D) := by
    cases accurate
    · exact ordinary_cross_pair I he hf hr hD.le hF hR hFc hRc hPc (prod_bound F hFc) (prod_bound R hRc)
        (by dsimp [Pc]; nlinarith [sq_nonneg D]) hρmax hPclim habs
    · exact accurate_cross_pair I he hf hr hD.le hF hR hFc hRc hPc (prod_bound F hFc) (prod_bound R hRc)
        (by dsimp [Pc]; nlinarith [sq_nonneg D]) hρmax hPclim habs
  obtain ⟨N,K,hN,hK,herr,hNnorm,hKnorm⟩ := hpair
  let Pd := ((1+4*I.format.unitRoundoff)*(A*D))^2+I.format.minSubnormal/I.format.unitRoundoff
  have hPd : 0 < Pd := by dsimp [Pd]; positivity
  have hPd_eta : I.format.minSubnormal ≤ I.format.unitRoundoff*Pd := by
    have hn : I.format.unitRoundoff ≠ 0 := hρ0.ne'
    have heq : I.format.unitRoundoff*(I.format.minSubnormal/I.format.unitRoundoff)=I.format.minSubnormal := by field_simp
    dsimp [Pd]
    nlinarith [mul_nonneg hρ0.le (sq_nonneg ((1+4*I.format.unitRoundoff)*(A*D)))]
  have hPd_lim : (11/10:ℝ)*Pd < I.format.overflowThreshold :=
    fmt.cross_dot_range hL0 hL hA0.le hE (le_refl _)
  have hlim1 : (1:ℝ) < I.format.overflowThreshold := by
    have hh := fmt.quadratic_range hL0 hL
    nlinarith [mul_self_nonneg L]
  obtain ⟨t,ht,ht0,ht1,hbound⟩ := cross_reduced_from_data I hone hN hK (norm_ne_zero_iff.mp hA0.ne') hD hd
    (by cases accurate <;> norm_num [crossCoefficient]) hv0 hv1 hρmax hlim1 hNnorm hKnorm herr hwitness hPd
    (by dsimp [Pd]; exact le_add_of_nonneg_right (by positivity)) hPd_eta hPd_lim
  refine ⟨t,ht,ht0,ht1,?_⟩
  have hroot : fourthRoot fmt.leastSubnormal^2 = Real.sqrt fmt.leastSubnormal := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hsA : Real.sqrt fmt.leastSubnormal/A ≤ fourthRoot fmt.leastSubnormal := by
    apply (div_le_iff₀ hA0).mpr
    rw [← hroot]
    nlinarith [mul_nonneg (fourthRoot_nonneg fmt.leastSubnormal) (sub_nonneg.mpr hA.le)]
  have hsA4 : 4*Real.sqrt fmt.leastSubnormal/A ≤ 4*fourthRoot fmt.leastSubnormal := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hsA (by norm_num : (0:ℝ) ≤ 4)
  have htiny := mul_le_mul_of_nonneg_right fmt.sqrt_eta_absorption hD.le
  have hU : 1+4*fmt.rho ≤ (3/2:ℝ) := by have hh := fmt.rho_le; norm_num at hh ⊢; linarith
  have hm := mul_le_mul_of_nonneg_left hU (show 0 ≤ 2*Real.sqrt fmt.leastSubnormal*D by positivity)
  rw [hρ,hη] at hbound
  change ‖GeometryCoverage.residual (realVec R) (realVec E) (realVec F)
      (LineReduction.parameter (realVec E) (realVec R) (realVec F) (t:ℝ)) (t:ℝ)‖ ≤ _
  dsimp [A,D] at *
  nlinarith only [hbound,hsA4,htiny,hm]

end DistanceAccuracy.PointProjection

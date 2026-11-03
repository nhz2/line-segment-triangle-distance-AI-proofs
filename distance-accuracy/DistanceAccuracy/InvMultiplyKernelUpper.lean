import DistanceAccuracy.InvMultiplyRaw
import DistanceAccuracy.ThreeDivideStored
namespace DistanceAccuracy.InvMultiplyKernelUpper
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds
open DistanceAccuracy.Determinant ProjectionRounding UpperSelection
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option exponentiation.threshold 2048
theorem kernel_upper (fmt : DistanceAccuracy.Format)
    {Pw Qw Rw : Vec3 fmt.interchange} {p q r : Fin 3 → ℚ} {L s₀ t₀ d : ℝ}
    (hP : ∀ i, value? fmt.interchange (Pw i) = some (p i))
    (hQ : ∀ i, value? fmt.interchange (Qw i) = some (q i))
    (hR : ∀ i, value? fmt.interchange (Rw i) = some (r i))
    (hL0 : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L)
    (hpD : ‖realVec p‖ ≤ (7/2)*L) (hqD : ‖realVec q‖ ≤ (7/2)*L) (hrD : ‖realVec r‖ ≤ (7/2)*L)
    (hpC : ∀ i, |(p i:ℝ)| ≤ ((7/2)*L)/Real.sqrt 3)
    (hqC : ∀ i, |(q i:ℝ)| ≤ ((7/2)*L)/Real.sqrt 3)
    (hrC : ∀ i, |(r i:ℝ)| ≤ ((7/2)*L)/Real.sqrt 3)
    (hgeo : ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      ‖realVec r+t•realVec q-s•realVec p‖ ≤ (7/2)*L)
    (hs₀ : s₀ ∈ Set.Icc (0:ℝ) 1) (ht₀ : t₀ ∈ Set.Icc (0:ℝ) 1) (hd : 0 ≤ d)
    (hwitness : ‖realVec r+t₀•realVec q-s₀•realVec p‖ ≤ d) :
    Upper fmt.interchange (fmt.rho*((7/2)*L)*FI (d/(fmt.rho*((7/2)*L)))+
      3.55*fmt.rho*((7/2)*L)+6*fourthRoot fmt.leastSubnormal)
      (InvMultiplyCore.core fmt.interchange Pw Qw Rw).q := by
  let I := fmt.interchange
  let D : ℝ := (7/2)*L
  have hρ : I.format.unitRoundoff = fmt.rho := by cases fmt <;> first | exact fp32_parameters.1 | exact fp64_parameters.1
  have hη : I.format.minSubnormal = fmt.leastSubnormal := by cases fmt <;> first | exact fp32_parameters.2.2 | exact fp64_parameters.2.2
  have hH : 0 < fourthRoot fmt.leastNormal := by
    unfold fourthRoot
    apply Real.sqrt_pos.mpr
    apply Real.sqrt_pos.mpr
    cases fmt <;> norm_num [Format.leastNormal]
  have hD : 0 < D := by dsimp [D]; linarith
  have hρp : 0 < fmt.rho := by rw [←hρ]; exact I.format.unitRoundoff_pos
  have hρmax : I.format.unitRoundoff ≤ 1/16777216 := by
    rw [hρ]; have hh := fmt.rho_le; norm_num at hh; exact hh
  have hη1 : I.format.minSubnormal ≤ 1 := by
    rw [hη]; cases fmt <;> norm_num [Format.leastSubnormal]
  obtain ⟨s,t,hs,ht,hs0,hs1,ht0,ht1,hraw⟩ := InvMultiplyRaw.raw_upper fmt
    hP hQ hR hL0 hadm hlarge hpD hqD hrD hpC hqC hrC hgeo hs₀ ht₀ hd hwitness
  have hsr : (s:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by exact_mod_cast hs0,by exact_mod_cast hs1⟩
  have htr : (t:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by exact_mod_cast ht0,by exact_mod_cast ht1⟩
  have hpartial : ‖(t:ℝ)•realVec q+realVec r‖ ≤ D := by
    simpa [add_comm] using hgeo 0 t (by norm_num) (by norm_num) htr.1 htr.2
  have hfinal : ‖-(s:ℝ)•realVec p+((t:ℝ)•realVec q+realVec r)‖ ≤ D := by
    convert hgeo s t hsr.1 hsr.2 htr.1 htr.2 using 1
    congr 1; module
  obtain ⟨hlin,hquad⟩ := stored_ranges fmt hD.le hadm (show D ≤ 9*L by dsimp [D]; linarith)
  obtain ⟨score,hscore,_,hbound⟩ := segment_candidate_score_sharp I hs ht hP hQ hR hD.le hpartial hfinal hρmax hη1 hlin hquad
  have hid : -(s:ℝ)•realVec p+((t:ℝ)•realVec q+realVec r) = realVec r+(t:ℝ)•realVec q-(s:ℝ)•realVec p := by module
  rw [hid] at hfinal hbound
  rw [hρ,hη] at hbound
  have hrmax : fmt.rho ≤ 1/16777216 := by rwa [hρ] at hρmax
  refine ⟨score,hscore,?_⟩
  exact inv_score_envelope hρp hrmax hD hd (fourthRoot_nonneg _) fmt.subnormal_nonneg
    (norm_nonneg _) hfinal (fmt.three_absolute_budget hD.le) hraw hbound

end DistanceAccuracy.InvMultiplyKernelUpper

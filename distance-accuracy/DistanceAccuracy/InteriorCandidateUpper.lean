import DistanceAccuracy.SecondSolveAdmissible
import DistanceAccuracy.SegmentStoredNorm
import DistanceAccuracy.UnderflowAbsorption
import DistanceAccuracy.UpperSelection
import DistanceAccuracy.Constants

/-! Actual interior-candidate upper score after the second parameter solve. -/
namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant
set_option exponentiation.threshold 2048
set_option maxHeartbeats 1000000

lemma stored_ranges (fmt : Format) {L D : ℝ} (hD : 0 ≤ D)
    (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4) (hDL : D ≤ 9*L) :
    4*(D+1) < fmt.interchange.format.overflowThreshold ∧
    8*(4*(D+1))*(4*(D+1))+4 < fmt.interchange.format.overflowThreshold := by
  have hc := fmt.admissible_coordinate_ceiling hadm
  have hDC : D ≤ 9*fmt.coordinateCeiling := by linarith
  constructor
  · have hh : 4*(9*fmt.coordinateCeiling+1) < fmt.interchange.format.overflowThreshold := by
      cases fmt <;> norm_num [Format.interchange, Format.coordinateCeiling, fp32, fp64,
        FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.overflowThreshold]
    linarith
  · have hh : 8*(4*(9*fmt.coordinateCeiling+1))^2+4 < fmt.interchange.format.overflowThreshold := by
      cases fmt <;> norm_num [Format.interchange, Format.coordinateCeiling, fp32, fp64,
        FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.overflowThreshold]
    have hs := mul_self_le_mul_self (show 0 ≤ 4*(D+1) by positivity)
      (show 4*(D+1) ≤ 4*(9*fmt.coordinateCeiling+1) by linarith)
    nlinarith

lemma projection_norm_budget {rho eta D A n b : ℝ}
    (hr : 0 ≤ rho) (he : 0 ≤ eta) (hD : 0 ≤ D) (hA : 0 ≤ A) (hAD : A ≤ D) (hn : 0 ≤ n)
    (h : n^2 ≤ b^2+((419/50)*rho*D)^2+64*eta*(1+A^2)) :
    n ≤ hypot b ((419/50)*rho*D)+8*Real.sqrt eta*(1+D) := by
  have hh := hypot_sq b ((419/50)*rho*D)
  have hh0 := hypot_nonneg b ((419/50)*rho*D)
  have heS := Real.sq_sqrt he
  have hADsq : A^2 ≤ D^2 := (sq_le_sq₀ hA hD).2 hAD
  have hmul := mul_le_mul_of_nonneg_left hADsq (show 0 ≤ 64*eta by positivity)
  have heD := mul_nonneg he hD
  have hn0 : 0 ≤ 8*Real.sqrt eta*(1+D) := by positivity
  have hs : n^2 ≤ (hypot b ((419/50)*rho*D))^2+(8*Real.sqrt eta*(1+D))^2 := by
    nlinarith
  nlinarith [mul_nonneg hh0 hn0]

/-- Actual two-FMA interior residual and stored squared norm, after the
    actual second solve. The first parameter is any decoded word in [0,1]. -/
theorem interior_candidate_upper (fmt : Format)
    {Pw Qw Rw : Vec3 fmt.interchange} {p q r : Fin 3 → ℚ}
    {tw : fmt.interchange.Word} {t : ℚ} {D L sstar : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hP : ∀ i, value? fmt.interchange (Pw i) = some (p i))
    (hQ : ∀ i, value? fmt.interchange (Qw i) = some (q i))
    (hR : ∀ i, value? fmt.interchange (Rw i) = some (r i))
    (ht : value? fmt.interchange tw = some t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hA : fourthRoot fmt.leastSubnormal < ‖realVec p‖) (hDL : D ≤ 9*L)
    (hpD : ‖realVec p‖ ≤ D) (hqD : ‖realVec q‖ ≤ D) (hrD : ‖realVec r‖ ≤ D)
    (hres : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ‖realVec r+(t : ℝ)•realVec q-s•realVec p‖ ≤ D)
    (hpC : ∀ i, |(p i : ℝ)| ≤ D/Real.sqrt 3)
    (hqC : ∀ i, |(q i : ℝ)| ≤ D/Real.sqrt 3)
    (hrC : ∀ i, |(r i : ℝ)| ≤ D/Real.sqrt 3)
    (hstar0 : 0 ≤ sstar) (hstar1 : sstar ≤ 1) :
    let sw := clamp01nan fmt.interchange
      (div fmt.interchange (fma fmt.interchange tw (dot3 fmt.interchange Pw Qw) (dot3 fmt.interchange Pw Rw))
        (dot3 fmt.interchange Pw Pw))
    let rw := fma3 fmt.interchange (neg fmt.interchange sw) Pw (fma3 fmt.interchange tw Qw Rw)
    UpperSelection.Upper fmt.interchange
      (hypot ‖realVec r+(t : ℝ)•realVec q-sstar•realVec p‖ ((419/50)*fmt.interchange.format.unitRoundoff*D)+
        (177/50)*fmt.interchange.format.unitRoundoff*D+fourthRoot fmt.leastSubnormal)
      (dot3 fmt.interchange rw rw) := by
  let sw := clamp01nan fmt.interchange
      (div fmt.interchange (fma fmt.interchange tw (dot3 fmt.interchange Pw Qw) (dot3 fmt.interchange Pw Rw))
        (dot3 fmt.interchange Pw Pw))
  have hkD : ‖realVec r+(t : ℝ)•realVec q‖ ≤ D := by simpa using hres 0 (by norm_num) (by norm_num)
  obtain ⟨s, hs, hs0, hs1, hproj⟩ := second_solve_admissible fmt hone hP hQ hR ht ht0 ht1
    hL hadm hA hDL hpD hqD hrD hkD hpC hqC hrC
  have hD : 0 ≤ D := (norm_nonneg _).trans hpD
  have hρ := fmt.interchange.format.unitRoundoff_pos.le
  have hρeq : fmt.interchange.format.unitRoundoff = fmt.rho := by
    cases fmt
    · exact fp32_parameters.1
    · exact fp64_parameters.1
  have hηeq : fmt.interchange.format.minSubnormal = fmt.leastSubnormal := by
    cases fmt
    · exact fp32_parameters.2.2
    · exact fp64_parameters.2.2
  have hη : 0 ≤ fmt.interchange.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hρmax : fmt.interchange.format.unitRoundoff ≤ 1/16777216 := by
    rw [hρeq]; have hh := fmt.rho_le; norm_num at hh; exact hh
  have hη1 : fmt.interchange.format.minSubnormal ≤ 1 := by
    rw [hηeq]; cases fmt <;> norm_num [Format.leastSubnormal]
  have hpartial : ‖(t : ℝ)•realVec q+realVec r‖ ≤ D := by simpa [add_comm] using hkD
  have hfinal : ‖-(s : ℝ)•realVec p+((t : ℝ)•realVec q+realVec r)‖ ≤ D := by
    have hh := hres (s : ℝ) (by exact_mod_cast hs0) (by exact_mod_cast hs1)
    convert hh using 1 <;> congr 1 <;> module
  obtain ⟨hlin, hquad⟩ := stored_ranges fmt hD hadm hDL
  obtain ⟨score, hscore, _, hscoreBound⟩ := segment_candidate_score fmt.interchange hs ht hP hQ hR hD
    hpartial hfinal hρmax hη1 hlin hquad
  have hsq := hproj sstar hstar0 hstar1
  have hn := projection_norm_budget hρ hη hD (norm_nonneg _) hpD
    (norm_nonneg ((realVec r+(t : ℝ)•realVec q)+(s : ℝ)•(-realVec p))) hsq
  have htarget : -(s : ℝ)•realVec p+((t : ℝ)•realVec q+realVec r) =
      (realVec r+(t : ℝ)•realVec q)+(s : ℝ)•(-realVec p) := by module
  rw [htarget] at hscoreBound
  have hcompare : (realVec r+(t : ℝ)•realVec q)+sstar•(-realVec p) =
      realVec r+(t : ℝ)•realVec q-sstar•realVec p := by module
  rw [hcompare] at hn
  have hfloor := fmt.kernel_absolute_budget hD
  rw [← hρeq, ← hηeq] at hfloor
  refine ⟨score, hscore, ?_⟩
  have hm := mul_nonneg hρ hD
  rw [← hηeq]
  nlinarith only [hscoreBound, hn, hfloor, hm]

/-- Finiteness of the actual interior candidate for every first-edge length.
    The second solve may produce NaN or infinity before clamping. -/
theorem interior_candidate_finite (fmt : Format)
    {Pw Qw Rw : Vec3 fmt.interchange} {p q r : Fin 3 → ℚ}
    {tw : fmt.interchange.Word} {t : ℚ} {D L : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hP : ∀ i, value? fmt.interchange (Pw i) = some (p i))
    (hQ : ∀ i, value? fmt.interchange (Qw i) = some (q i))
    (hR : ∀ i, value? fmt.interchange (Rw i) = some (r i))
    (ht : value? fmt.interchange tw = some t)
    (hD : 0 ≤ D) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4) (hDL : D ≤ 9*L)
    (hres : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ‖realVec r+(t : ℝ)•realVec q-s•realVec p‖ ≤ D) :
    let sw := clamp01nan fmt.interchange
      (div fmt.interchange (fma fmt.interchange tw (dot3 fmt.interchange Pw Qw) (dot3 fmt.interchange Pw Rw))
        (dot3 fmt.interchange Pw Pw))
    let rw := fma3 fmt.interchange (neg fmt.interchange sw) Pw (fma3 fmt.interchange tw Qw Rw)
    UpperSelection.Finite fmt.interchange (dot3 fmt.interchange rw rw) := by
  obtain ⟨s, hs, hs0, hs1⟩ := OperationBounds.clamp01nan_bounded fmt.interchange hone
    (div fmt.interchange (fma fmt.interchange tw (dot3 fmt.interchange Pw Qw) (dot3 fmt.interchange Pw Rw))
      (dot3 fmt.interchange Pw Pw))
  have hρmax : fmt.interchange.format.unitRoundoff ≤ 1/16777216 := by
    cases fmt <;> norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32,
      FP.IEEE.binary64, FP.IEEE.Format.unitRoundoff]
  have hη1 : fmt.interchange.format.minSubnormal ≤ 1 := by
    cases fmt <;> norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32,
      FP.IEEE.binary64, FP.IEEE.Format.minSubnormal]
  have hpartial : ‖(t : ℝ)•realVec q+realVec r‖ ≤ D := by
    simpa [add_comm] using hres 0 (by norm_num) (by norm_num)
  have hfinal : ‖-(s : ℝ)•realVec p+((t : ℝ)•realVec q+realVec r)‖ ≤ D := by
    have hh := hres (s : ℝ) (by exact_mod_cast hs0) (by exact_mod_cast hs1)
    convert hh using 1 <;> congr 1 <;> module
  obtain ⟨hlin, hquad⟩ := stored_ranges fmt hD hadm hDL
  obtain ⟨score, hscore, _, _⟩ := segment_candidate_score fmt.interchange hs ht hP hQ hR hD
    hpartial hfinal hρmax hη1 hlin hquad
  exact ⟨score, hscore⟩

end DistanceAccuracy.ProjectionRounding

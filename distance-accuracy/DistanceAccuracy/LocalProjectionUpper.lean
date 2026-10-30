import DistanceAccuracy.SecondSolveAdmissible
import DistanceAccuracy.SegmentStoredNorm
import DistanceAccuracy.UnderflowAbsorption
import DistanceAccuracy.UpperSelection

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant OperationBounds
set_option exponentiation.threshold 2048

lemma segment_norm_bound {R E : E3} {t D : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hR : ‖R‖ ≤ D) (hRE : ‖R + E‖ ≤ D) :
    ‖R + t • E‖ ≤ D := by
  have heq : R + t • E = (1 - t) • R + t • (R + E) := by module
  rw [heq]
  have h := norm_add_le ((1 - t) • R) (t • (R + E))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_nonneg (sub_nonneg.mpr ht1)] at h
  have h1 := mul_le_mul_of_nonneg_left hR (sub_nonneg.mpr ht1)
  have h2 := mul_le_mul_of_nonneg_left hRE ht0
  nlinarith only [h, h1, h2]

lemma short_direction_norm {R E : E3} {t v h : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hE : ‖E‖ ≤ h) :
    ‖R + t • E‖ ≤ ‖R + v • E‖ + h := by
  have heq : R + t • E = (R + v • E) + (t - v) • E := by module
  rw [heq]
  have hh := norm_add_le (R + v • E) ((t - v) • E)
  rw [norm_smul, Real.norm_eq_abs] at hh
  have hspan : |t-v| ≤ 1 := abs_le.mpr ⟨by linarith only [ht0,hv1],by linarith only [ht1,hv0]⟩
  have hm := mul_le_mul_of_nonneg_right hspan (norm_nonneg E)
  linarith only [hh, hm, hE]

lemma squared_loss_norm {r w : E3} {B eta A : ℝ}
    (heta : 0 ≤ eta) (hA : 0 ≤ A)
    (hloss : ‖r‖ ^ 2 ≤ ‖w‖ ^ 2 + B ^ 2 + 64 * eta * (1 + A ^ 2)) :
    ‖r‖ ≤ hypot ‖w‖ B + 8 * Real.sqrt eta * (1 + A) := by
  have hsq := hypot_sq ‖w‖ B
  have hs := Real.sq_sqrt heta
  have hcross := mul_nonneg (hypot_nonneg ‖w‖ B) (show 0 ≤ 8 * Real.sqrt eta * (1 + A) by positivity)
  have hextra := mul_nonneg heta hA
  have hsp : (8 * Real.sqrt eta * (1 + A)) ^ 2 = 64 * eta * (1 + A) ^ 2 := by
    rw [mul_pow, mul_pow, hs]
    ring
  have hnonneg : 0 ≤ hypot ‖w‖ B + 8 * Real.sqrt eta * (1 + A) :=
    add_nonneg (hypot_nonneg _ _) (by positivity)
  apply (sq_le_sq₀ (norm_nonneg r) hnonneg).mp
  nlinarith only [hloss, hsq, hsp, hcross, hextra]

lemma evaluation_ranges (fmt : Format) {D L : ℝ} (hD : 0 ≤ D) (hDL : D ≤ 9 * L)
    (hadm : L < fourthRoot fmt.interchange.format.maxFinite / 4) :
    4 * (D + 1) < fmt.interchange.format.overflowThreshold ∧
      8 * (4 * (D + 1)) * (4 * (D + 1)) + 4 < fmt.interchange.format.overflowThreshold := by
  have hc := fmt.admissible_coordinate_ceiling hadm
  have hDC : D ≤ 9 * fmt.coordinateCeiling := by linarith only [hc,hDL]
  have hk : 0 ≤ 4 * (D + 1) := by positivity
  have hkb : 4 * (D + 1) ≤ 4 * (9 * fmt.coordinateCeiling + 1) := by linarith only [hDC]
  have hs := mul_self_le_mul_self hk hkb
  have hb : 8 * (4 * (9 * fmt.coordinateCeiling + 1)) ^ 2 + 4 < fmt.interchange.format.overflowThreshold := by
    cases fmt <;> norm_num [Format.coordinateCeiling, Format.interchange, fp32, fp64,
      FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.overflowThreshold]
  have hsecond : 8 * (4 * (D + 1)) * (4 * (D + 1)) + 4 < fmt.interchange.format.overflowThreshold := by
    nlinarith only [hs,hb]
  exact ⟨by nlinarith only [hsecond,hD], hsecond⟩

lemma format_parameters (fmt : Format) :
    fmt.interchange.format.unitRoundoff = fmt.rho ∧
    fmt.interchange.format.minSubnormal = fmt.leastSubnormal := by
  cases fmt <;> norm_num [Format.interchange, Format.rho, Format.leastSubnormal, fp32, fp64,
    FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.unitRoundoff, FP.IEEE.Format.minSubnormal]

/-- Uniform upper bound for the actual direct candidate, including zero and
arbitrarily short directions and NaN/Inf quotient results before clamping. -/
theorem direct_candidate_upper (fmt : Format)
    {Ew Rw : Vec3 fmt.interchange} {e r : Fin 3 → ℚ} {D L v : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hE : ∀ i, value? fmt.interchange (Ew i) = some (e i))
    (hR : ∀ i, value? fmt.interchange (Rw i) = some (r i))
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite / 4)
    (hDL : D ≤ 9 * L) (heD : ‖realVec e‖ ≤ D) (hrD : ‖realVec r‖ ≤ D)
    (hRE : ‖realVec r + realVec e‖ ≤ D)
    (heC : ∀ i, |(e i : ℝ)| ≤ D / Real.sqrt 3)
    (hrC : ∀ i, |(r i : ℝ)| ≤ D / Real.sqrt 3)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    let tw := clamp01nan fmt.interchange (div fmt.interchange
      (neg fmt.interchange (dot3 fmt.interchange Ew Rw)) (dot3 fmt.interchange Ew Ew))
    let rw := fma3 fmt.interchange tw Ew Rw
    UpperSelection.Upper fmt.interchange
      (hypot ‖realVec r + v • realVec e‖ ((419 / 50) * fmt.rho * D) +
        (127 / 50) * fmt.rho * D + 2 * fourthRoot fmt.leastSubnormal)
      (dot3 fmt.interchange rw rw) := by
  dsimp only
  let tw := clamp01nan fmt.interchange (div fmt.interchange
    (neg fmt.interchange (dot3 fmt.interchange Ew Rw)) (dot3 fmt.interchange Ew Ew))
  obtain ⟨t, ht, ht0, ht1⟩ := clamp01nan_bounded fmt.interchange hone
    (div fmt.interchange (neg fmt.interchange (dot3 fmt.interchange Ew Rw)) (dot3 fmt.interchange Ew Ew))
  have ht0r : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht0
  have ht1r : (t : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hD : 0 ≤ D := (norm_nonneg _).trans heD
  have hfinal := segment_norm_bound ht0r ht1r hrD hRE
  obtain ⟨hlim,hqlim⟩ := evaluation_ranges fmt hD hDL hadm
  have hrmax : fmt.interchange.format.unitRoundoff ≤ 1 / 16777216 := by
    rw [(format_parameters fmt).1]; simpa only [show (2 : ℝ) ^ 24 = 16777216 by norm_num] using fmt.rho_le
  have heta1 : fmt.interchange.format.minSubnormal ≤ 1 := by
    rw [(format_parameters fmt).2]; cases fmt <;> norm_num [Format.leastSubnormal]
  obtain ⟨score,hscore,_,hscoreB⟩ := direct_candidate_score fmt.interchange ht hE hR hD
    (by simpa only [add_comm] using hfinal) hrmax heta1 hlim hqlim
  refine ⟨score,hscore,?_⟩
  simp only [(format_parameters fmt).1,(format_parameters fmt).2] at hscoreB
  rw [add_comm ((t : ℝ) • realVec e) (realVec r)] at hscoreB
  have hbudget := fmt.kernel_absolute_budget hD
  have hnormE := norm_nonneg (realVec e)
  have hfloor := fourthRoot_nonneg fmt.leastSubnormal
  have hrel0 := mul_nonneg fmt.rho_nonneg hD
  by_cases hlarge : fourthRoot fmt.leastSubnormal < ‖realVec e‖
  · obtain ⟨s,hs,_,_,hloss⟩ := direct_solve_admissible fmt hone hE hR hL hadm hlarge hDL heD hrD heC hrC
    have hst : s = t := Option.some.inj (hs.symm.trans ht)
    subst s
    have hdist := squared_loss_norm fmt.subnormal_nonneg hnormE (by
      simpa only [(format_parameters fmt).1,(format_parameters fmt).2] using hloss v hv0 hv1)
    have hscale := mul_le_mul_of_nonneg_left heD (show 0 ≤ 8 * Real.sqrt fmt.leastSubnormal by positivity)
    nlinarith only [hscoreB,hdist,hscale,hbudget,hfloor,hrel0,fmt.subnormal_nonneg]
  · have hshort := short_direction_norm (R := realVec r) ht0r ht1r hv0 hv1 (le_of_not_gt hlarge)
    have hh : ‖realVec r + v • realVec e‖ ≤ hypot ‖realVec r + v • realVec e‖ ((419 / 50) * fmt.rho * D) := by
      have h := hypot_sq ‖realVec r + v • realVec e‖ ((419 / 50) * fmt.rho * D)
      nlinarith only [h,hypot_nonneg ‖realVec r + v • realVec e‖ ((419 / 50) * fmt.rho * D),
        norm_nonneg (realVec r + v • realVec e),sq_nonneg ((419 / 50) * fmt.rho * D)]
    have hsqr := Real.sqrt_nonneg fmt.leastSubnormal
    have hprod := mul_nonneg hsqr (show 0 ≤ 1 + D by positivity)
    nlinarith only [hscoreB,hshort,hh,hbudget,hprod,hrel0,fmt.subnormal_nonneg]

/-- Uniform actual endpoint candidate upper bound, with the short-Q branch
covering every result of the NaN-aware clamp. -/
theorem endpoint_candidate_upper (fmt : Format)
    {Pw Qw Rw : Vec3 fmt.interchange} {p q r : Fin 3 → ℚ} {D L v : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hP : ∀ i, value? fmt.interchange (Pw i) = some (p i))
    (hQ : ∀ i, value? fmt.interchange (Qw i) = some (q i))
    (hR : ∀ i, value? fmt.interchange (Rw i) = some (r i))
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite / 4)
    (hDL : D ≤ 9 * L) (hpD : ‖realVec p‖ ≤ D) (hqD : ‖realVec q‖ ≤ D) (hrD : ‖realVec r‖ ≤ D)
    (hkD : ‖realVec r - realVec p‖ ≤ D)
    (hkQ : ‖(realVec r - realVec p) + realVec q‖ ≤ D)
    (hpC : ∀ i, |(p i : ℝ)| ≤ D / Real.sqrt 3)
    (hqC : ∀ i, |(q i : ℝ)| ≤ D / Real.sqrt 3)
    (hrC : ∀ i, |(r i : ℝ)| ≤ D / Real.sqrt 3)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    let tw := clamp01nan fmt.interchange (div fmt.interchange
      (sub fmt.interchange (dot3 fmt.interchange Pw Qw) (dot3 fmt.interchange Qw Rw))
      (dot3 fmt.interchange Qw Qw))
    let rw := fma3 fmt.interchange tw Qw (vsub fmt.interchange Rw Pw)
    UpperSelection.Upper fmt.interchange
      (hypot ‖(realVec r - realVec p) + v • realVec q‖ ((419 / 50) * fmt.rho * D) +
        (177 / 50) * fmt.rho * D + 2 * fourthRoot fmt.leastSubnormal)
      (dot3 fmt.interchange rw rw) := by
  dsimp only
  obtain ⟨t, ht, ht0, ht1⟩ := clamp01nan_bounded fmt.interchange hone
    (div fmt.interchange (sub fmt.interchange (dot3 fmt.interchange Pw Qw) (dot3 fmt.interchange Qw Rw))
      (dot3 fmt.interchange Qw Qw))
  have ht0r : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht0
  have ht1r : (t : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hD : 0 ≤ D := (norm_nonneg _).trans hqD
  have hfinal := segment_norm_bound ht0r ht1r hkD hkQ
  obtain ⟨hlim,hqlim⟩ := evaluation_ranges fmt hD hDL hadm
  have hrmax : fmt.interchange.format.unitRoundoff ≤ 1 / 16777216 := by
    rw [(format_parameters fmt).1]; simpa only [show (2 : ℝ) ^ 24 = 16777216 by norm_num] using fmt.rho_le
  have heta1 : fmt.interchange.format.minSubnormal ≤ 1 := by
    rw [(format_parameters fmt).2]; cases fmt <;> norm_num [Format.leastSubnormal]
  obtain ⟨score,hscore,_,hscoreB⟩ := endpoint_candidate_score fmt.interchange ht hP hQ hR hD hkD
    (by simpa only [add_comm] using hfinal) hrmax heta1 hlim hqlim
  refine ⟨score,hscore,?_⟩
  simp only [(format_parameters fmt).1,(format_parameters fmt).2] at hscoreB
  rw [add_comm ((t : ℝ) • realVec q) (realVec r - realVec p)] at hscoreB
  have hbudget := fmt.kernel_absolute_budget hD
  have hnormQ := norm_nonneg (realVec q)
  have hfloor := fourthRoot_nonneg fmt.leastSubnormal
  have hrel0 := mul_nonneg fmt.rho_nonneg hD
  by_cases hlarge : fourthRoot fmt.leastSubnormal < ‖realVec q‖
  · obtain ⟨s,hs,_,_,hloss⟩ := endpoint_solve_admissible fmt hone hP hQ hR hL hadm hlarge hDL hpD hqD hrD hkD hpC hqC hrC
    have hst : s = t := Option.some.inj (hs.symm.trans ht)
    subst s
    have hdist := squared_loss_norm fmt.subnormal_nonneg hnormQ (by
      simpa only [(format_parameters fmt).1,(format_parameters fmt).2] using hloss v hv0 hv1)
    have hscale := mul_le_mul_of_nonneg_left hqD (show 0 ≤ 8 * Real.sqrt fmt.leastSubnormal by positivity)
    nlinarith only [hscoreB,hdist,hscale,hbudget,hfloor,hrel0,fmt.subnormal_nonneg]
  · have hshort := short_direction_norm ht0r ht1r hv0 hv1 (le_of_not_gt hlarge)
      (R := realVec r - realVec p)
    have hh : ‖(realVec r - realVec p) + v • realVec q‖ ≤
        hypot ‖(realVec r - realVec p) + v • realVec q‖ ((419 / 50) * fmt.rho * D) := by
      have h := hypot_sq ‖(realVec r - realVec p) + v • realVec q‖ ((419 / 50) * fmt.rho * D)
      nlinarith only [h,hypot_nonneg ‖(realVec r - realVec p) + v • realVec q‖ ((419 / 50) * fmt.rho * D),
        norm_nonneg ((realVec r - realVec p) + v • realVec q),sq_nonneg ((419 / 50) * fmt.rho * D)]
    have hsqr := Real.sqrt_nonneg fmt.leastSubnormal
    have hprod := mul_nonneg hsqr (show 0 ≤ 1 + D by positivity)
    nlinarith only [hscoreB,hshort,hh,hbudget,hprod,hrel0,fmt.subnormal_nonneg]

end DistanceAccuracy.ProjectionRounding

import DistanceAccuracy.LocalProjectionUpper

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant OperationBounds DotWordBounds
set_option exponentiation.threshold 2048

/-- The AC/BC numerator uses dot(R,E), in the implementation's original
operand order. Its actual scalar schedule is bounded directly. -/
theorem direct_solve_admissible_swapped (fmt : Format)
    {Ew Rw : Vec3 fmt.interchange} {e r : Fin 3 → ℚ} {D L : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hE : ∀ i, value? fmt.interchange (Ew i) = some (e i))
    (hR : ∀ i, value? fmt.interchange (Rw i) = some (r i))
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite / 4)
    (hA : fourthRoot fmt.leastSubnormal < ‖realVec e‖) (hDL : D ≤ 9*L)
    (heD : ‖realVec e‖ ≤ D) (hrD : ‖realVec r‖ ≤ D)
    (heC : ∀ i, |(e i : ℝ)| ≤ D/Real.sqrt 3)
    (hrC : ∀ i, |(r i : ℝ)| ≤ D/Real.sqrt 3) :
    ∃ s : ℚ, value? fmt.interchange (clamp01nan fmt.interchange
      (div fmt.interchange (neg fmt.interchange (dot3 fmt.interchange Rw Ew)) (dot3 fmt.interchange Ew Ew))) = some s ∧
      0 ≤ s ∧ s ≤ 1 ∧ ∀ sstar : ℝ, 0 ≤ sstar → sstar ≤ 1 →
      ‖realVec r+(s : ℝ)•realVec e‖^2 ≤ ‖realVec r+sstar•realVec e‖^2+
        ((419/50)*fmt.interchange.format.unitRoundoff*D)^2+
        64*fmt.interchange.format.minSubnormal*(1+‖realVec e‖^2) := by
  obtain ⟨a, _, _, ha, _, _, hap, haErr, haSharp, _, _, _, _⟩ :=
    three_dots_admissible fmt hE hE hR hL hadm hA hDL heD heD hrD heC heC hrC
  have hD : 0 ≤ D := (norm_nonneg _).trans heD
  have hr := fmt.interchange.format.unitRoundoff_pos.le
  have hrmax : fmt.interchange.format.unitRoundoff ≤ 1 / 16777216 := by
    rw [(format_parameters fmt).1]; simpa only [show (2 : ℝ) ^ 24 = 16777216 by norm_num] using fmt.rho_le
  have heta1 : fmt.interchange.format.minSubnormal ≤ 1 := by
    rw [(format_parameters fmt).2]; cases fmt <;> norm_num [Format.leastSubnormal]
  let B := D ^ 2 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hetaB : fmt.interchange.format.minSubnormal ≤ B := by dsimp [B]; nlinarith only [heta1,sq_nonneg D]
  have hsqrt : 1 ≤ Real.sqrt (3 : ℝ) := by apply (Real.le_sqrt (by norm_num) (by norm_num)).2; norm_num
  have hdiv : D / Real.sqrt 3 ≤ D := div_le_self hD hsqrt
  have hprod : ∀ i, |(r i : ℝ) * (e i : ℝ)| ≤ B := by
    intro i
    rw [abs_mul]
    have h := mul_le_mul ((hrC i).trans hdiv) ((heC i).trans hdiv) (abs_nonneg _) hD
    dsimp [B]
    nlinarith only [h]
  have hBmax : 6 * B < fmt.interchange.format.overflowThreshold := by
    have h := fmt.quadratic_range hL hadm
    have hs : D ^ 2 ≤ (9 * L) ^ 2 := by gcongr
    dsimp [B]
    nlinarith only [h,hs,sq_nonneg L]
  obtain ⟨d, hd, hdErr⟩ := dot3_finite_weighted fmt.interchange hR hE hB hprod hetaB (by linarith only [hrmax]) hBmax
  change |(d : ℝ) - scalarDot r e| ≤ _ at hdErr
  rw [scalarDot_inner, real_inner_comm (realVec e) (realVec r)] at hdErr
  have hgeom := weighted_general_scaled hD (a := realVec e) (b := realVec r) hrC
  have hscale := mul_le_mul_of_nonneg_left hgeom
    (show 0 ≤ fmt.interchange.format.unitRoundoff * (1 + fmt.interchange.format.unitRoundoff) ^ 2 by positivity)
  have hdSharp : |(d : ℝ) - inner ℝ (realVec e) (realVec r)| ≤
      (2161 / 1000) * fmt.interchange.format.unitRoundoff * (‖realVec e‖ * D) *
        (1 + fmt.interchange.format.unitRoundoff) ^ 2 + 2 * fmt.interchange.format.minSubnormal := by
    dsimp [realVec] at hscale hdErr ⊢
    have h0 : (r 0 : ℝ) * (e 0 : ℝ) = (e 0 : ℝ) * (r 0 : ℝ) := mul_comm _ _
    have h1 : (r 1 : ℝ) * (e 1 : ℝ) = (e 1 : ℝ) * (r 1 : ℝ) := mul_comm _ _
    have h2 : (r 2 : ℝ) * (e 2 : ℝ) = (e 2 : ℝ) * (r 2 : ℝ) := mul_comm _ _
    rw [h0,h1,h2] at hdErr
    nlinarith only [hscale,hdErr]
  obtain ⟨s,hs,hs0,hs1⟩ := clamp01nan_bounded fmt.interchange hone
    (div fmt.interchange (neg fmt.interchange (dot3 fmt.interchange Rw Ew)) (dot3 fmt.interchange Ew Ew))
  have hne : realVec e ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (fourthRoot_nonneg _) hA)
  have hlim1 : (1 : ℝ) < fmt.interchange.format.overflowThreshold := by
    have h := fmt.quadratic_range hL hadm
    nlinarith only [h,sq_nonneg L]
  refine ⟨s,hs,hs0,hs1,?_⟩
  intro sstar hsstar0 hsstar1
  exact direct_word_projection_loss fmt.interchange hone ha hd hs hap hne hD heD hrD
    (by exact_mod_cast hs0) (by exact_mod_cast hs1) hsstar0 hsstar1 hrmax hlim1 haErr haSharp hdSharp

/-- Actual swapped-operand AC/BC candidate upper bound, including short directions. -/
theorem direct_candidate_upper_swapped (fmt : Format)
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
      (neg fmt.interchange (dot3 fmt.interchange Rw Ew)) (dot3 fmt.interchange Ew Ew))
    let rw := fma3 fmt.interchange tw Ew Rw
    UpperSelection.Upper fmt.interchange
      (hypot ‖realVec r + v • realVec e‖ ((419 / 50) * fmt.rho * D) +
        (127 / 50) * fmt.rho * D + 2 * fourthRoot fmt.leastSubnormal)
      (dot3 fmt.interchange rw rw) := by
  dsimp only
  let tw := clamp01nan fmt.interchange (div fmt.interchange
    (neg fmt.interchange (dot3 fmt.interchange Rw Ew)) (dot3 fmt.interchange Ew Ew))
  obtain ⟨t, ht, ht0, ht1⟩ := clamp01nan_bounded fmt.interchange hone
    (div fmt.interchange (neg fmt.interchange (dot3 fmt.interchange Rw Ew)) (dot3 fmt.interchange Ew Ew))
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
  · obtain ⟨s,hs,_,_,hloss⟩ := direct_solve_admissible_swapped fmt hone hE hR hL hadm hlarge hDL heD hrD heC hrC
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


end DistanceAccuracy.ProjectionRounding

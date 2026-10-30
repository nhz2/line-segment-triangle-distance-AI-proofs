import DistanceAccuracy.CrossingHeight
import DistanceAccuracy.FaceRanges

/-! Admissible-coordinate range discharge for compensated crossing normals
    and the two plane dot products. -/
namespace DistanceAccuracy.CrossingHeight
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds
open Determinant
set_option exponentiation.threshold 2048
set_option maxHeartbeats 1000000

lemma cubic_range (fmt : Format) {L : ℝ} (hL : 0 ≤ L)
    (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4) :
    10000*L^3+32 < fmt.interchange.format.overflowThreshold := by
  have hc := fmt.admissible_coordinate_ceiling hadm
  have hp : L^3 ≤ fmt.coordinateCeiling^3 := by gcongr
  have hh : 10000*fmt.coordinateCeiling^3+32 < fmt.interchange.format.overflowThreshold := by
    cases fmt <;> norm_num [Format.interchange, Format.coordinateCeiling, fp32, fp64,
      FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.overflowThreshold]
  linarith

lemma quadratic_range (fmt : Format) {L : ℝ} (hL : 0 ≤ L)
    (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4) :
    1000*L^2+32 < fmt.interchange.format.overflowThreshold := by
  have hc := fmt.admissible_coordinate_ceiling hadm
  have hp : L^2 ≤ fmt.coordinateCeiling^2 := by gcongr
  have hh : 1000*fmt.coordinateCeiling^2+32 < fmt.interchange.format.overflowThreshold := by
    cases fmt <;> norm_num [Format.interchange, Format.coordinateCeiling, fp32, fp64,
      FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.overflowThreshold]
  linarith

/-- All range and subnormal premises for the concrete plane crossing follow
    from admissible coordinates and a compensated-normal error bound. -/
theorem word_crossing_admissible (fmt : Format)
    {Mw APw Pw : Vec3 fmt.interchange} {m ap p : Fin 3 → ℚ}
    {N : Geometry.E3} {L D t : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hM : ∀ k, value? fmt.interchange (Mw k) = some (m k))
    (hAPw : ∀ k, value? fmt.interchange (APw k) = some (ap k))
    (hPw : ∀ k, value? fmt.interchange (Pw k) = some (p k))
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hD : 0 < D) (hDL : D ≤ 9*L)
    (hNbound : ‖N‖ ≤ D^2)
    (hNfloor : (fourthRoot fmt.leastSubnormal)^2 ≤ ‖N‖)
    (hnormal : ‖realVec m-N‖/‖N‖ ≤ (2037/1000)*fmt.rho+4*(fourthRoot fmt.leastSubnormal)^2)
    (hAP : ‖realVec ap‖ ≤ D) (hP : ‖realVec p‖ ≤ D)
    (hAX : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ‖realVec ap-s•realVec p‖ ≤ D)
    (hAPC : ∀ k, |(ap k : ℝ)| ≤ D/Real.sqrt 3)
    (hPC : ∀ k, |(p k : ℝ)| ≤ D/Real.sqrt 3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hroot : inner ℝ N (realVec ap-t•realVec p) = 0) :
    ∃ s : ℚ, ∃ ax : Fin 3 → ℚ,
      value? fmt.interchange (clamp01nan fmt.interchange
        (div fmt.interchange (dot3 fmt.interchange Mw APw) (dot3 fmt.interchange Mw Pw))) = some s ∧
      (∀ k, value? fmt.interchange (fma3 fmt.interchange
        (neg fmt.interchange (clamp01nan fmt.interchange
          (div fmt.interchange (dot3 fmt.interchange Mw APw) (dot3 fmt.interchange Mw Pw)))) Pw APw k) = some (ax k)) ∧
      0 ≤ s ∧ s ≤ 1 ∧ |inner ℝ N (realVec ax)|/‖N‖ ≤
        (42/5)*fmt.interchange.format.unitRoundoff*D+fourthRoot fmt.leastSubnormal := by
  let h := fourthRoot fmt.leastSubnormal
  let B := 2*D^3+1
  have hρ : fmt.interchange.format.unitRoundoff = fmt.rho := by
    cases fmt
    · exact fp32_parameters.1
    · exact fp64_parameters.1
  have hη : fmt.interchange.format.minSubnormal = fmt.leastSubnormal := by
    cases fmt
    · exact fp32_parameters.2.2
    · exact fp64_parameters.2.2
  obtain ⟨hlp, hl, hhmax⟩ := FaceRanges.root_bounds fmt
  have hh : 0 < h := hlp.trans_le hl
  have hpow : h^4 = fmt.leastSubnormal := fourthRoot_pow_four fmt.subnormal_nonneg
  have hsquare : h^2 = Real.sqrt fmt.leastSubnormal := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hN : 0 < ‖N‖ := (sq_pos_of_pos hh).trans_le hNfloor
  have hρ0 := fmt.rho_nonneg
  have hρmax : fmt.interchange.format.unitRoundoff ≤ 1/16777216 := by
    rw [hρ]; have hh := fmt.rho_le; norm_num at hh; exact hh
  have habs : 1000000*h^2 ≤ fmt.rho := by rw [hsquare]; exact fmt.sqrt_eta_absorption
  have hnorm : ‖realVec m-N‖ ≤ (2038/1000)*fmt.interchange.format.unitRoundoff*‖N‖ := by
    have hh := (div_le_iff₀ hN).mp hnormal
    have hc : (2037/1000)*fmt.rho+4*h^2 ≤ (2038/1000)*fmt.rho := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hc hN.le
    rw [hρ]
    exact hh.trans hm
  have hMn : ‖realVec m‖ ≤ 2*D^2 := by
    have ht := norm_add_le (realVec m-N) N
    rw [sub_add_cancel] at ht
    have hcoef : (2038/1000)*fmt.interchange.format.unitRoundoff ≤ 1 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hcoef hN.le
    nlinarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hη1 : fmt.leastSubnormal ≤ 1 := by cases fmt <;> norm_num [Format.leastSubnormal]
  have hηB : fmt.interchange.format.minSubnormal ≤ B := by rw [hη]; dsimp [B]; nlinarith [pow_nonneg hD.le 3]
  have hsqrt : 1 ≤ Real.sqrt (3:ℝ) := by apply (Real.le_sqrt (by norm_num) (by norm_num)).2; norm_num
  have hdiv := div_le_self hD.le hsqrt
  have hproducts (w : Fin 3 → ℚ) (hw : ∀ k, |(w k : ℝ)| ≤ D/Real.sqrt 3) :
      ∀ k, |(m k : ℝ)*(w k : ℝ)| ≤ B := by
    intro k
    have hm : |(m k : ℝ)| ≤ ‖realVec m‖ := by
      have hh := PiLp.norm_apply_le (realVec m) k
      change ‖(m k : ℝ)‖ ≤ ‖realVec m‖ at hh
      rw [Real.norm_eq_abs] at hh
      exact hh
    have hp := mul_le_mul (hm.trans hMn) ((hw k).trans hdiv) (abs_nonneg _) (by positivity : 0 ≤ 2*D^2)
    rw [abs_mul]; dsimp [B]; nlinarith
  have hBmax : 6*B < fmt.interchange.format.overflowThreshold := by
    have hc := cubic_range fmt hL hadm
    have hp : D^3 ≤ (9*L)^3 := by gcongr
    dsimp [B]; nlinarith [pow_nonneg hL 3]
  have hlin : 2*D < fmt.interchange.format.overflowThreshold := by
    have hh := fmt.linear_range hL hadm
    linarith
  have honeMax : (1:ℝ) < fmt.interchange.format.overflowThreshold := by
    have hh := fmt.quadratic_range hL hadm
    nlinarith [sq_nonneg L]
  have hetaH : fmt.interchange.format.minSubnormal ≤ h^2 := by
    rw [hη, ← hpow]
    have hhmax' : h ≤ 1/8 := hhmax
    have hs : h^2 ≤ (1/8:ℝ)^2 := (sq_le_sq₀ hh.le (by norm_num)).2 hhmax'
    nlinarith [mul_nonneg (sq_nonneg h) (show 0 ≤ 1-h^2 by nlinarith)]
  have hetaSmall : fmt.interchange.format.minSubnormal ≤ fmt.interchange.format.unitRoundoff/1000000 := by
    rw [hρ]; nlinarith
  have hetaFloor : fmt.interchange.format.minSubnormal ≤ h^2*‖N‖ := by
    rw [hη, ← hpow]
    have hm := mul_le_mul_of_nonneg_left hNfloor (sq_nonneg h)
    nlinarith
  obtain ⟨s, ax, hs, hax, hs0, hs1, height⟩ := word_crossing_height fmt.interchange
    hone hM hAPw hPw hD hN hnorm hAP hP hAX hAPC hPC hB (hproducts ap hAPC) (hproducts p hPC)
    hηB hBmax honeMax hρmax hetaSmall hetaFloor ht0 ht1 hroot hlin hetaH
  refine ⟨s, ax, hs, hax, hs0, hs1, height.trans ?_⟩
  have hhmax' : h ≤ 1/8 := hhmax
  have hm := mul_le_mul_of_nonneg_left hhmax' hh.le
  change (42/5)*fmt.interchange.format.unitRoundoff*D+6*h^2 ≤ (42/5)*fmt.interchange.format.unitRoundoff*D+h
  nlinarith

lemma cross_norm_le {E F : Geometry.E3} {D : ℝ} (hD : 0 ≤ D)
    (hE : ‖E‖ ≤ D) (hF : ‖F‖ ≤ D) : ‖exactCross E F‖ ≤ D^2 := by
  have hid : ‖exactCross E F‖^2 = ‖E‖^2*‖F‖^2-(inner ℝ E F)^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
      exactCross, dotProduct, Fin.sum_univ_succ]
    ring
  have he := (sq_le_sq₀ (norm_nonneg E) hD).2 hE
  have hf := (sq_le_sq₀ (norm_nonneg F) hD).2 hF
  have hp := mul_le_mul he hf (sq_nonneg _) (sq_nonneg _)
  nlinarith [norm_nonneg (exactCross E F), sq_nonneg D, sq_nonneg (inner ℝ E F)]

/-- Complete compensated-normal crossing height theorem. Every computed
    quantity is an actual IEEE word; all no-overflow and local error bounds
    are derived from admissible coordinates and geometric thick-branch tests. -/
theorem word_crossing_thick (fmt : Format)
    {Ew Fw APw Pw : Vec3 fmt.interchange} {e f ap p : Fin 3 → ℚ} {L D t : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hEw : ∀ k, value? fmt.interchange (Ew k) = some (e k))
    (hFw : ∀ k, value? fmt.interchange (Fw k) = some (f k))
    (hAPw : ∀ k, value? fmt.interchange (APw k) = some (ap k))
    (hPw : ∀ k, value? fmt.interchange (Pw k) = some (p k))
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hD : 0 < D) (hDL : D ≤ 9*L)
    (hE0 : 0 < ‖realVec e‖) (hE : ‖realVec e‖ ≤ D) (hF : ‖realVec f‖ ≤ D)
    (hEC : ∀ k, |(e k : ℝ)| ≤ D/Real.sqrt 3)
    (hFC : ∀ k, |(f k : ℝ)| ≤ D/Real.sqrt 3)
    (hfloor : (fourthRoot fmt.leastSubnormal)^2 ≤ ‖exactCross (realVec e) (realVec f)‖)
    (hthick : 16*fmt.interchange.format.unitRoundoff*‖realVec e‖*D ≤ ‖exactCross (realVec e) (realVec f)‖)
    (hAP : ‖realVec ap‖ ≤ D) (hP : ‖realVec p‖ ≤ D)
    (hAX : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ‖realVec ap-s•realVec p‖ ≤ D)
    (hAPC : ∀ k, |(ap k : ℝ)| ≤ D/Real.sqrt 3)
    (hPC : ∀ k, |(p k : ℝ)| ≤ D/Real.sqrt 3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hroot : inner ℝ (exactCross (realVec e) (realVec f)) (realVec ap-t•realVec p) = 0) :
    let Mw := cross3Accurate fmt.interchange Ew Fw
    ∃ s : ℚ, ∃ ax : Fin 3 → ℚ,
      value? fmt.interchange (clamp01nan fmt.interchange
        (div fmt.interchange (dot3 fmt.interchange Mw APw) (dot3 fmt.interchange Mw Pw))) = some s ∧
      (∀ k, value? fmt.interchange (fma3 fmt.interchange
        (neg fmt.interchange (clamp01nan fmt.interchange
          (div fmt.interchange (dot3 fmt.interchange Mw APw) (dot3 fmt.interchange Mw Pw)))) Pw APw k) = some (ax k)) ∧
      0 ≤ s ∧ s ≤ 1 ∧ |inner ℝ (exactCross (realVec e) (realVec f)) (realVec ax)|/
        ‖exactCross (realVec e) (realVec f)‖ ≤
        (42/5)*fmt.interchange.format.unitRoundoff*D+fourthRoot fmt.leastSubnormal := by
  let P := D^2+1
  have hρ : fmt.interchange.format.unitRoundoff = fmt.rho := by
    cases fmt
    · exact fp32_parameters.1
    · exact fp64_parameters.1
  have hη : fmt.interchange.format.minSubnormal = fmt.leastSubnormal := by
    cases fmt
    · exact fp32_parameters.2.2
    · exact fp64_parameters.2.2
  have hρmax : fmt.interchange.format.unitRoundoff ≤ 1/16777216 := by
    rw [hρ]; have hh := fmt.rho_le; norm_num at hh; exact hh
  obtain ⟨hlp, hl, _⟩ := FaceRanges.root_bounds fmt
  have hh : 0 < fourthRoot fmt.leastSubnormal := hlp.trans_le hl
  have hPpos : 0 < P := by dsimp [P]; positivity
  have heta : fmt.interchange.format.minSubnormal ≤ P := by
    have hh : fmt.leastSubnormal ≤ 1 := by cases fmt <;> norm_num [Format.leastSubnormal]
    rw [hη]; dsimp [P]; nlinarith [sq_nonneg D]
  have hsqrt : 1 ≤ Real.sqrt (3:ℝ) := by apply (Real.le_sqrt (by norm_num) (by norm_num)).2; norm_num
  have hdiv := div_le_self hD.le hsqrt
  have hprod : ∀ i j, |(e i : ℝ)*(f j : ℝ)| ≤ P := by
    intro i j
    have hm := mul_le_mul ((hEC i).trans hdiv) ((hFC j).trans hdiv) (abs_nonneg _) hD.le
    rw [abs_mul]; dsimp [P]; nlinarith
  have hPmax : 10*P < fmt.interchange.format.overflowThreshold := by
    have hc := quadratic_range fmt hL hadm
    have hp : D^2 ≤ (9*L)^2 := by gcongr
    dsimp [P]; nlinarith [sq_nonneg L]
  have hpow : fmt.interchange.format.minSubnormal = (fourthRoot fmt.leastSubnormal)^4 := by
    rw [hη]; exact (fourthRoot_pow_four fmt.subnormal_nonneg).symm
  obtain ⟨m, hm, hnormal⟩ := word_cross3Accurate_thick fmt.interchange hEw hFw hD hFC
    hPpos hprod heta hρmax hPmax hE0 hh hpow hfloor hthick
  apply word_crossing_admissible fmt hone hm hAPw hPw hL hadm hD hDL
    (cross_norm_le hD.le hE hF) hfloor _ hAP hP hAX hAPC hPC ht0 ht1 hroot
  simpa only [hρ] using hnormal

end DistanceAccuracy.CrossingHeight

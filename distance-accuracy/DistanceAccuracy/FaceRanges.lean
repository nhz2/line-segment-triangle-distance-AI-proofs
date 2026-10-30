import DistanceAccuracy.FormatRange
import DistanceAccuracy.ReconstructionIEEE

/-! Range discharge for the non-small face edge and its reciprocal solve. -/
namespace DistanceAccuracy.FaceRanges
open FP.IEEE FP.IEEE.Interchange
set_option exponentiation.threshold 2048
set_option maxHeartbeats 1000000

noncomputable def rootLower : Format → ℝ
  | .binary32 => 1/2^38
  | .binary64 => 1/2^269

lemma root_bounds (f : Format) :
    0 < rootLower f ∧ rootLower f ≤ fourthRoot f.leastSubnormal ∧
      fourthRoot f.leastSubnormal ≤ 1/8 := by
  refine ⟨?_, ?_, ?_⟩
  · cases f <;> norm_num [rootLower]
  · apply (pow_le_pow_iff_left₀ (by cases f <;> norm_num [rootLower]) (fourthRoot_nonneg _) (by decide : (4:ℕ) ≠ 0)).mp
    rw [fourthRoot_pow_four f.subnormal_nonneg]
    cases f <;> norm_num [rootLower, Format.leastSubnormal]
  · apply (pow_le_pow_iff_left₀ (fourthRoot_nonneg _) (by norm_num : (0:ℝ) ≤ 1/8) (by decide : (4:ℕ) ≠ 0)).mp
    rw [fourthRoot_pow_four f.subnormal_nonneg]
    cases f <;> norm_num [Format.leastSubnormal]

lemma eta_small {h A eta : ℝ} (hh : 0 ≤ h) (hhmax : h ≤ 1/8)
    (he : eta = h^4) (hA : h < A) : eta ≤ A^2/8 := by
  have hsq : h^2 ≤ (1/8:ℝ)^2 := (sq_le_sq₀ hh (by norm_num)).2 hhmax
  have hsqA : h^2 ≤ A^2 := (sq_le_sq₀ hh (by linarith)).2 hA.le
  have hprod := mul_nonneg (sq_nonneg h) (show 0 ≤ 1/8-h^2 by nlinarith)
  nlinarith

lemma dot_coefficient {rho : ℝ} (hr : 0 ≤ rho) (hrmax : rho ≤ 1/1024) :
    3*rho*(1+rho)^2 ≤ 1/4 := by
  have hs : rho^2 ≤ (1/1024:ℝ)^2 := (sq_le_sq₀ hr (by norm_num)).2 hrmax
  have hc := mul_le_mul_of_nonneg_left hs hr
  nlinarith

lemma self_dot_half {rho eta A a : ℝ} (hr : 0 ≤ rho) (hrmax : rho ≤ 1/1024)
    (heta : eta ≤ A^2/8)
    (ha : |a-A^2| ≤ 3*rho*(1+rho)^2*A^2+2*eta) :
    |a-A^2| ≤ A^2/2 ∧ A^2/2 ≤ a ∧ a ≤ 3*A^2/2 := by
  have hc := mul_le_mul_of_nonneg_right (dot_coefficient hr hrmax) (sq_nonneg A)
  have he : |a-A^2| ≤ A^2/2 := by nlinarith
  exact ⟨he, by have hh := (abs_le.mp he).1; linarith,
    by have hh := (abs_le.mp he).2; linarith⟩

lemma coefficient_normalized {rho eta h A D a b exact : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/1024) (hh : 0 < h) (hhmax : h ≤ 1)
    (hA : h < A) (hD : A ≤ D) (heta : eta ≤ A^2/8) (ha : A^2/2 ≤ a)
    (hb : |b-exact| ≤ 3*rho*(1+rho)^2*A*D+2*eta) (he : |exact| ≤ A*D) :
    |b| ≤ a*(16*(D+1)/h) := by
  have hA0 : 0 < A := hh.trans hA
  have hD0 : 0 < D := hA0.trans_le hD
  have ha0 : 0 < a := by nlinarith
  have hc := mul_le_mul_of_nonneg_right (dot_coefficient hr hrmax) (mul_nonneg hA0.le hD0.le)
  have habs := abs_add_le (b-exact) exact
  rw [sub_add_cancel] at habs
  have hAD : A^2 ≤ A*D := by nlinarith
  have hbb : |b| ≤ 2*A*D := by nlinarith
  have hratio : 2*A*D*h ≤ a*(16*(D+1)) := by
    have hhA := mul_le_mul_of_nonneg_left hA.le (show 0 ≤ 2*A*D by positivity)
    have haa := mul_le_mul_of_nonneg_right ha (show 0 ≤ 4*D by positivity)
    nlinarith
  have hd : 2*A*D ≤ a*(16*(D+1)/h) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hh).2 hratio
  exact hbb.trans hd

/-- The face range package derives all scalar safety premises from the
    self-dot error and the input coordinate bound. -/
theorem face_ranges (f : Format) {L A D a b d be de : ℝ}
    (hL : 0 ≤ L) (hadm : L < fourthRoot f.interchange.format.maxFinite/4)
    (hA : fourthRoot f.leastSubnormal < A) (hAD : A ≤ D) (hD : D ≤ 9*L)
    (ha : |a-A^2| ≤ 3*f.rho*(1+f.rho)^2*A^2+2*f.leastSubnormal)
    (hb : |b-be| ≤ 3*f.rho*(1+f.rho)^2*A*D+2*f.leastSubnormal)
    (hd : |d-de| ≤ 3*f.rho*(1+f.rho)^2*A*D+2*f.leastSubnormal)
    (hbe : |be| ≤ A*D) (hde : |de| ≤ A*D) :
    let T := 16*(D+1)/fourthRoot f.leastSubnormal
    f.leastSubnormal ≤ A^2/8 ∧ 0 < a ∧ |a-A^2| ≤ A^2 ∧
    f.interchange.format.minNormal ≤ 1/a ∧ 1/a < f.interchange.format.overflowThreshold ∧
    0 < T ∧ |b| ≤ a*T ∧ |d| ≤ a*T ∧ f.leastSubnormal ≤ T ∧
    8*T < f.interchange.format.overflowThreshold := by
  dsimp only
  obtain ⟨hlp, hl, hhmax⟩ := root_bounds f
  have hh : 0 < fourthRoot f.leastSubnormal := hlp.trans_le hl
  have hA0 : 0 < A := hh.trans hA
  have hD0 : 0 < D := hA0.trans_le hAD
  have hρ := f.rho_nonneg
  have hρmax : f.rho ≤ 1/1024 := by have h := f.rho_le; norm_num at h; linarith
  have heta := eta_small hh.le hhmax (fourthRoot_pow_four f.subnormal_nonneg).symm hA
  obtain ⟨haErr, haLower, haUpper⟩ := self_dot_half hρ hρmax heta ha
  have ha0 : 0 < a := by nlinarith
  have hc := f.admissible_coordinate_ceiling hadm
  have hLsq : L^2 ≤ f.coordinateCeiling^2 := (sq_le_sq₀ hL f.coordinateCeiling_nonneg).2 hc
  have hN : 0 < f.interchange.format.minNormal := by
    cases f <;> norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.minNormal]
  have hNrange : f.interchange.format.minNormal*(200*f.coordinateCeiling^2+2) ≤ 1 := by
    cases f <;> norm_num [Format.interchange, Format.coordinateCeiling, fp32, fp64,
      FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.minNormal]
  have haBound : a ≤ 200*f.coordinateCeiling^2+2 := by
    have hAsq : A^2 ≤ (9*L)^2 := (sq_le_sq₀ hA0.le (by positivity)).2 (hAD.trans hD)
    nlinarith
  have hn : f.interchange.format.minNormal ≤ 1/a := by
    apply (le_div_iff₀ ha0).2
    have hm := mul_le_mul_of_nonneg_left haBound hN.le
    nlinarith
  have hover : 0 < f.interchange.format.overflowThreshold := by
    cases f <;> norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32,
      FP.IEEE.binary64, FP.IEEE.Format.overflowThreshold]
  have hrecipBudget : 2 < f.interchange.format.overflowThreshold*(rootLower f)^2 := by
    cases f <;> norm_num [Format.interchange, rootLower, fp32, fp64, FP.IEEE.binary32,
      FP.IEEE.binary64, FP.IEEE.Format.overflowThreshold]
  have hrootSq : (rootLower f)^2 ≤ A^2 := (sq_le_sq₀ hlp.le hA0.le).2 (hl.trans hA.le)
  have hrecip : 1/a < f.interchange.format.overflowThreshold := by
    apply (div_lt_iff₀ ha0).2
    have hm := mul_le_mul_of_nonneg_left hrootSq hover.le
    have hm' := mul_le_mul_of_nonneg_left haLower hover.le
    nlinarith
  have hTpos : 0 < 16*(D+1)/fourthRoot f.leastSubnormal := by positivity
  have hbT := coefficient_normalized hρ hρmax hh (by linarith) hA hAD heta haLower hb hbe
  have hdT := coefficient_normalized hρ hρmax hh (by linarith) hA hAD heta haLower hd hde
  have hη1 : f.leastSubnormal ≤ 1 := by cases f <;> norm_num [Format.leastSubnormal]
  have hηT : f.leastSubnormal ≤ 16*(D+1)/fourthRoot f.leastSubnormal := by
    apply (le_div_iff₀ hh).2
    have hm := mul_le_mul_of_nonneg_right hη1 hh.le
    nlinarith
  have hTBudget : 128*(9*f.coordinateCeiling+1) < f.interchange.format.overflowThreshold*rootLower f := by
    cases f <;> norm_num [Format.interchange, Format.coordinateCeiling, rootLower, fp32, fp64,
      FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.overflowThreshold]
  have hTlim : 8*(16*(D+1)/fourthRoot f.leastSubnormal) < f.interchange.format.overflowThreshold := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hh).2
    have hm := mul_le_mul_of_nonneg_left hl hover.le
    nlinarith
  exact ⟨heta, ha0, haErr.trans (by nlinarith [sq_nonneg A]), hn, hrecip,
    hTpos, hbT, hdT, hηT, hTlim⟩

end DistanceAccuracy.FaceRanges

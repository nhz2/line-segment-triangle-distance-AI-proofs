import DistanceAccuracy.FormatBudgets
import DistanceAccuracy.IEEEBridge

namespace DistanceAccuracy
open FP.IEEE FP.IEEE.Interchange
set_option exponentiation.threshold 2048

noncomputable def Format.interchange : Format → FP.IEEE.Interchange
  | .binary32 => fp32
  | .binary64 => fp64

instance (f : Format) : f.interchange.Valid := by
  cases f <;> dsimp [Format.interchange] <;> infer_instance

noncomputable def Format.coordinateCeiling : Format → ℝ
  | .binary32 => 2 ^ 30
  | .binary64 => 2 ^ 254

lemma Format.coordinateCeiling_nonneg (f : Format) : 0 ≤ f.coordinateCeiling := by
  cases f <;> norm_num [Format.coordinateCeiling]

lemma Format.admissible_coordinate_ceiling (f : Format) {L : ℝ}
    (hL : L < fourthRoot f.interchange.format.maxFinite / 4) :
    L ≤ f.coordinateCeiling := by
  have hm : 0 ≤ f.interchange.format.maxFinite := by
    cases f <;> norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32,
      FP.IEEE.binary64, FP.IEEE.Format.maxFinite]
  have hp : f.interchange.format.maxFinite ≤ (4*f.coordinateCeiling)^4 := by
    cases f <;> norm_num [Format.interchange, Format.coordinateCeiling, fp32, fp64,
      FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.maxFinite]
  have hceiling := f.coordinateCeiling_nonneg
  have hh : fourthRoot f.interchange.format.maxFinite ≤ 4*f.coordinateCeiling := by
    apply (pow_le_pow_iff_left₀ (fourthRoot_nonneg _) (by positivity : 0 ≤ 4*f.coordinateCeiling)
      (by decide : (4:ℕ) ≠ 0)).mp
    rw [fourthRoot_pow_four hm]
    exact hp
  linarith

lemma Format.quadratic_range (f : Format) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : L < fourthRoot f.interchange.format.maxFinite / 4) :
    512*L*L+32 < f.interchange.format.overflowThreshold := by
  have hc := f.admissible_coordinate_ceiling hL
  have hs := mul_self_le_mul_self hL0 hc
  have hn : 512*f.coordinateCeiling^2+32 < f.interchange.format.overflowThreshold := by
    cases f <;> norm_num [Format.interchange, Format.coordinateCeiling, fp32, fp64,
      FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.overflowThreshold]
  nlinarith

lemma Format.linear_range (f : Format) {L : ℝ} (_hL0 : 0 ≤ L)
    (hL : L < fourthRoot f.interchange.format.maxFinite / 4) :
    32*L < f.interchange.format.overflowThreshold := by
  have hc := f.admissible_coordinate_ceiling hL
  have hn : 32*f.coordinateCeiling < f.interchange.format.overflowThreshold := by
    cases f <;> norm_num [Format.interchange, Format.coordinateCeiling, fp32, fp64,
      FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.overflowThreshold]
  linarith

noncomputable def Format.subnormalRootLower : Format → ℝ
  | .binary32 => 1 / 2 ^ 75
  | .binary64 => 1 / 2 ^ 537

lemma Format.subnormalRootLower_le (f : Format) :
    f.subnormalRootLower ≤ Real.sqrt f.interchange.format.minSubnormal := by
  apply (Real.le_sqrt _ _).mpr
  · cases f <;> norm_num [Format.subnormalRootLower, Format.interchange, fp32, fp64,
      FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.minSubnormal]
  · cases f <;> norm_num [Format.subnormalRootLower]
  · cases f <;> norm_num [Format.interchange, fp32, fp64,
      FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.minSubnormal]

lemma Format.quotient_range (f : Format) {L : ℝ}
    (hL : L < fourthRoot f.interchange.format.maxFinite / 4) :
    128*(L+1) < f.interchange.format.overflowThreshold * Real.sqrt f.interchange.format.minSubnormal := by
  have hc := f.admissible_coordinate_ceiling hL
  have hn : 128*(f.coordinateCeiling+1) <
      f.interchange.format.overflowThreshold*f.subnormalRootLower := by
    cases f <;> norm_num [Format.interchange, Format.coordinateCeiling, Format.subnormalRootLower,
      fp32, fp64, FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.overflowThreshold]
  have ht : 0 ≤ f.interchange.format.overflowThreshold := by
    cases f <;> norm_num [Format.interchange, fp32, fp64,
      FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.overflowThreshold]
  have hmul := mul_le_mul_of_nonneg_left f.subnormalRootLower_le ht
  linarith

lemma Format.normalRoot_le_one (f : Format) : fourthRoot f.leastNormal ≤ 1 := by
  apply (pow_le_pow_iff_left₀ (fourthRoot_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    (by decide : (4:ℕ) ≠ 0)).mp
  rw [fourthRoot_pow_four f.normal_nonneg]
  cases f <;> norm_num [Format.leastNormal]

lemma Format.small_scale_admissible (f : Format) :
    fourthRoot f.leastNormal / 64 < fourthRoot f.interchange.format.maxFinite / 4 := by
  have hm : 0 ≤ f.interchange.format.maxFinite := by
    cases f <;> norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32,
      FP.IEEE.binary64, FP.IEEE.Format.maxFinite]
  have hlarge : (4:ℝ) ≤ fourthRoot f.interchange.format.maxFinite := by
    apply (pow_le_pow_iff_left₀ (by norm_num : (0:ℝ) ≤ 4) (fourthRoot_nonneg _)
      (by decide : (4:ℕ) ≠ 0)).mp
    rw [fourthRoot_pow_four hm]
    cases f <;> norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32,
      FP.IEEE.binary64, FP.IEEE.Format.maxFinite]
  have hs := f.normalRoot_le_one
  linarith

lemma Format.quartic_range (f : Format) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : L < fourthRoot f.interchange.format.maxFinite/4) :
    192*L^4+32 < f.interchange.format.overflowThreshold := by
  have hm : 0 ≤ f.interchange.format.maxFinite := by
    cases f <;> norm_num [Format.interchange,fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.maxFinite]
  have hp := pow_lt_pow_left₀ (show 4*L < fourthRoot f.interchange.format.maxFinite by linarith)
    (by positivity : 0 ≤ 4*L) (by decide : (4:ℕ) ≠ 0)
  rw [fourthRoot_pow_four hm, mul_pow] at hp
  have hmax : 128 ≤ f.interchange.format.maxFinite := by
    cases f <;> norm_num [Format.interchange,fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.maxFinite]
  have hth : f.interchange.format.maxFinite ≤ f.interchange.format.overflowThreshold := by
    cases f <;> norm_num [Format.interchange,fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,
      FP.IEEE.Format.maxFinite,FP.IEEE.Format.overflowThreshold]
  norm_num only [show (4:ℝ)^4=256 by norm_num] at hp
  linarith

lemma Format.cross_dot_range (f : Format) {L A D : ℝ} (hL0 : 0 ≤ L)
    (hL : L < fourthRoot f.interchange.format.maxFinite/4)
    (hA0 : 0 ≤ A) (hAD : A ≤ D) (hD : D ≤ (7/2)*L) :
    (11/10:ℝ)*(((1+4*f.interchange.format.unitRoundoff)*(A*D))^2+
      f.interchange.format.minSubnormal/f.interchange.format.unitRoundoff) <
        f.interchange.format.overflowThreshold := by
  have hρ : 0 ≤ f.interchange.format.unitRoundoff := f.interchange.format.unitRoundoff_pos.le
  have hρmax : f.interchange.format.unitRoundoff ≤ 1/16777216 := by
    cases f <;> norm_num [Format.interchange,fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.unitRoundoff]
  have he : f.interchange.format.minSubnormal/f.interchange.format.unitRoundoff ≤ 1 := by
    cases f <;> norm_num [Format.interchange,fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,
      FP.IEEE.Format.unitRoundoff,FP.IEEE.Format.minSubnormal]
  have hD0 := hA0.trans hAD
  have hm := mul_le_mul (hAD.trans hD) hD hD0 (by positivity : 0 ≤ (7/2:ℝ)*L)
  have hm0 : 0 ≤ A*D := mul_nonneg hA0 hD0
  have hs := mul_self_le_mul_self hm0 hm
  have hcoef : (1+4*f.interchange.format.unitRoundoff)^2 ≤ (1001/1000:ℝ) := by
    nlinarith [mul_nonneg hρ (sub_nonneg.mpr hρmax)]
  have hprod := mul_le_mul hcoef (show (A*D)^2 ≤ ((7/2:ℝ)*L)^4 by nlinarith only [hs])
    (sq_nonneg (A*D)) (by norm_num : (0:ℝ) ≤ 1001/1000)
  have hquad := f.quartic_range hL0 hL
  rw [mul_pow] at hprod
  nlinarith [pow_nonneg hL0 4]

end DistanceAccuracy

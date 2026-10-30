import DistanceAccuracy.DotWordBounds

namespace DistanceAccuracy.DotWordBounds
open Determinant

/-- Polynomial certificate for the sharp diagonal weighted-dot bound on a
cube. The maximum occurs at (H,H,0), but no calculus assertion is assumed. -/
lemma diagonal_cube_bound {H x y z : ℝ} (hH : 0 < H)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxH : x ≤ H) (hyH : y ≤ H) (hzH : z ≤ H) :
    2 * (3 * x + 2 * y + z) ^ 2 ≤ 25 * H * (x + y + z) := by
  have hX : 0 ≤ H - x := sub_nonneg.mpr hxH
  have hY : 0 ≤ H - y := sub_nonneg.mpr hyH
  have hZ : 0 ≤ H - z := sub_nonneg.mpr hzH
  have hcert : 0 ≤ H * (25 * H * (x + y + z) - 2 * (3 * x + 2 * y + z) ^ 2) := by
    calc
      _ = 18 * H * x * (H - x) + 8 * H * y * (H - y) + 2 * H * z * (H - z) +
        7 * x * (H - y) * (H - z) + 17 * y * (H - x) * (H - z) +
        23 * z * (H - x) * (H - y) + 18 * x * z * (H - y) +
        32 * y * z * (H - x) + 3 * x * y * z := by ring
      _ ≥ 0 := by positivity
  have := (mul_nonneg_iff_of_pos_left hH).mp hcert
  linarith

/-- Sharp self-dot estimate: W(a,a) ≤ sqrt(25/2) B ||a|| when all
coordinates have magnitude at most B. -/
theorem weighted_self_bound {a : E3} {B : ℝ} (hB : 0 < B)
    (ha : ∀ i, |a i| ≤ B) :
    3 * (a 0) ^ 2 + 2 * (a 1) ^ 2 + (a 2) ^ 2 ≤
      Real.sqrt (25 / 2) * B * ‖a‖ := by
  have hc (i : Fin 3) : (a i) ^ 2 ≤ B ^ 2 := by
    have h := ha i
    nlinarith [sq_abs (a i), mul_nonneg (sub_nonneg.mpr h)
      (show 0 ≤ B + |a i| by positivity)]
  have hcube := diagonal_cube_bound (sq_pos_of_pos hB)
    (sq_nonneg (a 0)) (sq_nonneg (a 1)) (sq_nonneg (a 2)) (hc 0) (hc 1) (hc 2)
  have hnorm : ‖a‖ ^ 2 = (a 0) ^ 2 + (a 1) ^ 2 + (a 2) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    ring
  have hs : (Real.sqrt (25 / 2 : ℝ)) ^ 2 = 25 / 2 := Real.sq_sqrt (by norm_num)
  have hsq : (Real.sqrt (25 / 2) * B * ‖a‖) ^ 2 = (25 / 2) * B ^ 2 * ‖a‖ ^ 2 := by
    rw [mul_pow, mul_pow, hs]
  have hpos : 0 ≤ Real.sqrt (25 / 2) * B * ‖a‖ := by positivity
  nlinarith

noncomputable def weightedAbs (b : E3) : E3 :=
  WithLp.toLp 2 ![3 * |b 0|, 2 * |b 1|, |b 2|]

lemma weightedAbs_norm {b : E3} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i, |b i| ≤ B) : ‖weightedAbs b‖ ≤ Real.sqrt 14 * B := by
  have hc (i : Fin 3) : (b i) ^ 2 ≤ B ^ 2 := by
    have h := hb i
    nlinarith [sq_abs (b i), mul_nonneg (sub_nonneg.mpr h)
      (show 0 ≤ B + |b i| by positivity)]
  have hn : ‖weightedAbs b‖ ^ 2 = 9 * (b 0) ^ 2 + 4 * (b 1) ^ 2 + (b 2) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, weightedAbs, Fin.sum_univ_succ, mul_pow]
    ring
  have hs : (Real.sqrt (14 : ℝ)) ^ 2 = 14 := Real.sq_sqrt (by norm_num)
  have heq : (Real.sqrt 14 * B) ^ 2 = 14 * B ^ 2 := by rw [mul_pow, hs]
  nlinarith [hc 0, hc 1, hc 2, norm_nonneg (weightedAbs b),
    mul_nonneg (Real.sqrt_nonneg (14 : ℝ)) hB]

/-- Cauchy-Schwarz gives the sharp general weighted-dot coordinate bound. -/
theorem weighted_general_bound {a b : E3} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i, |b i| ≤ B) :
    3 * |a 0 * b 0| + 2 * |a 1 * b 1| + |a 2 * b 2| ≤
      Real.sqrt 14 * B * ‖a‖ := by
  have hc := real_inner_le_norm (absVec a) (weightedAbs b)
  rw [norm_absVec] at hc
  have hw := weightedAbs_norm hB hb
  have hm := mul_le_mul_of_nonneg_left hw (norm_nonneg a)
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ,
    absVec, weightedAbs] at hc
  simp only [abs_mul]
  dsimp [weightedAbs] at hm
  nlinarith

lemma weighted_general_scaled {a b : E3} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ i, |b i| ≤ D / Real.sqrt 3) :
    3 * |a 0 * b 0| + 2 * |a 1 * b 1| + |a 2 * b 2| ≤
      (2161 / 1000) * D * ‖a‖ := by
  have hs3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs3sq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hs14sq := Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)
  have hratio : Real.sqrt 14 / Real.sqrt 3 ≤ (2161 / 1000 : ℝ) := by
    apply (div_le_iff₀ hs3).2
    nlinarith [Real.sqrt_nonneg (14 : ℝ)]
  have hbase := weighted_general_bound (a := a) (show 0 ≤ D / Real.sqrt 3 by positivity) hb
  have hm := mul_le_mul_of_nonneg_right hratio (mul_nonneg hD (norm_nonneg a))
  have heq : Real.sqrt 14 * (D / Real.sqrt 3) * ‖a‖ =
      (Real.sqrt 14 / Real.sqrt 3) * (D * ‖a‖) := by ring
  rw [heq] at hbase
  nlinarith

lemma weighted_self_scaled {a : E3} {D : ℝ} (hD : 0 < D)
    (ha : ∀ i, |a i| ≤ D / Real.sqrt 3) :
    3 * (a 0) ^ 2 + 2 * (a 1) ^ 2 + (a 2) ^ 2 ≤
      (2042 / 1000) * D * ‖a‖ := by
  have hs3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs3sq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hssq := Real.sq_sqrt (show (0 : ℝ) ≤ 25 / 2 by norm_num)
  have hratio : Real.sqrt (25 / 2) / Real.sqrt 3 ≤ (2042 / 1000 : ℝ) := by
    apply (div_le_iff₀ hs3).2
    nlinarith [Real.sqrt_nonneg (25 / 2 : ℝ)]
  have hbase := weighted_self_bound (show 0 < D / Real.sqrt 3 by positivity) ha
  have hm := mul_le_mul_of_nonneg_right hratio (mul_nonneg hD.le (norm_nonneg a))
  have heq : Real.sqrt (25 / 2) * (D / Real.sqrt 3) * ‖a‖ =
      (Real.sqrt (25 / 2) / Real.sqrt 3) * (D * ‖a‖) := by ring
  rw [heq] at hbase
  nlinarith

end DistanceAccuracy.DotWordBounds

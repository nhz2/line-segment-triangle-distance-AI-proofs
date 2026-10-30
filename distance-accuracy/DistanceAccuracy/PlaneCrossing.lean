import DistanceAccuracy.AffineRoot
import DistanceAccuracy.Geometry

namespace DistanceAccuracy.PlaneCrossing
open DistanceAccuracy.Geometry

/-- An approximate normal and two inexact dot products determine an affine
plane equation. Its minimizing parameter controls true plane height without
an inverse crossing-angle factor. All errors are explicit local quantities. -/
theorem plane_height {N M AP P : E3} {g₀ g₁ s t a b₀ b₁ D : ℝ}
    (ha : 0 ≤ a) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁) (hD : 0 ≤ D)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hN : 0 < ‖N‖) (hnormal : ‖M-N‖ ≤ a*‖N‖)
    (hP : ‖P‖ ≤ D) (hAP : ‖AP-s•P‖ ≤ D)
    (he0 : |g₀-inner ℝ M AP| ≤ b₀*‖N‖*D)
    (he1 : |g₁+inner ℝ M P| ≤ b₁*‖N‖*D)
    (hroot : inner ℝ N (AP-t•P) = 0)
    (hopt : 0 ≤ (g₁^2*s+g₀*g₁)*(t-s)) :
    |inner ℝ N (AP-s•P)| / ‖N‖ ≤ (a+b₀+b₁)*D := by
  have hns : |inner ℝ (M-N) (AP-s•P)| ≤ a*‖N‖*D :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul hnormal hAP (norm_nonneg _) (by positivity))
  have hnp : |inner ℝ (M-N) P| ≤ a*‖N‖*D :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul hnormal hP (norm_nonneg _) (by positivity))
  have hsabs : |s| ≤ 1 := by rw [abs_of_nonneg hs0]; exact hs1
  have hts : |t-s| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hes : |(g₀+g₁*s)-(inner ℝ N AP+(-inner ℝ N P)*s)| ≤ (a+b₀+b₁)*‖N‖*D := by
    have heq : (g₀+g₁*s)-(inner ℝ N AP+(-inner ℝ N P)*s) =
        (g₀-inner ℝ M AP)+(g₁+inner ℝ M P)*s+inner ℝ (M-N) (AP-s•P) := by
      simp only [inner_sub_left, inner_sub_right, inner_smul_right]; ring
    rw [heq]
    have hmul : |(g₁+inner ℝ M P)*s| ≤ b₁*‖N‖*D := by
      rw [abs_mul]
      exact (mul_le_mul he1 hsabs (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    have h1 := abs_add_le (g₀-inner ℝ M AP) ((g₁+inner ℝ M P)*s)
    have h2 := abs_add_le ((g₀-inner ℝ M AP)+(g₁+inner ℝ M P)*s)
      (inner ℝ (M-N) (AP-s•P))
    nlinarith
  have hosc : |((g₀+g₁*t)-(inner ℝ N AP+(-inner ℝ N P)*t))-
      ((g₀+g₁*s)-(inner ℝ N AP+(-inner ℝ N P)*s))| ≤ (a+b₀+b₁)*‖N‖*D := by
    have heq : ((g₀+g₁*t)-(inner ℝ N AP+(-inner ℝ N P)*t))-
      ((g₀+g₁*s)-(inner ℝ N AP+(-inner ℝ N P)*s)) =
      ((g₁+inner ℝ M P)-inner ℝ (M-N) P)*(t-s) := by
      simp only [inner_sub_left]; ring
    rw [heq, abs_mul]
    have hinner : |(g₁+inner ℝ M P)-inner ℝ (M-N) P| ≤ (a+b₁)*‖N‖*D := by
      have h := abs_sub (g₁+inner ℝ M P) (inner ℝ (M-N) P)
      nlinarith
    have h := mul_le_mul hinner hts (abs_nonneg _) (by positivity : 0 ≤ (a+b₁)*‖N‖*D)
    have hp := mul_nonneg (mul_nonneg hb₀ hN.le) hD
    nlinarith
  have hr : inner ℝ N AP+(-inner ℝ N P)*t = 0 := by
    simp only [inner_sub_right, inner_smul_right] at hroot
    nlinarith only [hroot]
  have h := affine_root_error hr hopt hes hosc
  have heq : inner ℝ N AP+(-inner ℝ N P)*s = inner ℝ N (AP-s•P) := by
    simp only [inner_sub_right, inner_smul_right]; ring
  rw [heq] at h
  exact (div_le_iff₀ hN).mpr (by nlinarith)

end DistanceAccuracy.PlaneCrossing

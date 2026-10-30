import DistanceAccuracy.Projection
import DistanceAccuracy.Bounds
import DistanceAccuracy.Geometry

/-! Squared projection loss lifted to Euclidean residual norms and perturbed
cross vectors. These lemmas do not assume a small angle or accurate parameters. -/
namespace DistanceAccuracy.ReducedProjection
open DistanceAccuracy.Geometry

lemma residual_sq (k n : E3) (t : ℝ) :
    ‖k + t • n‖ ^ 2 = quadratic (‖n‖ ^ 2) (inner ℝ n k) (‖k‖ ^ 2) t := by
  rw [norm_add_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [real_inner_comm k n]
  dsimp [quadratic]
  ring

/-- An effective-gradient bound produces a squared norm bound; the small
squared direction norm cancels against the corresponding factor in `er`. -/
theorem projected_residual_sq_le {k n : E3} {ah bh t tstar er ea B C : ℝ}
    (hn : n ≠ 0) (hKKT : 0 ≤ (ah * t + bh) * (tstar - t))
    (hsplit : (ah - ‖n‖ ^ 2) * t + (bh - inner ℝ n k) = er + ea)
    (hspan : |t - tstar| ≤ 1) (_hB : 0 ≤ B) (_hC : 0 ≤ C)
    (her : |er| ≤ ‖n‖ * B) (hea : |ea| ≤ C) :
    ‖k + t • n‖ ^ 2 ≤ ‖k + tstar • n‖ ^ 2 + B ^ 2 + 2 * C := by
  have ha : 0 < ‖n‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  have hl := projection_loss_absolute (a := ‖n‖ ^ 2) (b := inner ℝ n k)
    (c := ‖k‖ ^ 2) ha hKKT hsplit hspan
  have hs : er ^ 2 ≤ (‖n‖ * B) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg er) her
    simpa only [← sq, sq_abs] using h
  have hb : er ^ 2 / ‖n‖ ^ 2 ≤ B ^ 2 := by
    apply (div_le_iff₀ ha).mpr
    nlinarith only [hs]
  rw [residual_sq, residual_sq]
  linarith

lemma residual_perturbation {k n kc nc : E3} {t δ : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (he : ‖kc - k‖ + ‖nc - n‖ ≤ δ) :
    ‖(kc + t • nc) - (k + t • n)‖ ≤ δ := by
  have hid : (kc + t • nc) - (k + t • n) = (kc - k) + t • (nc - n) := by module
  rw [hid]
  calc
    ‖(kc - k) + t • (nc - n)‖ ≤ ‖kc - k‖ + ‖t • (nc - n)‖ := norm_add_le _ _
    _ = ‖kc - k‖ + t * ‖nc - n‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    _ ≤ δ := by nlinarith [norm_nonneg (nc - n)]

/-- Original and perturbed reduced residuals differ by at most δ on [0,1].
Combining that with the squared solve loss gives the `J`-type estimate. -/
theorem perturbed_projection_norm_bound {k n kc nc : E3} {t v d δ B C : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (_hd : 0 ≤ d) (_hδ : 0 ≤ δ) (_hB : 0 ≤ B) (hC : 0 ≤ C)
    (he : ‖kc - k‖ + ‖nc - n‖ ≤ δ)
    (hstar : ‖k + v • n‖ ≤ d)
    (hsolve : ‖kc + t • nc‖ ^ 2 ≤ ‖kc + v • nc‖ ^ 2 + B ^ 2 + 2 * C) :
    ‖k + t • n‖ ≤ hypot (d + δ) B + δ + Real.sqrt (2 * C) := by
  have het := residual_perturbation ht0 ht1 he
  have hev := residual_perturbation hv0 hv1 he
  have hvnorm : ‖kc + v • nc‖ ≤ d + δ := by
    have h := norm_le_norm_add_norm_sub (k + v • n) (kc + v • nc)
    rw [norm_sub_rev] at h
    linarith
  have htnorm : ‖k + t • n‖ ≤ ‖kc + t • nc‖ + δ := by
    have h := norm_le_norm_add_norm_sub (kc + t • nc) (k + t • n)
    linarith
  have hvnormsq := mul_self_le_mul_self (norm_nonneg (kc + v • nc)) hvnorm
  have hsq := hypot_sq (d + δ) B
  have hs := Real.sq_sqrt (show 0 ≤ 2 * C by positivity)
  have hh := hypot_nonneg (d + δ) B
  have hs0 := Real.sqrt_nonneg (2 * C)
  have hcprod := mul_nonneg hh hs0
  have htbound : ‖kc + t • nc‖ ≤ hypot (d + δ) B + Real.sqrt (2 * C) := by
    nlinarith [norm_nonneg (kc + t • nc)]
  linarith

end DistanceAccuracy.ReducedProjection

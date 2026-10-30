import DistanceAccuracy.ReducedProjection

namespace DistanceAccuracy

lemma hypot_scale {a b c : ℝ} (hc : 0 ≤ c) : hypot (c*a) (c*b) = c*hypot a b := by
  apply (sq_eq_sq₀ (hypot_nonneg _ _) (mul_nonneg hc (hypot_nonneg _ _))).mp
  simp only [hypot_sq, mul_pow]
  ring

namespace ReducedProjection
open DistanceAccuracy.Geometry

/-- Normalize only in the analysis; no division of vector components is
inserted into the executable algorithm. -/
theorem normalized_perturbed_bound {k n kc nc : E3} {t v A d δ B C : ℝ}
    (hA : 0 < A) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hd : 0 ≤ d) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (he : ‖kc-k‖+‖nc-n‖ ≤ A*δ)
    (hstar : ‖k+v•n‖ ≤ A*d)
    (hsolve : ‖kc+t•nc‖^2 ≤ ‖kc+v•nc‖^2+(A*B)^2+2*C) :
    ‖k+t•n‖/A ≤ hypot (d+δ) B+δ+Real.sqrt (2*C)/A := by
  have h := perturbed_projection_norm_bound ht0 ht1 hv0 hv1
    (mul_nonneg hA.le hd) (mul_nonneg hA.le hδ) (mul_nonneg hA.le hB) hC he hstar hsolve
  rw [← mul_add, hypot_scale hA.le] at h
  apply (div_le_iff₀ hA).mpr
  have hs : Real.sqrt (2*C)/A*A = Real.sqrt (2*C) := div_mul_cancel₀ _ hA.ne'
  nlinarith only [h,hs]

/-- Cross-vector perturbation and the exact-line solve combine into J, with
absolute cross errors carried additively rather than amplified by the angle. -/
theorem normalized_J_bound {k n kc nc : E3} {t v A d rho D c e C : ℝ}
    (hA : 0 < A) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hd : 0 ≤ d) (hr : 0 < rho) (hD : 0 < D) (hc : 0 ≤ c) (he0 : 0 ≤ e) (hC : 0 ≤ C)
    (he : ‖kc-k‖+‖nc-n‖ ≤ A*(c*rho*D+e))
    (hstar : ‖k+v•n‖ ≤ A*d)
    (hsolve : ‖kc+t•nc‖^2 ≤ ‖kc+v•nc‖^2+(A*(7.02*rho*D))^2+2*C) :
    ‖k+t•n‖/A ≤ rho*D*J c (d/(rho*D))+2*e+Real.sqrt (2*C)/A := by
  have h := normalized_perturbed_bound hA ht0 ht1 hv0 hv1 hd
    (by positivity : 0 ≤ c*rho*D+e) (by positivity : 0 ≤ 7.02*rho*D) hC he hstar hsolve
  have hh := hypot_add_le (a := d+c*rho*D) (b := 7.02*rho*D) (by positivity) he0
  have hscale : hypot (d+c*rho*D) (7.02*rho*D)+c*rho*D = rho*D*J c (d/(rho*D)) := by
    have hn : rho*D ≠ 0 := mul_ne_zero hr.ne' hD.ne'
    have heq : d+c*rho*D = (rho*D)*(d/(rho*D)+c) := by field_simp <;> ring
    rw [heq, show 7.02*rho*D = (rho*D)*7.02 by ring, hypot_scale (by positivity)]
    dsimp [J]
    ring
  have heq : d+(c*rho*D+e) = (d+c*rho*D)+e := by ring
  rw [heq] at h
  rw [← hscale]
  linarith

end ReducedProjection
end DistanceAccuracy

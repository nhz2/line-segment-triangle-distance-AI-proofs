import DistanceAccuracy.Projection

/-!
# Plane-crossing root lemma

A clamped root of an approximate affine function is close in *function value*
to a root of the true affine function. There is no inverse-angle factor.
This proves the scalar mechanism used in §7 of `proof.md`.
-/
namespace DistanceAccuracy

lemma affine_root_value_bound {g es et M : ℝ}
    (hoptimal : 0 ≤ g * (et - g))
    (hes : |es| ≤ M) (hosc : |et - es| ≤ M) : |g - es| ≤ M := by
  obtain ⟨heslo, heshi⟩ := abs_le.mp hes
  obtain ⟨holo, hohi⟩ := abs_le.mp hosc
  rcases mul_nonneg_iff.mp hoptimal with ⟨hg, ht⟩ | ⟨hg, ht⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The errors at the computed parameter and at a true root suffice.
The variational condition includes a constant approximate affine function. -/
theorem affine_root_error {f₀ f₁ g₀ g₁ s t M : ℝ}
    (hroot : f₀ + f₁ * t = 0)
    (hoptimal : 0 ≤ ((g₁ ^ 2) * s + g₀ * g₁) * (t - s))
    (hes : |(g₀ + g₁ * s) - (f₀ + f₁ * s)| ≤ M)
    (hosc : |((g₀ + g₁ * t) - (f₀ + f₁ * t)) -
      ((g₀ + g₁ * s) - (f₀ + f₁ * s))| ≤ M) :
    |f₀ + f₁ * s| ≤ M := by
  have hv : 0 ≤ (g₀ + g₁ * s) *
      (((g₀ + g₁ * t) - (f₀ + f₁ * t)) - (g₀ + g₁ * s)) := by
    rw [hroot]
    nlinarith only [hoptimal]
  have h := affine_root_value_bound hv hes hosc
  simpa only [sub_sub_cancel] using h

/-- A nonconstant approximate affine function's clamped root supplies the
variational condition automatically. -/
theorem clamped_affine_root_error {f₀ f₁ g₀ g₁ t M : ℝ}
    (hg : g₁ ≠ 0) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hroot : f₀ + f₁ * t = 0)
    (hes : |(g₀ + g₁ * max 0 (min 1 (-g₀ / g₁))) -
      (f₀ + f₁ * max 0 (min 1 (-g₀ / g₁)))| ≤ M)
    (hosc : |((g₀ + g₁ * t) - (f₀ + f₁ * t)) -
      ((g₀ + g₁ * max 0 (min 1 (-g₀ / g₁))) -
        (f₀ + f₁ * max 0 (min 1 (-g₀ / g₁))))| ≤ M) :
    |f₀ + f₁ * max 0 (min 1 (-g₀ / g₁))| ≤ M := by
  have ha : 0 < g₁ ^ 2 := sq_pos_of_ne_zero hg
  have hq : -(g₀ * g₁) / g₁ ^ 2 = -g₀ / g₁ := by field_simp
  have ho := clamp_optimal (a := g₁ ^ 2) (b := g₀ * g₁) ha
    (show (0 : ℝ) ≤ 1 by norm_num) ht0 ht1
  rw [hq] at ho
  exact affine_root_error hroot ho hes hosc

end DistanceAccuracy

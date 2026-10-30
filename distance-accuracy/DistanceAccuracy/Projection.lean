import Mathlib

/-!
# The squared-loss projection lemma

These are the real-arithmetic lemmas in §1 of `proof.md`. The variational
inequality is explicit: the caller must establish that the computed parameter
minimizes the perturbed quadratic on the clamping interval. No floating-point
implementation is assumed or axiomatized here.
-/
namespace DistanceAccuracy

def quadratic (a b c t : ℝ) : ℝ := a * t ^ 2 + 2 * b * t + c

/-- A perturbed first-order optimality condition gives a squared loss,
without dividing by a geometric angle. -/
theorem projection_loss {a b c ah bh t tstar : ℝ} (ha : 0 < a)
    (hoptimal : 0 ≤ (ah * t + bh) * (tstar - t)) :
    quadratic a b c t - quadratic a b c tstar ≤
      ((ah - a) * t + (bh - b)) ^ 2 / a := by
  apply (le_div_iff₀ ha).2
  have hs := sq_nonneg (a * (t - tstar) + ((ah - a) * t + (bh - b)))
  have ho := mul_nonneg (le_of_lt ha) hoptimal
  dsimp [quadratic]
  nlinarith

/-- Splitting off an absolute gradient error avoids dividing that error by a
possibly tiny direction length. Both parameters lie in an interval of length 1. -/
theorem projection_loss_absolute {a b c ah bh t tstar er ea : ℝ}
    (ha : 0 < a)
    (hoptimal : 0 ≤ (ah * t + bh) * (tstar - t))
    (hsplit : (ah - a) * t + (bh - b) = er + ea)
    (hspan : |t - tstar| ≤ 1) :
    quadratic a b c t - quadratic a b c tstar ≤ er ^ 2 / a + 2 * |ea| := by
  have he : -(ea * (t - tstar)) ≤ |ea| := by
    calc
      -(ea * (t - tstar)) ≤ |ea * (t - tstar)| := neg_le_abs _
      _ = |ea| * |t - tstar| := abs_mul _ _
      _ ≤ |ea| * 1 := mul_le_mul_of_nonneg_left hspan (abs_nonneg _)
      _ = |ea| := mul_one _
  have hsplit' := congrArg (fun x : ℝ => x * (t - tstar)) hsplit
  have hbase : quadratic a b c t - quadratic a b c tstar ≤
      -2 * er * (t - tstar) - a * (t - tstar) ^ 2 + 2 * |ea| := by
    dsimp [quadratic]
    nlinarith
  have hs := sq_nonneg (a * (t - tstar) + er)
  have hcompletion : -2 * er * (t - tstar) - a * (t - tstar) ^ 2 ≤ er ^ 2 / a := by
    apply (le_div_iff₀ ha).2
    nlinarith
  linarith

/-- Projection onto an interval satisfies the needed variational inequality,
including both clamped endpoints. -/
theorem clamp_optimal {a b lo hi x : ℝ} (ha : 0 < a) (hlohi : lo ≤ hi)
    (hxlo : lo ≤ x) (hxhi : x ≤ hi) :
    0 ≤ (a * (max lo (min hi (-b / a))) + b) *
      (x - max lo (min hi (-b / a))) := by
  by_cases hl : -b / a ≤ lo
  · have hc : max lo (min hi (-b / a)) = lo := by
      exact max_eq_left (le_trans (min_le_right _ _) hl)
    rw [hc]
    have hab : 0 ≤ a * lo + b := by
      have := (div_le_iff₀ ha).1 hl
      nlinarith
    exact mul_nonneg hab (sub_nonneg.mpr hxlo)
  · by_cases hh : hi ≤ -b / a
    · have hc : max lo (min hi (-b / a)) = hi := by
        rw [min_eq_left hh, max_eq_right hlohi]
      rw [hc]
      have hab : a * hi + b ≤ 0 := by
        have := (le_div_iff₀ ha).1 hh
        nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos hab (sub_nonpos.mpr hxhi)
    · have hc : max lo (min hi (-b / a)) = -b / a := by
        rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]
      rw [hc]
      have hz : a * (-b / a) + b = 0 := by field_simp; ring
      rw [hz, zero_mul]

end DistanceAccuracy

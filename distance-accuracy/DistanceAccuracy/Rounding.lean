import Mathlib

/-!
# Three-operation rounding error

The hypotheses below are local error bounds at the three *actual* operation
inputs. Instantiating them for IEEE operations (including proving no overflow)
is a separate obligation. The lemma propagates their errors without treating
an FMA as a multiply followed by an add.
-/
namespace DistanceAccuracy

private lemma accumulate_three {rho eta x y z e₁ e₂ e₃ : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1 / 16) (he : 0 ≤ eta)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h₁ : e₁ ≤ rho * x + eta / 2)
    (h₂ : e₂ ≤ rho * (x + y + e₁) + eta / 2)
    (h₃ : e₃ ≤ rho * (x + y + z + e₁ + e₂) + eta / 2) :
    e₁ + e₂ + e₃ ≤ rho * (1 + rho) ^ 2 * (3 * x + 2 * y + z) + 2 * eta := by
  have h₁r := mul_le_mul_of_nonneg_left h₁ hr
  have h₁rr := mul_le_mul_of_nonneg_left h₁ (sq_nonneg rho)
  have h₂r := mul_le_mul_of_nonneg_left h₂ hr
  have hc : 0 ≤ 1 - 3 * rho - rho ^ 2 := by
    have hs := mul_self_le_mul_self hr hrmax
    nlinarith
  have hce := mul_nonneg hc he
  have hx₂ := mul_nonneg (sq_nonneg rho) hx
  have hy₂ := mul_nonneg (sq_nonneg rho) hy
  have hz₂ := mul_nonneg (sq_nonneg rho) hz
  have hx₃ := mul_nonneg (pow_nonneg hr 3) hx
  have hy₃ := mul_nonneg (pow_nonneg hr 3) hy
  have hz₃ := mul_nonneg (pow_nonneg hr 3) hz
  nlinarith

/-- For x=a₁b₁, y=a₂b₂, z=a₃b₃ this is the weighted `dot3` bound
in §2 of the natural-language proof. p is the rounded multiply;
s and q are the rounded FMA results. -/
theorem dot3_error {rho eta x y z p s q : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1 / 16) (he : 0 ≤ eta)
    (hp : |p - x| ≤ rho * |x| + eta / 2)
    (hs : |s - (p + y)| ≤ rho * |p + y| + eta / 2)
    (hq : |q - (s + z)| ≤ rho * |s + z| + eta / 2) :
    |q - (x + y + z)| ≤
      rho * (1 + rho) ^ 2 * (3 * |x| + 2 * |y| + |z|) + 2 * eta := by
  have habp : |p + y| ≤ |x| + |y| + |p - x| := by
    calc
      |p + y| = |(x + y) + (p - x)| := by congr 1; ring
      _ ≤ |x + y| + |p - x| := abs_add_le _ _
      _ ≤ |x| + |y| + |p - x| := add_le_add (abs_add_le _ _) (le_refl _)
  have habs : |s + z| ≤ |x| + |y| + |z| + |p - x| + |s - (p + y)| := by
    calc
      |s + z| = |(p + y) + z + (s - (p + y))| := by congr 1; ring
      _ ≤ |(p + y) + z| + |s - (p + y)| := abs_add_le _ _
      _ ≤ (|p + y| + |z|) + |s - (p + y)| := add_le_add (abs_add_le _ _) (le_refl _)
      _ ≤ |x| + |y| + |z| + |p - x| + |s - (p + y)| := by linarith
  have hs' : |s - (p + y)| ≤ rho * (|x| + |y| + |p - x|) + eta / 2 := by
    have := mul_le_mul_of_nonneg_left habp hr
    linarith
  have hq' : |q - (s + z)| ≤
      rho * (|x| + |y| + |z| + |p - x| + |s - (p + y)|) + eta / 2 := by
    have := mul_le_mul_of_nonneg_left habs hr
    linarith
  have ht : |q - (x + y + z)| ≤ |p - x| + |s - (p + y)| + |q - (s + z)| := by
    calc
      |q - (x + y + z)| = |((p - x) + (s - (p + y))) + (q - (s + z))| := by
        congr 1; ring
      _ ≤ |(p - x) + (s - (p + y))| + |q - (s + z)| := abs_add_le _ _
      _ ≤ |p - x| + |s - (p + y)| + |q - (s + z)| :=
        add_le_add (abs_add_le _ _) (le_refl _)
  exact ht.trans (accumulate_three hr hrmax he (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    hp hs' hq')

end DistanceAccuracy

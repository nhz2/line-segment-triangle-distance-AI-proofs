import DistanceAccuracy.Formats

/-!
# Exact-arithmetic certificate for the example with coefficient > 9.155

The convex-combination equalities and the comparison with the claimed output
are formalized here. `counterexample.jl` checks that Julia actually returns
q = 4181413/32768; the Lean theorem does not execute Julia or assert its output.
-/
namespace DistanceAccuracy.Counterexample

abbrev Vec3 := Fin 3 → ℝ

def A : Vec3 := ![-10350544, -10332076, -10169968]
def B : Vec3 := ![10350545, 7004759, 9067019]
def C : Vec3 := ![9871916, 10332077, 10169969]
def P0 : Vec3 := ![-9373420, -7754638, -8416905]
def P1 : Vec3 := ![9778836, 10196786, 10057847]
def intersection : Vec3 := ![9479582, 9916295, 9769179]

lemma on_segment : intersection = (1 / 64 : ℝ) • P0 + (63 / 64 : ℝ) • P1 := by
  funext i
  fin_cases i <;> norm_num [intersection, P0, P1]

lemma in_triangle : intersection =
    (10 / 513 : ℝ) • A + (2 / 513 : ℝ) • B + (501 / 513 : ℝ) • C := by
  funext i
  fin_cases i <;> norm_num [intersection, A, B, C]

lemma weights_are_convex :
    (0 : ℝ) ≤ 1 / 64 ∧ 0 ≤ (63 / 64 : ℝ) ∧ (1 / 64 : ℝ) + 63 / 64 = 1 ∧
    (0 : ℝ) ≤ 10 / 513 ∧ 0 ≤ (2 / 513 : ℝ) ∧ 0 ≤ (501 / 513 : ℝ) ∧
    (10 / 513 : ℝ) + 2 / 513 + 501 / 513 = 1 := by norm_num

noncomputable def q : ℝ := 4181413 / 32768
noncomputable def unit : ℝ := (1 / 2 ^ 23) * 10350545

lemma squared_comparison : ((9.155 : ℝ) * unit) ^ 2 < q := by norm_num [q, unit]

lemma coefficient_gt : (9.155 : ℝ) * unit < Real.sqrt q := by
  have hs := Real.sq_sqrt (show 0 ≤ q by norm_num [q])
  have hn := Real.sqrt_nonneg q
  have hb := squared_comparison
  have hu : 0 ≤ unit := by norm_num [unit]
  nlinarith

lemma float32_floor_le : fourthRoot Format.binary32.leastNormal ≤ (1 / 2 ^ 31 : ℝ) := by
  apply (pow_le_pow_iff_left₀ (fourthRoot_nonneg _) (by positivity)
    (by decide : (4 : ℕ) ≠ 0)).1
  rw [fourthRoot_pow_four Format.binary32.normal_nonneg]
  norm_num [Format.leastNormal]

/-- Constant nine fails for the specified q, even including the underflow floor. -/
lemma exceeds_nine_with_floor :
    9 * unit + fourthRoot Format.binary32.leastNormal < Real.sqrt q := by
  have hq := Real.sq_sqrt (show 0 ≤ q by norm_num [q])
  have hn := Real.sqrt_nonneg q
  have hc : (9 * unit + (1 / 2 ^ 31 : ℝ)) ^ 2 < q := by norm_num [q, unit]
  have hp : 0 ≤ 9 * unit + (1 / 2 ^ 31 : ℝ) := by norm_num [unit]
  have hfloor := float32_floor_le
  have hbound : 9 * unit + (1 / 2 ^ 31 : ℝ) < Real.sqrt q := by nlinarith
  linarith

end DistanceAccuracy.Counterexample

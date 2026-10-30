import Mathlib

/-! Exact real arithmetic for the error-envelope functions in `proof.md`, §3. -/
namespace DistanceAccuracy

noncomputable def hypot (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)

lemma hypot_nonneg (a b : ℝ) : 0 ≤ hypot a b := Real.sqrt_nonneg _

lemma hypot_sq (a b : ℝ) : hypot a b ^ 2 = a ^ 2 + b ^ 2 := by
  exact Real.sq_sqrt (by positivity)

lemma hypot_le {a b c : ℝ} (hc : 0 ≤ c) (hs : a ^ 2 + b ^ 2 ≤ c ^ 2) :
    hypot a b ≤ c := by
  exact Real.sqrt_le_iff.mpr ⟨hc, hs⟩

lemma le_hypot (a b : ℝ) : a ≤ hypot a b := by
  have := hypot_sq a b
  have := hypot_nonneg a b
  nlinarith [sq_nonneg b]

lemma hypot_mono {a a' b : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') :
    hypot a b ≤ hypot a' b := by
  apply hypot_le (hypot_nonneg _ _)
  rw [hypot_sq]
  nlinarith

lemma hypot_add_le {a b t : ℝ} (_ha : 0 ≤ a) (ht : 0 ≤ t) :
    hypot (a + t) b ≤ hypot a b + t := by
  apply hypot_le (add_nonneg (hypot_nonneg _ _) ht)
  have hs := hypot_sq a b
  have hh := le_hypot a b
  nlinarith [mul_nonneg (sub_nonneg.mpr hh) ht]

noncomputable def J (c z : ℝ) : ℝ := hypot (z + c) 7.02 + c
noncomputable def F (z : ℝ) : ℝ := hypot (J 3.17 z) 8.38
noncomputable def V (z : ℝ) : ℝ := hypot (J 3.60 z) 7.22
noncomputable def P (z : ℝ) : ℝ :=
  max (V (z + 2.02) + 4.03) (hypot (V (z + 2.02) + 4.02) 8.38 + 3.53)

lemma J_nonneg {c z : ℝ} (hc : 0 ≤ c) : 0 ≤ J c z := by
  exact add_nonneg (hypot_nonneg _ _) hc
lemma F_nonneg (z : ℝ) : 0 ≤ F z := hypot_nonneg _ _
lemma V_nonneg (z : ℝ) : 0 ≤ V z := hypot_nonneg _ _

lemma J_mono {c x y : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hxy : x ≤ y) :
    J c x ≤ J c y := by
  dsimp [J]
  exact add_le_add (hypot_mono (by linarith) (by linarith)) (le_refl c)
lemma F_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : F x ≤ F y := by
  exact hypot_mono (J_nonneg (by norm_num)) (J_mono (by norm_num) hx hxy)
lemma V_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : V x ≤ V y := by
  exact hypot_mono (J_nonneg (by norm_num)) (J_mono (by norm_num) hx hxy)

lemma J_add_le {c z t : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z) (ht : 0 ≤ t) :
    J c (z + t) ≤ J c z + t := by
  have h := hypot_add_le (b := (7.02 : ℝ)) (a := z + c) (by linarith) ht
  simpa only [J, add_assoc, add_comm, add_left_comm] using add_le_add h (le_refl c)

lemma F_add_le {z t : ℝ} (hz : 0 ≤ z) (ht : 0 ≤ t) : F (z + t) ≤ F z + t := by
  calc
    F (z + t) ≤ hypot (J 3.17 z + t) 8.38 :=
      hypot_mono (J_nonneg (by norm_num)) (J_add_le (by norm_num) hz ht)
    _ ≤ F z + t := hypot_add_le (J_nonneg (by norm_num)) ht

lemma V_add_le {z t : ℝ} (hz : 0 ≤ z) (ht : 0 ≤ t) : V (z + t) ≤ V z + t := by
  calc
    V (z + t) ≤ hypot (J 3.60 z + t) 7.22 :=
      hypot_mono (J_nonneg (by norm_num)) (J_add_le (by norm_num) hz ht)
    _ ≤ V z + t := hypot_add_le (J_nonneg (by norm_num)) ht

/-- Every bound of this form transfers a geometric/underflow perturbation
with multiplier at most one. -/
lemma F_le_at_zero {z : ℝ} (hz : 0 ≤ z) : F z ≤ F 0 + z := by
  simpa using F_add_le (z := 0) (by norm_num) hz
lemma V_le_at_zero {z : ℝ} (hz : 0 ≤ z) : V z ≤ V 0 + z := by
  simpa using V_add_le (z := 0) (by norm_num) hz

end DistanceAccuracy

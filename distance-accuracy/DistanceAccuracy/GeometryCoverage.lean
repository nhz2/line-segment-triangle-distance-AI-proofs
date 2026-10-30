import DistanceAccuracy.Geometry

/-!
# Exact boundary witnesses for the upper distance bound

These lemmas prove the geometric coverage steps in §§4 and 7 of `proof.md`.
They do not assume an upper-distance certificate: an edge witness is constructed
from two bounded residuals by interpolation. Floating-point evaluation errors
are separate from these exact Euclidean statements.
-/
namespace DistanceAccuracy.GeometryCoverage

abbrev E3 := Geometry.E3

def mix (a b t : ℝ) : ℝ := (1 - t) * a + t * b

def residual (R E F : E3) (u v : ℝ) : E3 := R + u • E + v • F

lemma mix_nonneg {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ mix a b t :=
  add_nonneg (mul_nonneg (by linarith) ha) (mul_nonneg ht0 hb)

lemma mix_le_one {a b t : ℝ} (ha : a ≤ 1) (hb : b ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : mix a b t ≤ 1 := by
  have h1 := mul_le_mul_of_nonneg_left ha (show 0 ≤ 1 - t by linarith)
  have h2 := mul_le_mul_of_nonneg_left hb ht0
  dsimp [mix]
  nlinarith

lemma residual_mix (R E F : E3) (u₀ v₀ u₁ v₁ t : ℝ) :
    residual R E F (mix u₀ u₁ t) (mix v₀ v₁ t) =
      (1 - t) • residual R E F u₀ v₀ + t • residual R E F u₁ v₁ := by
  dsimp [residual, mix]
  module

lemma norm_mix_le {x y : E3} {B t : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ‖(1 - t) • x + t • y‖ ≤ B := by
  calc
    ‖(1 - t) • x + t • y‖ ≤ ‖(1 - t) • x‖ + ‖t • y‖ := norm_add_le _ _
    _ = (1 - t) * ‖x‖ + t * ‖y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ 1 - t), abs_of_nonneg ht0]
    _ ≤ B := by
      have h1 := mul_le_mul_of_nonneg_left hx (show 0 ≤ 1 - t by linarith)
      have h2 := mul_le_mul_of_nonneg_left hy ht0
      nlinarith

lemma residual_mix_le {R E F : E3} {u₀ v₀ u₁ v₁ B t : ℝ}
    (h₀ : ‖residual R E F u₀ v₀‖ ≤ B) (h₁ : ‖residual R E F u₁ v₁‖ ≤ B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖residual R E F (mix u₀ u₁ t) (mix v₀ v₁ t)‖ ≤ B := by
  rw [residual_mix]
  exact norm_mix_le h₀ h₁ ht0 ht1

private lemma continuous_mix (a b : ℝ) : Continuous (mix a b) := by
  unfold mix
  fun_prop

private lemma exists_zero {f : ℝ → ℝ} (hf : Continuous f) (h0 : 0 ≤ f 0) (h1 : f 1 ≤ 0) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, f t = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨h1, h0⟩
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
    hf.continuousOn hmem
  exact ⟨t, ht, he⟩

/-- If an unconstrained line projection leaves the first segment, an endpoint
of that segment has a witness at no larger than the common residual bound.
The other parameter remains in its interval. No minimizer or angle assumption
is needed for this geometric implication. -/
theorem segment_boundary_witness {R E F : E3} {u₀ v₀ u₁ v₁ B : ℝ}
    (hu₀ : u₀ ∈ Set.Icc (0 : ℝ) 1)
    (hv₀ : v₀ ∈ Set.Icc (0 : ℝ) 1) (hv₁ : v₁ ∈ Set.Icc (0 : ℝ) 1)
    (hout : u₁ ≤ 0 ∨ 1 ≤ u₁)
    (h₀ : ‖residual R E F u₀ v₀‖ ≤ B) (h₁ : ‖residual R E F u₁ v₁‖ ≤ B) :
    ∃ u v : ℝ, (u = 0 ∨ u = 1) ∧ v ∈ Set.Icc (0 : ℝ) 1 ∧
      ‖residual R E F u v‖ ≤ B := by
  let f : ℝ → ℝ := fun t => min (mix u₀ u₁ t) (1 - mix u₀ u₁ t)
  have hf : Continuous f := (continuous_mix u₀ u₁).min (continuous_const.sub (continuous_mix u₀ u₁))
  have h0 : 0 ≤ f 0 := by dsimp [f, mix]; simp only [sub_zero, one_mul, zero_mul, add_zero]; exact le_min hu₀.1 (by linarith [hu₀.2])
  have h1 : f 1 ≤ 0 := by
    dsimp [f, mix]; simp only [sub_self, zero_mul, one_mul, zero_add]
    rcases hout with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  obtain ⟨t, ⟨ht0, ht1⟩, he⟩ := exists_zero hf h0 h1
  have hboundary : mix u₀ u₁ t = 0 ∨ mix u₀ u₁ t = 1 := by
    dsimp [f] at he
    rcases le_total (mix u₀ u₁ t) (1 - mix u₀ u₁ t) with h | h
    · left; simpa only [min_eq_left h] using he
    · right; rw [min_eq_right h] at he; linarith
  exact ⟨mix u₀ u₁ t, mix v₀ v₁ t, hboundary,
    ⟨mix_nonneg hv₀.1 hv₁.1 ht0 ht1, mix_le_one hv₀.2 hv₁.2 ht0 ht1⟩,
    residual_mix_le h₀ h₁ ht0 ht1⟩

/-- If an unconstrained line projection leaves the triangular parameter domain,
one of the two explicitly available edges (u=0 or u+v=1) has a bounded witness.
This is the coupled face/edge coverage step; v=0 is deliberately not needed. -/
theorem triangle_boundary_witness {R E F : E3} {u₀ v₀ u₁ v₁ B : ℝ}
    (hu₀ : 0 ≤ u₀) (huv₀ : u₀ + v₀ ≤ 1)
    (hv₀ : v₀ ∈ Set.Icc (0 : ℝ) 1) (hv₁ : v₁ ∈ Set.Icc (0 : ℝ) 1)
    (hout : u₁ ≤ 0 ∨ 1 ≤ u₁ + v₁)
    (h₀ : ‖residual R E F u₀ v₀‖ ≤ B) (h₁ : ‖residual R E F u₁ v₁‖ ≤ B) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ 1 ∧ (u = 0 ∨ u + v = 1) ∧
      ‖residual R E F u v‖ ≤ B := by
  let f : ℝ → ℝ := fun t => min (mix u₀ u₁ t) (1 - mix u₀ u₁ t - mix v₀ v₁ t)
  have hf : Continuous f := (continuous_mix u₀ u₁).min
    ((continuous_const.sub (continuous_mix u₀ u₁)).sub (continuous_mix v₀ v₁))
  have h0 : 0 ≤ f 0 := by
    dsimp [f, mix]; simp only [sub_zero, one_mul, zero_mul, add_zero]
    exact le_min hu₀ (by linarith)
  have h1 : f 1 ≤ 0 := by
    dsimp [f, mix]; simp only [sub_self, zero_mul, one_mul, zero_add]
    rcases hout with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  obtain ⟨t, ⟨ht0, ht1⟩, he⟩ := exists_zero hf h0 h1
  have hu : 0 ≤ mix u₀ u₁ t := by
    have h := min_le_left (mix u₀ u₁ t) (1 - mix u₀ u₁ t - mix v₀ v₁ t)
    change min _ _ = 0 at he; linarith
  have huv : mix u₀ u₁ t + mix v₀ v₁ t ≤ 1 := by
    have h := min_le_right (mix u₀ u₁ t) (1 - mix u₀ u₁ t - mix v₀ v₁ t)
    change min _ _ = 0 at he; linarith
  have hboundary : mix u₀ u₁ t = 0 ∨ mix u₀ u₁ t + mix v₀ v₁ t = 1 := by
    dsimp [f] at he
    rcases le_total (mix u₀ u₁ t) (1 - mix u₀ u₁ t - mix v₀ v₁ t) with h | h
    · left; simpa only [min_eq_left h] using he
    · right; rw [min_eq_right h] at he; linarith
  exact ⟨mix u₀ u₁ t, mix v₀ v₁ t, hu, mix_nonneg hv₀.1 hv₁.1 ht0 ht1,
    huv, hboundary, residual_mix_le h₀ h₁ ht0 ht1⟩

/-- The exact final cap agrees with the virtual shortened-interval projection,
or that virtual projection is on BC. This is independent of error estimates. -/
theorem face_cap_coverage {q v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    let u := max 0 (min 1 q)
    let ubar := max 0 (min (1 - v) q)
    (u = ubar ∧ min v (1 - u) = v) ∨ ubar + v = 1 := by
  dsimp
  by_cases hq : q ≤ 1 - v
  · left
    have hq1 : q ≤ 1 := by linarith
    rw [min_eq_right hq1, min_eq_right hq]
    refine ⟨rfl, min_eq_left ?_⟩
    have hu : max 0 q ≤ 1 - v := max_le (by linarith) hq
    linarith
  · right
    rw [min_eq_left (le_of_not_ge hq), max_eq_right (by linarith : 0 ≤ 1 - v)]
    ring


/-- Every point of a triangle is within half the base length of AC or BC.
This handles short/zero first edges without any division. -/
theorem short_base_edge_witness {R E F : E3} {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) :
    ∃ u' v' : ℝ, 0 ≤ u' ∧ 0 ≤ v' ∧ u' + v' ≤ 1 ∧
      (u' = 0 ∨ u' + v' = 1) ∧
      ‖residual R E F u v - residual R E F u' v'‖ ≤ ‖E‖ / 2 := by
  have hdiff (u' : ℝ) : residual R E F u v - residual R E F u' v = (u - u') • E := by
    dsimp [residual]; module
  by_cases h : u ≤ (1 - v) / 2
  · refine ⟨0, v, le_rfl, hv, by linarith, Or.inl rfl, ?_⟩
    rw [hdiff, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu]
    have hm := mul_le_mul_of_nonneg_right (show u ≤ 1 / 2 by linarith) (norm_nonneg E)
    linarith
  · refine ⟨1-v, v, by linarith, hv, by linarith, Or.inr (by ring), ?_⟩
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith : u - (1-v) ≤ 0)]
    have hm := mul_le_mul_of_nonneg_right (show -(u - (1-v)) ≤ 1 / 2 by linarith) (norm_nonneg E)
    linarith

private lemma ac_projection {c w : ℝ} (hc : 0 < c) (hw0 : 0 ≤ w) (hwc : w ≤ c) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ 1 ∧ (u = 0 ∨ u + v = 1) ∧ w = u + c * v := by
  refine ⟨0, w/c, le_rfl, div_nonneg hw0 hc.le, ?_, Or.inl rfl, ?_⟩
  · have h := (div_le_one hc).2 hwc; linarith
  · field_simp; ring

private lemma bc_projection {c w : ℝ} (hc : c < 1) (hcw : c ≤ w) (hw1 : w ≤ 1) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ 1 ∧ (u = 0 ∨ u + v = 1) ∧ w = u + c * v := by
  have hd : 0 < 1 - c := by linarith
  have hv0 : 0 ≤ (1-w)/(1-c) := div_nonneg (by linarith) hd.le
  have hv1 : (1-w)/(1-c) ≤ 1 := (div_le_one hd).2 (by linarith)
  refine ⟨1-(1-w)/(1-c), (1-w)/(1-c), by linarith, hv0,
    by linarith, Or.inr (by ring), ?_⟩
  field_simp
  ring

/-- The projection of a triangular point onto any scalar direction is attained
on AC or BC. The explicit case split includes obtuse triangles. -/
lemma projected_edge_witness {c u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) :
    ∃ u' v' : ℝ, 0 ≤ u' ∧ 0 ≤ v' ∧ u' + v' ≤ 1 ∧
      (u' = 0 ∨ u' + v' = 1) ∧ u + c * v = u' + c * v' := by
  by_cases hc0 : c ≤ 0
  · apply bc_projection (by linarith)
    · have hp := mul_nonneg (neg_nonneg.mpr hc0) (show 0 ≤ 1-v by linarith)
      nlinarith
    · have hp := mul_nonpos_of_nonpos_of_nonneg hc0 hv
      linarith
  · have hc0 : 0 < c := lt_of_not_ge hc0
    by_cases hc1 : 1 ≤ c
    · apply ac_projection hc0
      · exact add_nonneg hu (mul_nonneg hc0.le hv)
      · have h1 := mul_nonneg hc0.le (show 0 ≤ 1-u-v by linarith)
        have h2 := mul_nonneg (show 0 ≤ c-1 by linarith) hu
        nlinarith
    · have hc1 : c < 1 := lt_of_not_ge hc1
      by_cases hwc : u + c * v ≤ c
      · exact ac_projection hc0 (add_nonneg hu (mul_nonneg hc0.le hv)) hwc
      · apply bc_projection hc1 (le_of_not_ge hwc)
        have hp := mul_nonneg (show 0 ≤ 1-c by linarith) hv
        nlinarith

/-- A decomposition F=cE+H makes every triangle point lie within ||H|| of AC
or BC. Orthogonality is not required; choosing the orthogonal decomposition
later identifies ||H|| with the triangle height. -/
theorem height_edge_witness {R E F H : E3} {c u v : ℝ}
    (hF : F = c • E + H) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) :
    ∃ u' v' : ℝ, 0 ≤ u' ∧ 0 ≤ v' ∧ u' + v' ≤ 1 ∧
      (u' = 0 ∨ u' + v' = 1) ∧
      ‖residual R E F u v - residual R E F u' v'‖ ≤ ‖H‖ := by
  obtain ⟨u', v', hu', hv', huv', he, hproj⟩ := projected_edge_witness (c := c) hu hv huv
  refine ⟨u', v', hu', hv', huv', he, ?_⟩
  have hcoeff : u - u' + c * (v-v') = 0 := by nlinarith only [hproj]
  have hdiff : residual R E F u v - residual R E F u' v' = (v-v') • H := by
    calc
      _ = (u-u'+c*(v-v')) • E + (v-v') • H := by rw [hF]; dsimp [residual]; module
      _ = _ := by rw [hcoeff, zero_smul, zero_add]
  rw [hdiff, norm_smul, Real.norm_eq_abs]
  have hspan : |v-v'| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hspan (norm_nonneg H)

end DistanceAccuracy.GeometryCoverage

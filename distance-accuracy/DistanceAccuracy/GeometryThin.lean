import DistanceAccuracy.GeometryCoverage

/-! Thin-triangle edge coverage, including obtuse and degenerate triangles. -/
namespace DistanceAccuracy.GeometryCoverage
open scoped RealInnerProductSpace
open Matrix WithLp

noncomputable def exactCross (E F : E3) : E3 := toLp 2 (crossProduct (ofLp E) (ofLp F))

lemma exactCross_sq (E F : E3) :
    ‖exactCross E F‖ ^ 2 = ‖E‖ ^ 2 * ‖F‖ ^ 2 - ⟪E, F⟫ ^ 2 := by
  simp_rw [exactCross, norm_sq_eq_re_inner (𝕜 := ℝ), EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, RCLike.re_to_real, cross_dot_cross, dotProduct_comm (ofLp F) (ofLp E), sq]

/-- The perpendicular height over the first edge, established by squared norms.
There is no angle lower bound. -/
lemma orthogonal_height {E F : E3} (hE : E ≠ 0) :
    ‖F - (⟪E, F⟫ / ‖E‖ ^ 2) • E‖ = ‖exactCross E F‖ / ‖E‖ := by
  have ha : 0 < ‖E‖ := norm_pos_iff.mpr hE
  have han : ‖E‖ ≠ 0 := ne_of_gt ha
  have hc := exactCross_sq E F
  have hs : ‖F - (⟪E, F⟫ / ‖E‖ ^ 2) • E‖ ^ 2 * ‖E‖ ^ 2 = ‖exactCross E F‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm F E,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
    rw [real_inner_comm E F]
    nlinarith only [hc]
  apply (sq_eq_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) ha.le)).mp
  rw [div_pow]
  exact (eq_div_iff (pow_ne_zero 2 han)).2 hs

/-- If the area divided by the first-edge length is at most k, every triangle
point is within k of AC or BC. Handles a zero first edge separately. -/
theorem thin_triangle_edge_witness {R E F : E3} {u v k : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) (hk : 0 ≤ k)
    (harea : ‖exactCross E F‖ ≤ k * ‖E‖) :
    ∃ u' v' : ℝ, 0 ≤ u' ∧ 0 ≤ v' ∧ u' + v' ≤ 1 ∧
      (u' = 0 ∨ u' + v' = 1) ∧
      ‖residual R E F u v - residual R E F u' v'‖ ≤ k := by
  by_cases hE : E = 0
  · obtain ⟨u', v', hu', hv', huv', he, hd⟩ := short_base_edge_witness (R := R) (E := E) (F := F) hu hv huv
    refine ⟨u', v', hu', hv', huv', he, hd.trans ?_⟩
    simpa only [hE, norm_zero, zero_div] using hk
  · let c := ⟪E, F⟫ / ‖E‖ ^ 2
    let H := F - c • E
    have hF : F = c • E + H := by dsimp [H]; module
    obtain ⟨u', v', hu', hv', huv', he, hd⟩ := height_edge_witness (R := R) hF hu hv huv
    refine ⟨u', v', hu', hv', huv', he, hd.trans ?_⟩
    dsimp [H, c]
    rw [orthogonal_height hE]
    exact (div_le_iff₀ (norm_pos_iff.mpr hE)).2 harea

/-- Specialization of the thin-normal fallback threshold proposed in the IEEE
analysis: ||N|| ≤ 16 rho ||E|| D. -/
theorem roundoff_thin_edge_witness {R E F : E3} {u v rho D : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1)
    (hrho : 0 ≤ rho) (hD : 0 ≤ D)
    (harea : ‖exactCross E F‖ ≤ 16 * rho * ‖E‖ * D) :
    ∃ u' v' : ℝ, 0 ≤ u' ∧ 0 ≤ v' ∧ u' + v' ≤ 1 ∧
      (u' = 0 ∨ u' + v' = 1) ∧
      ‖residual R E F u v - residual R E F u' v'‖ ≤ 16 * rho * D := by
  apply thin_triangle_edge_witness hu hv huv (by positivity)
  nlinarith only [harea]

/-- Combined thin-normal and underflow-area fallback. The base-length split
prevents dividing an absolute area error by an arbitrarily short edge. -/
theorem combined_thin_edge_witness {R E F : E3} {u v rho D h : ℝ}
    (hu : 0≤u) (hv : 0≤v) (huv : u+v≤1)
    (hrho : 0≤rho) (hD : 0≤D) (hh : 0≤h)
    (hthin : ‖E‖≤h ∨ ‖exactCross E F‖≤16*rho*‖E‖*D ∨ ‖exactCross E F‖≤h^2) :
    ∃ u' v' : ℝ, 0≤u' ∧ 0≤v' ∧ u'+v'≤1 ∧ (u'=0 ∨ u'+v'=1) ∧
      ‖residual R E F u v-residual R E F u' v'‖≤16*rho*D+h := by
  by_cases he : ‖E‖≤h
  · obtain ⟨u',v',hu',hv',huv',hbd,hd⟩ := short_base_edge_witness (R := R) (E := E) (F := F) hu hv huv
    exact ⟨u',v',hu',hv',huv',hbd,hd.trans (by nlinarith [mul_nonneg hrho hD])⟩
  · apply thin_triangle_edge_witness hu hv huv (by positivity)
    rcases hthin with hsmall | harea | harea
    · exact False.elim (he hsmall)
    · nlinarith [mul_nonneg hh (norm_nonneg E)]
    · have hp := mul_nonneg (norm_nonneg E) (mul_nonneg hrho hD)
      have hq := mul_nonneg hh (show 0≤‖E‖-h by linarith)
      nlinarith

end DistanceAccuracy.GeometryCoverage

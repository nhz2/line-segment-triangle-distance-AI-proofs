import DistanceAccuracy.GeometryThin

namespace DistanceAccuracy.GeometryCoverage
open scoped RealInnerProductSpace
open Matrix WithLp

/-- Polynomial Gram identity behind orthogonal projection onto a triangle's
plane. It is valid without independence assumptions. -/
lemma plane_gram_identity (R E F : E3) :
    ‖exactCross E F‖^2 • R+
      (inner ℝ E F*inner ℝ F R-‖F‖^2*inner ℝ E R) • E+
      (inner ℝ E F*inner ℝ E R-‖E‖^2*inner ℝ F R) • F =
      inner ℝ (exactCross E F) R • exactCross E F := by
  rw [exactCross_sq]
  ext i
  fin_cases i <;>
    simp [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct,Fin.sum_univ_succ,exactCross,crossProduct] <;> ring

/-- Every point has an affine barycentric projection onto a nondegenerate
triangle plane. Its residual norm equals the exact normal height. The weights
are unrestricted here: the boundary interpolation lemma handles outside points. -/
theorem plane_projection_exists (R E F : E3) (hN : exactCross E F ≠ 0) :
    ∃ u v : ℝ, ‖R+u • E+v • F‖ = |inner ℝ (exactCross E F) R|/‖exactCross E F‖ := by
  let N := exactCross E F
  let d := ‖N‖^2
  let u := (inner ℝ E F*inner ℝ F R-‖F‖^2*inner ℝ E R)/d
  let v := (inner ℝ E F*inner ℝ E R-‖E‖^2*inner ℝ F R)/d
  have hnorm : 0 < ‖N‖ := norm_pos_iff.mpr hN
  have hd : d ≠ 0 := ne_of_gt (sq_pos_of_pos hnorm)
  have heq : R+u • E+v • F = (inner ℝ N R/d) • N := by
    have hpoly := plane_gram_identity R E F
    ext i
    have hi := congrArg (fun z : E3 => z i) hpoly
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hi ⊢
    dsimp [u,v]
    field_simp
    nlinarith only [hi]
  refine ⟨u,v,?_⟩
  rw [heq,norm_smul,Real.norm_eq_abs,abs_div,abs_of_nonneg (sq_nonneg ‖N‖)]
  field_simp
  <;> ring

end DistanceAccuracy.GeometryCoverage

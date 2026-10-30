import DistanceAccuracy.GeometryThin
import DistanceAccuracy.ReducedProjection

namespace DistanceAccuracy.LineReduction
open DistanceAccuracy.GeometryCoverage
open scoped RealInnerProductSpace

noncomputable def parameter (E R F : E3) (v : ℝ) : ℝ :=
  -inner ℝ E (R+v•F)/‖E‖^2

lemma exactCross_add_smul (E R F : E3) (v : ℝ) :
    exactCross E (R+v•F) = exactCross E R+v•exactCross E F := by
  ext k
  fin_cases k <;> simp [exactCross, cross_apply] <;> ring

lemma parameter_residual (E R F : E3) (v : ℝ) :
    residual R E F (parameter E R F v) v =
      (R+v•F)-(inner ℝ E (R+v•F)/‖E‖^2)•E := by
  dsimp [GeometryCoverage.residual, parameter]
  module

/-- Eliminating the unconstrained first parameter is exactly a normalized
cross-product problem, including nearly parallel directions. -/
theorem reduced_norm {E R F : E3} (hE : E ≠ 0) (v : ℝ) :
    ‖residual R E F (parameter E R F v) v‖ =
      ‖(‖E‖⁻¹)•exactCross E R+v•((‖E‖⁻¹)•exactCross E F)‖ := by
  rw [parameter_residual, orthogonal_height hE]
  have he : (‖E‖⁻¹)•exactCross E R+v•((‖E‖⁻¹)•exactCross E F) =
      (‖E‖⁻¹)•exactCross E (R+v•F) := by
    rw [exactCross_add_smul]
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg E))]
  ring

lemma reduced_norm_raw {E R F : E3} (hE : E ≠ 0) (v : ℝ) :
    ‖GeometryCoverage.residual R E F (parameter E R F v) v‖ =
      ‖exactCross E R+v•exactCross E F‖/‖E‖ := by
  rw [parameter_residual,orthogonal_height hE,exactCross_add_smul]

lemma parameter_equation {E R F : E3} (hE : E ≠ 0) (v : ℝ) :
    ‖E‖^2*parameter E R F v+inner ℝ E (R+v•F) = 0 := by
  have hn : ‖E‖ ≠ 0 := norm_ne_zero_iff.mpr hE
  dsimp [parameter]
  field_simp
  ring

/-- The exact line minimizer never has a greater residual than any supplied
first parameter. This supplies the first endpoint of a boundary interpolation. -/
theorem line_minimizes {E R F : E3} (hE : E ≠ 0) (u v : ℝ) :
    ‖residual R E F (parameter E R F v) v‖ ≤ ‖residual R E F u v‖ := by
  have hsq0 := ReducedProjection.residual_sq (R+v•F) E (parameter E R F v)
  have hsqu := ReducedProjection.residual_sq (R+v•F) E u
  have hpar := parameter_equation (R := R) (F := F) hE v
  have hdiff : ‖(R+v•F)+u•E‖^2-‖(R+v•F)+(parameter E R F v)•E‖^2 =
      (u-parameter E R F v)^2*‖E‖^2 := by
    rw [hsqu, hsq0]
    dsimp [quadratic]
    linear_combination 2*(u-parameter E R F v)*hpar
  have hp := mul_nonneg (sq_nonneg (u-parameter E R F v)) (sq_nonneg ‖E‖)
  have hle : ‖(R+v•F)+(parameter E R F v)•E‖ ≤ ‖(R+v•F)+u•E‖ := by
    nlinarith [norm_nonneg ((R+v•F)+(parameter E R F v)•E), norm_nonneg ((R+v•F)+u•E)]
  have h0 : residual R E F (parameter E R F v) v = (R+v•F)+(parameter E R F v)•E := by
    dsimp [GeometryCoverage.residual]; module
  have h1 : residual R E F u v = (R+v•F)+u•E := by dsimp [GeometryCoverage.residual]; module
  simpa only [h0, h1] using hle

end DistanceAccuracy.LineReduction

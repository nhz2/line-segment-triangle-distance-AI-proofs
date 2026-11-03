import DistanceAccuracy.ReprojectGeometry
import DistanceAccuracy.UnderflowAbsorption
namespace DistanceAccuracy.ReprojectGeometry
open GeometryCoverage
set_option maxHeartbeats 1500000

lemma line_sq {E R F : E3} (hE : E ≠ 0) (s t : ℝ) :
    ‖residual R E F s t‖^2 =
      ‖residual R E F (LineReduction.parameter E R F t) t‖^2+
        (s-LineReduction.parameter E R F t)^2*‖E‖^2 := by
  have hp := LineReduction.parameter_equation (R := R) (F := F) hE t
  have hid (v : ℝ) : residual R E F v t = (R+t•F)+v•E := by
    dsimp [GeometryCoverage.residual]; module
  simp only [hid, ReducedProjection.residual_sq, quadratic]
  linear_combination 2*(s-LineReduction.parameter E R F t)*hp

lemma line_nearby {E R F : E3} {s t B K C : ℝ} (hE : E ≠ 0)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hline : ‖residual R E F (LineReduction.parameter E R F t) t‖ ≤ B)
    (herr : |s-LineReduction.parameter E R F t| * ‖E‖ ≤ K+C) :
    ‖residual R E F s t‖ ≤ hypot B K+C := by
  have hsq := line_sq (R := R) (F := F) hE s t
  have hb := (sq_le_sq₀ (norm_nonneg _) hB).mpr hline
  have he := (sq_le_sq₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (add_nonneg hK hC)).mpr herr
  rw [mul_pow,sq_abs] at he
  have hh := hypot_sq B K
  have hhk : K ≤ hypot B K := by
    have h := hypot_nonneg B K
    nlinarith only [hh,h,sq_nonneg B]
  nlinarith only [hC,hsq,hb,he,hh, mul_nonneg hC (sub_nonneg.mpr hhk),
    norm_nonneg (residual R E F s t), hypot_nonneg B K]

/-- The actual second solve supplies a witness at its own parameter. Either
it has the correct clipped endpoint, or its line displacement is small. -/
theorem rounded_witness {R E F : E3} {s₀ t₀ t s B K C : ℝ}
    (hE : E ≠ 0) (hs₀ : s₀ ∈ Set.Icc (0:ℝ) 1)
    (ht₀ : t₀ ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hw : ‖residual R E F s₀ t₀‖ ≤ B)
    (hl : ‖residual R E F (LineReduction.parameter E R F t) t‖ ≤ B)
    (hc : (s=0 ∧ LineReduction.parameter E R F t≤0) ∨
      (s=1 ∧ 1≤LineReduction.parameter E R F t) ∨
      |s-LineReduction.parameter E R F t| * ‖E‖ ≤ K+C) :
    ∃ v ∈ Set.Icc (0:ℝ) 1, ‖residual R E F s v‖ ≤ hypot B K+C := by
  rcases hc with ⟨rfl,hu⟩ | ⟨rfl,hu⟩ | he
  · obtain ⟨v,hv,hb⟩ := clipped_witness hs₀ ht₀ ht hw hl
    have hc : clip (LineReduction.parameter E R F t)=0 :=
      max_eq_left ((min_le_right _ _).trans hu)
    rw [hc] at hb
    exact ⟨v,hv,by linarith [le_hypot B K]⟩
  · obtain ⟨v,hv,hb⟩ := clipped_witness hs₀ ht₀ ht hw hl
    have hc : clip (LineReduction.parameter E R F t)=1 := by simp [clip,min_eq_left hu]
    rw [hc] at hb
    exact ⟨v,hv,by linarith [le_hypot B K]⟩
  · exact ⟨t,ht,line_nearby hE hB hK hC hl he⟩

end DistanceAccuracy.ReprojectGeometry

namespace DistanceAccuracy
set_option exponentiation.threshold 2048
lemma third_absolute_gradient {fmt : Format} {A D : ℝ}
    (hA : fourthRoot fmt.leastSubnormal < A) (hAD : A ≤ D) :
    32*fmt.leastSubnormal*(1+A^2)/A ≤ 32*Real.sqrt fmt.leastSubnormal*(1+D) := by
  have hh := fourthRoot_nonneg fmt.leastSubnormal
  have hh1 := fmt.subnormal_root_small
  have hh2 : (fourthRoot fmt.leastSubnormal)^2 = Real.sqrt fmt.leastSubnormal :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hsq : Real.sqrt fmt.leastSubnormal ≤ fourthRoot fmt.leastSubnormal := by nlinarith only [hh,hh1,hh2]
  have hAp : 0 < A := hh.trans_lt hA
  have hs := Real.sq_sqrt fmt.subnormal_nonneg
  have heta : fmt.leastSubnormal ≤ Real.sqrt fmt.leastSubnormal := by
    have hmax : Real.sqrt fmt.leastSubnormal ≤ 1 := hsq.trans (by linarith)
    nlinarith only [hs, Real.sqrt_nonneg fmt.leastSubnormal,hmax]
  have hηA : fmt.leastSubnormal ≤ Real.sqrt fmt.leastSubnormal*A := by
    have h := mul_le_mul_of_nonneg_left (hsq.trans hA.le) (Real.sqrt_nonneg fmt.leastSubnormal)
    nlinarith only [h,hs]
  have hηAD := mul_le_mul_of_nonneg_right heta (sq_nonneg A)
  have hAD' := mul_le_mul_of_nonneg_left hAD (mul_nonneg (Real.sqrt_nonneg fmt.leastSubnormal) hAp.le)
  apply (div_le_iff₀ hAp).mpr
  nlinarith only [hηA,hηAD,hAD']

/-- Two projection losses and the stored norm fit in one subnormal-root
allowance. This larger coefficient is still tiny for both IEEE formats. -/
lemma Format.three_absolute_budget (fmt : Format) {D : ℝ} (hD : 0 ≤ D) :
    100*Real.sqrt fmt.leastSubnormal*(1+D)+6*fmt.leastSubnormal+
      2*Real.sqrt (2*fmt.leastSubnormal) ≤ fourthRoot fmt.leastSubnormal+(1/1000)*fmt.rho*D := by
  let h := fourthRoot fmt.leastSubnormal
  have h0 : 0 ≤ h := fourthRoot_nonneg _
  have h1 : h ≤ (1/1000:ℝ) := by
    apply (pow_le_pow_iff_left₀ h0 (by norm_num : (0:ℝ) ≤ 1/1000) (by decide : (4:ℕ) ≠ 0)).mp
    rw [show h^4=fmt.leastSubnormal from fourthRoot_pow_four fmt.subnormal_nonneg]
    cases fmt <;> norm_num [Format.leastSubnormal]
  have h2 : h^2 = Real.sqrt fmt.leastSubnormal := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h4 : h^4 = fmt.leastSubnormal := fourthRoot_pow_four fmt.subnormal_nonneg
  have he : fmt.leastSubnormal ≤ Real.sqrt fmt.leastSubnormal := by
    nlinarith [mul_nonneg (sq_nonneg h) (show 0 ≤ 1-h^2 by nlinarith)]
  have hc : 110*Real.sqrt fmt.leastSubnormal ≤ h := by nlinarith [mul_nonneg h0 (show 0 ≤ 1-110*h by linarith)]
  have hr : Real.sqrt (2*fmt.leastSubnormal) ≤ 2*Real.sqrt fmt.leastSubnormal := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt fmt.subnormal_nonneg,fmt.subnormal_nonneg]
  have hm := mul_le_mul_of_nonneg_right fmt.sqrt_eta_absorption hD
  have hm0 := mul_nonneg (Real.sqrt_nonneg fmt.leastSubnormal) hD
  change _ ≤ h+(1/1000)*fmt.rho*D
  nlinarith only [he,hc,hr,hm,hm0]
end DistanceAccuracy

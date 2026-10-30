import DistanceAccuracy.LineReduction
import DistanceAccuracy.Bounds

namespace DistanceAccuracy.KernelCoverage
open DistanceAccuracy.GeometryCoverage
open DistanceAccuracy.LineReduction

private lemma norm_le_hypot {r : E3} {B C : ℝ} (hB : 0 ≤ B)
    (h : ‖r‖^2 ≤ B^2+C^2) : ‖r‖ ≤ hypot B C := by
  have hs := hypot_sq B C
  nlinarith [norm_nonneg r, hypot_nonneg B C]

/-- Combining the reduced projection with the second projection or an endpoint
projection costs one squared-loss budget, rather than a sum of distances. -/
theorem segment_kernel {R E F : E3} {u₀ v₀ v B C c₀ c₁ ci selected : ℝ}
    (hB : 0 ≤ B) (hu₀ : u₀ ∈ Set.Icc (0:ℝ) 1)
    (hv₀ : v₀ ∈ Set.Icc (0:ℝ) 1) (hv : v ∈ Set.Icc (0:ℝ) 1)
    (hwitness : ‖GeometryCoverage.residual R E F u₀ v₀‖ ≤ B)
    (hreduced : ‖GeometryCoverage.residual R E F (parameter E R F v) v‖ ≤ B)
    (hinterior : parameter E R F v ∈ Set.Icc (0:ℝ) 1 →
      ci^2 ≤ ‖GeometryCoverage.residual R E F (parameter E R F v) v‖^2+C^2)
    (hzero : ∀ t ∈ Set.Icc (0:ℝ) 1, c₀^2 ≤ ‖GeometryCoverage.residual R E F 0 t‖^2+C^2)
    (hone : ∀ t ∈ Set.Icc (0:ℝ) 1, c₁^2 ≤ ‖GeometryCoverage.residual R E F 1 t‖^2+C^2)
    (hs₀ : selected ≤ c₀) (hs₁ : selected ≤ c₁) (hsi : selected ≤ ci) :
    selected ≤ hypot B C := by
  by_cases hin : parameter E R F v ∈ Set.Icc (0:ℝ) 1
  · have h := hinterior hin
    have hs := mul_self_le_mul_self (norm_nonneg _) hreduced
    have hh := hypot_sq B C
    have hi : ci ≤ hypot B C := by nlinarith [hypot_nonneg B C]
    exact hsi.trans hi
  · have hout : parameter E R F v ≤ 0 ∨ 1 ≤ parameter E R F v := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hin
      exact hin.imp le_of_lt le_of_lt
    obtain ⟨u',v',hu',hv',hh⟩ := segment_boundary_witness hu₀ hv₀ hv hout hwitness hreduced
    have hs := mul_self_le_mul_self (norm_nonneg _) hh
    have he := hypot_sq B C
    rcases hu' with rfl | rfl
    · have h := hzero v' hv'
      have hc : c₀ ≤ hypot B C := by nlinarith [hypot_nonneg B C]
      exact hs₀.trans hc
    · have h := hone v' hv'
      have hc : c₁ ≤ hypot B C := by nlinarith [hypot_nonneg B C]
      exact hs₁.trans hc

/-- Exact capping either realizes the virtual shortened-interval projection or
puts it on BC. An outside line minimizer supplies an AC/BC witness instead. -/
theorem face_or_edge {R E F : E3} {u₀ v₀ v raw B C : ℝ}
    (hB : 0 ≤ B) (hu₀ : 0 ≤ u₀) (hv₀ : 0 ≤ v₀) (huv₀ : u₀+v₀ ≤ 1)
    (hv : v ∈ Set.Icc (0:ℝ) 1)
    (hwitness : ‖GeometryCoverage.residual R E F u₀ v₀‖ ≤ B)
    (hreduced : ‖GeometryCoverage.residual R E F (parameter E R F v) v‖ ≤ B)
    (hvirtual : parameter E R F v ∈ Set.Icc 0 (1-v) →
      ‖GeometryCoverage.residual R E F (max 0 (min (1-v) raw)) v‖^2 ≤
        ‖GeometryCoverage.residual R E F (parameter E R F v) v‖^2+C^2) :
    ‖GeometryCoverage.residual R E F (max 0 (min 1 raw)) (min v (1-max 0 (min 1 raw)))‖ ≤ hypot B C ∨
    ∃ u' v' : ℝ, 0 ≤ u' ∧ 0 ≤ v' ∧ u'+v' ≤ 1 ∧ (u'=0 ∨ u'+v'=1) ∧
      ‖GeometryCoverage.residual R E F u' v'‖ ≤ hypot B C := by
  by_cases hin : parameter E R F v ∈ Set.Icc 0 (1-v)
  · have hsq := hvirtual hin
    have hs := mul_self_le_mul_self (norm_nonneg _) hreduced
    have hnorm : ‖GeometryCoverage.residual R E F (max 0 (min (1-v) raw)) v‖ ≤ hypot B C :=
      norm_le_hypot hB (by nlinarith)
    rcases face_cap_coverage (q := raw) hv.1 hv.2 with ⟨hu,hcap⟩ | hboundary
    · left
      rw [hcap,hu]
      exact hnorm
    · right
      refine ⟨max 0 (min (1-v) raw), v, le_max_left _ _, hv.1, ?_, Or.inr hboundary, hnorm⟩
      linarith
  · have hout : parameter E R F v ≤ 0 ∨ 1 ≤ parameter E R F v+v := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hin
      rcases hin with h | h
      · exact Or.inl h.le
      · exact Or.inr (by linarith)
    obtain ⟨u',v',hu',hv',huv',he,hnorm⟩ := triangle_boundary_witness hu₀ huv₀
      ⟨hv₀, by linarith⟩ hv hout hwitness hreduced
    right
    refine ⟨u',v',hu',hv',huv',he,hnorm.trans ?_⟩
    have hh := hypot_sq B C
    nlinarith [hypot_nonneg B C, sq_nonneg C]

end DistanceAccuracy.KernelCoverage

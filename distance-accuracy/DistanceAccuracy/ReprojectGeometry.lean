import DistanceAccuracy.LineReduction

/-! Exact geometry for the clamp-and-reproject segment kernel. These theorems do
not assert an IEEE rounding bound. Division here is real division (0/0 = 0). -/
namespace DistanceAccuracy.ReprojectGeometry
open GeometryCoverage

noncomputable def clip (t : ℝ) : ℝ := max 0 (min 1 t)

lemma clip_mem (t : ℝ) : clip t ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Interpolation produces a witness on the *particular* endpoint selected
by clipping, rather than merely on one of the two endpoints. -/
theorem clipped_witness {R E F : E3} {u₀ v₀ u₁ v₁ B : ℝ}
    (hu₀ : u₀ ∈ Set.Icc (0:ℝ) 1)
    (hv₀ : v₀ ∈ Set.Icc (0:ℝ) 1) (hv₁ : v₁ ∈ Set.Icc (0:ℝ) 1)
    (h₀ : ‖residual R E F u₀ v₀‖ ≤ B)
    (h₁ : ‖residual R E F u₁ v₁‖ ≤ B) :
    ∃ v ∈ Set.Icc (0:ℝ) 1, ‖residual R E F (clip u₁) v‖ ≤ B := by
  have interpolate (target : ℝ)
      (hbetween : target ∈ Set.Icc (min u₀ u₁) (max u₀ u₁)) :
      ∃ v ∈ Set.Icc (0:ℝ) 1, ‖residual R E F target v‖ ≤ B := by
    have hc : Continuous (mix u₀ u₁) := by unfold mix; fun_prop
    have hends : mix u₀ u₁ 0 = u₀ ∧ mix u₀ u₁ 1 = u₁ := by simp [mix]
    have ht : target ∈ Set.uIcc (mix u₀ u₁ 0) (mix u₀ u₁ 1) := by
      simpa [hends.1, hends.2, Set.uIcc] using hbetween
    obtain ⟨t, ht, he⟩ := intermediate_value_uIcc (a := (0:ℝ)) (b := 1) hc.continuousOn ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := by simpa [Set.uIcc] using ht
    refine ⟨mix v₀ v₁ t,
      ⟨mix_nonneg hv₀.1 hv₁.1 ht'.1 ht'.2, mix_le_one hv₀.2 hv₁.2 ht'.1 ht'.2⟩, ?_⟩
    rw [← he]
    exact residual_mix_le h₀ h₁ ht'.1 ht'.2
  by_cases hlo : u₁ ≤ 0
  · have he : clip u₁ = 0 := by simp [clip, min_eq_right (show u₁ ≤ 1 by linarith), max_eq_left hlo]
    rw [he]
    exact interpolate 0 ⟨(min_le_right _ _).trans hlo, hu₀.1.trans (le_max_left _ _)⟩
  · by_cases hhi : 1 ≤ u₁
    · have he : clip u₁ = 1 := by simp [clip, min_eq_left hhi]
      rw [he]
      exact interpolate 1 ⟨(min_le_left _ _).trans hu₀.2, hhi.trans (le_max_right _ _)⟩
    · have he : clip u₁ = u₁ := by
        rw [clip, min_eq_right (le_of_not_ge hhi), max_eq_right (le_of_not_ge hlo)]
      exact ⟨v₁, hv₁, by simpa [he] using h₁⟩

noncomputable def project (k n : E3) : ℝ := clip (-inner ℝ n k / ‖n‖^2)

lemma project_mem (k n : E3) : project k n ∈ Set.Icc (0:ℝ) 1 := clip_mem _

lemma project_minimizes (k n : E3) {v : ℝ} (hv : v ∈ Set.Icc (0:ℝ) 1) :
    ‖k + project k n • n‖ ≤ ‖k + v • n‖ := by
  by_cases hn : n = 0
  · simp [hn]
  have ha : 0 < ‖n‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  have ho := clamp_optimal (b := inner ℝ n k) ha (by norm_num : (0:ℝ) ≤ 1) hv.1 hv.2
  have hl := projection_loss (b := inner ℝ n k) (c := ‖k‖^2) ha ho
  have hs : ‖k + project k n • n‖^2 ≤ ‖k + v • n‖^2 := by
    rw [ReducedProjection.residual_sq, ReducedProjection.residual_sq]
    simpa [project, clip] using hl
  nlinarith [norm_nonneg (k + project k n • n), norm_nonneg (k + v • n)]

noncomputable def first (P Q R : E3) : ℝ := project (exactCross P R) (exactCross P Q)
noncomputable def second (P Q R : E3) : ℝ := project (R + first P Q R • Q) (-P)
noncomputable def third (P Q R : E3) : ℝ := project (R - second P Q R • P) Q
noncomputable def separation (P Q R : E3) : E3 :=
  R + third P Q R • Q - second P Q R • P

/-- All three exact scalar solves, including zero and parallel directions,
return a globally closest pair of points of the two segments. -/
theorem minimizes (P Q R : E3) {s t : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ‖separation P Q R‖ ≤ ‖R + t • Q - s • P‖ := by
  by_cases hp : P = 0
  · simpa [separation, third, hp] using project_minimizes R Q ht
  let v := first P Q R
  let u := LineReduction.parameter (-P) R Q v
  have hu : second P Q R = clip u := by
    simp [second, project, u, v, LineReduction.parameter]
  have hv : v ∈ Set.Icc (0:ℝ) 1 := project_mem _ _
  have hmin : ‖residual R (-P) Q u v‖ ≤ ‖residual R (-P) Q s t‖ := by
    have hcross := project_minimizes (exactCross P R) (exactCross P Q) ht
    have hline := LineReduction.line_minimizes (R := R) (F := Q) hp (-s) t
    have hraw := LineReduction.reduced_norm_raw (R := R) (F := Q) hp v
    have hraw' := LineReduction.reduced_norm_raw (R := R) (F := Q) hp t
    have hid : residual R (-P) Q u v = residual R P Q (LineReduction.parameter P R Q v) v := by
      simp [u, LineReduction.parameter, GeometryCoverage.residual, inner_neg_left, neg_smul, neg_div]
    rw [hid, hraw]
    have hdiv := div_le_div_of_nonneg_right hcross (norm_nonneg P)
    change ‖exactCross P R + v • exactCross P Q‖ / ‖P‖ ≤ _ at hdiv
    rw [← hraw'] at hdiv
    have hr : residual R P Q (-s) t = residual R (-P) Q s t := by dsimp [GeometryCoverage.residual]; module
    exact hdiv.trans (by simpa [hr] using hline)
  obtain ⟨v', hv', hb⟩ := clipped_witness hs ht hv (le_refl _) hmin
  have hfinal := project_minimizes (R - second P Q R • P) Q hv'
  have hid : separation P Q R = (R - second P Q R • P) + third P Q R • Q := by
    dsimp [separation]; module
  rw [hid]
  change ‖(R - second P Q R • P) + project (R - second P Q R • P) Q • Q‖ ≤ _
  apply hfinal.trans
  rw [← hu] at hb
  convert hb using 1 <;> congr 1 <;> dsimp [GeometryCoverage.residual] <;> module

/-- The three projections use precisely the scalar numerators in the source
when dot products and FMA are interpreted in exact real arithmetic. -/
lemma first_formula (P Q R : E3) :
    first P Q R = clip (-inner ℝ (exactCross P Q) (exactCross P R) /
      inner ℝ (exactCross P Q) (exactCross P Q)) := by
  simp [first, project]

lemma second_formula (P Q R : E3) :
    second P Q R = clip ((first P Q R * inner ℝ P Q + inner ℝ P R) /
      inner ℝ P P) := by
  simp [second, project, inner_neg_left,
    inner_add_right, inner_smul_right, add_comm]

lemma third_formula (P Q R : E3) :
    third P Q R = clip ((second P Q R * inner ℝ P Q - inner ℝ Q R) /
      inner ℝ Q Q) := by
  simp [third, project, inner_sub_right,
    inner_smul_right, real_inner_comm Q P, neg_sub]

end DistanceAccuracy.ReprojectGeometry

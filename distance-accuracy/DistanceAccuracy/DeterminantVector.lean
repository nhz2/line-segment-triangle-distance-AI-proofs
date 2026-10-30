import DistanceAccuracy.Determinant
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DistanceAccuracy.Determinant

abbrev E3 := EuclideanSpace ℝ (Fin 3)

noncomputable def absVec (v : E3) : E3 := WithLp.toLp 2 (fun i => |v i|)
noncomputable def ones : E3 := WithLp.toLp 2 (fun _ => (1 : ℝ))

lemma norm_absVec (v : E3) : ‖absVec v‖ = ‖v‖ := by
  have h : ‖absVec v‖ ^ 2 = ‖v‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, absVec]
  nlinarith [norm_nonneg (absVec v), norm_nonneg v]

lemma norm_ones : ‖ones‖ = Real.sqrt 3 := by
  have h : ‖ones‖ ^ 2 = 3 := by
    norm_num [EuclideanSpace.real_norm_sq_eq, ones, Fin.sum_univ_succ]
  have hs : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg ones, Real.sqrt_nonneg (3 : ℝ)]

lemma norm_le_of_coordinate_bounds {r u : E3} (hu : ∀ i, 0 ≤ u i)
    (h : ∀ i, |r i| ≤ u i) : ‖r‖ ≤ ‖u‖ := by
  have hsq : ‖r‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    have hi := h i
    have hui := hu i
    nlinarith [sq_abs (r i), mul_nonneg (sub_nonneg.mpr hi) (show 0 ≤ u i + |r i| by positivity)]
  nlinarith [norm_nonneg r, norm_nonneg u]

/-- Lift coordinatewise mixed errors to a Euclidean norm bound. -/
theorem vector_mixed_bound {r n p : E3} {alpha beta delta : ℝ}
    (ha : 0 ≤ alpha) (hb : 0 ≤ beta) (hd : 0 ≤ delta)
    (h : ∀ i, |r i| ≤ alpha * |n i| + beta * |p i| + delta) :
    ‖r‖ ≤ alpha * ‖n‖ + beta * ‖p‖ + delta * Real.sqrt 3 := by
  let u : E3 := alpha • absVec n + beta • absVec p + delta • ones
  have hu : ∀ i, u i = alpha * |n i| + beta * |p i| + delta := by
    intro i
    simp [u, absVec, ones]
  have hru : ‖r‖ ≤ ‖u‖ := norm_le_of_coordinate_bounds
    (fun i => by rw [hu]; positivity) (fun i => by rw [hu]; exact h i)
  have hn := norm_add_le (alpha • absVec n + beta • absVec p) (delta • ones)
  have hn' := norm_add_le (alpha • absVec n) (beta • absVec p)
  have hnorm : ‖u‖ ≤ alpha * ‖n‖ + beta * ‖p‖ + delta * Real.sqrt 3 := by
    dsimp [u]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
      abs_of_nonneg hd, norm_absVec, norm_ones] at hn hn' ⊢
    linarith
  exact hru.trans hnorm

/-- Three compensated determinants retain only a second-order product term.
The 4eta absolute term comes from 2sqrt(3)eta < 4eta. -/
theorem compensated_vector_bound {r n p : E3} {rho eta : ℝ}
    (hr : 0 ≤ rho) (he : 0 ≤ eta)
    (h : ∀ i, |r i| ≤ (2 * rho + rho ^ 2) * |n i| +
      rho ^ 2 * (1 + rho) * |p i| + 2 * eta) :
    ‖r‖ ≤ (2 * rho + rho ^ 2) * ‖n‖ +
      rho ^ 2 * (1 + rho) * ‖p‖ + 4 * eta := by
  have hv := vector_mixed_bound (by positivity) (by positivity) (by positivity) h
  have hs : Real.sqrt (3 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hm := mul_le_mul_of_nonneg_right hs he
  nlinarith

/-- The second-order term divided by the triangle area is small outside the
thin-triangle branch. B represents the coordinate bound on the second vector. -/
theorem thick_normal_bound {rho eta A D N error : ℝ}
    (hr : 0 < rho) (hA : 0 < A) (hD : 0 < D) (hN : 0 < N)
    (he : 0 ≤ eta)
    (harea : 16 * rho * A * D ≤ N)
    (herr : error ≤ (2 * rho + rho ^ 2) * N +
      rho ^ 2 * (1 + rho) * (A * D / Real.sqrt 3) + 4 * eta) :
    error / N ≤ 2 * rho + rho ^ 2 +
      rho * (1 + rho) / (16 * Real.sqrt 3) + 4 * eta / N := by
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  apply (div_le_iff₀ hN).2
  have ht := mul_le_mul_of_nonneg_right harea
    (show 0 ≤ rho * (1 + rho) / (16 * Real.sqrt 3) by positivity)
  have heq : rho ^ 2 * (1 + rho) * (A * D / Real.sqrt 3) =
      (16 * rho * A * D) * (rho * (1 + rho) / (16 * Real.sqrt 3)) := by ring
  rw [heq] at herr
  have hcancel : (4 * eta / N) * N = 4 * eta := div_mul_cancel₀ _ (ne_of_gt hN)
  nlinarith

/-- A cyclic vector of products has norm bounded by the maximum coordinate
of the second input times the norm of the first. -/
noncomputable def selectedProducts (a b : E3) : E3 :=
  WithLp.toLp 2 ![a 2 * b 1, a 0 * b 2, a 1 * b 0]

lemma selectedProducts_bound {a b : E3} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i, |b i| ≤ B) : ‖selectedProducts a b‖ ≤ ‖a‖ * B := by
  have hsq (i j : Fin 3) : (a i * b j) ^ 2 ≤ (a i) ^ 2 * B ^ 2 := by
    have hb' : (b j) ^ 2 ≤ B ^ 2 := by
      have h := hb j
      nlinarith [sq_abs (b j), mul_nonneg (sub_nonneg.mpr h)
        (show 0 ≤ B + |b j| by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (a i)) (sub_nonneg.mpr hb')]
  have hn : ‖selectedProducts a b‖ ^ 2 ≤ ‖a‖ ^ 2 * B ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    simp [selectedProducts, Fin.sum_univ_succ]
    nlinarith [hsq 2 1, hsq 0 2, hsq 1 0]
  nlinarith [norm_nonneg (selectedProducts a b), norm_nonneg a,
    mul_nonneg (norm_nonneg a) hB]

/-- At binary32 precision or finer, the thick-triangle extra relative term is
less than 0.037 rho; this replaces the much deeper pure-relative Kahan bound. -/
lemma thick_extra_budget {rho : ℝ} (hr : 0 ≤ rho)
    (hrmax : rho ≤ 1 / 16777216) :
    rho ^ 2 + rho * (1 + rho) / (16 * Real.sqrt 3) ≤ (37 / 1000) * rho := by
  have hs : (173 / 100 : ℝ) ≤ Real.sqrt 3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hspos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : rho ^ 2 ≤ rho / 16777216 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hrmax)]
  have hprod := mul_nonneg (show 0 ≤ (37 / 1000 : ℝ) * rho - rho ^ 2 by nlinarith)
    (sub_nonneg.mpr hs)
  have hd : rho * (1 + rho) / (16 * Real.sqrt 3) ≤ (37 / 1000) * rho - rho ^ 2 := by
    apply (div_le_iff₀ (show 0 < 16 * Real.sqrt (3 : ℝ) by positivity)).2
    nlinarith
  linarith

/-- A fourth-power subnormal floor makes the normalized absolute term small. -/
lemma thick_floor_budget {eta h N : ℝ} (hh : 0 < h) (he : eta = h ^ 4)
    (hN : h ^ 2 ≤ N) : 4 * eta / N ≤ 4 * h ^ 2 := by
  have hNp : 0 < N := lt_of_lt_of_le (sq_pos_of_pos hh) hN
  apply (div_le_iff₀ hNp).2
  rw [he]
  nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hN)]

/-- Complete normalized normal-error budget in the thick, above-floor case. -/
theorem thick_normal_budget {rho eta h A D N error : ℝ}
    (hr : 0 < rho) (hrmax : rho ≤ 1 / 16777216)
    (hA : 0 < A) (hD : 0 < D) (hh : 0 < h)
    (he : eta = h ^ 4) (hfloor : h ^ 2 ≤ N)
    (harea : 16 * rho * A * D ≤ N)
    (herr : error ≤ (2 * rho + rho ^ 2) * N +
      rho ^ 2 * (1 + rho) * (A * D / Real.sqrt 3) + 4 * eta) :
    error / N ≤ (2037 / 1000) * rho + 4 * h ^ 2 := by
  have hNp : 0 < N := lt_of_lt_of_le (sq_pos_of_pos hh) hfloor
  have heta : 0 ≤ eta := by rw [he]; positivity
  have hn := thick_normal_bound hr hA hD hNp heta harea herr
  have hx := thick_extra_budget (le_of_lt hr) hrmax
  have hf := thick_floor_budget hh he hfloor
  linarith

noncomputable def exactCross (a b : E3) : E3 :=
  WithLp.toLp 2 ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0]

noncomputable def compensatedCross (F : FP.IEEE.Format) (a b : E3) : E3 :=
  WithLp.toLp 2 ![kahan F (a 1) (b 2) (a 2) (b 1),
    kahan F (a 2) (b 0) (a 0) (b 2), kahan F (a 0) (b 1) (a 1) (b 0)]

/-- Vector determinant accuracy derived from the representability of the
inputs and finite products, with no assumed determinant accuracy estimates. -/
theorem compensated_cross_error (F : FP.IEEE.Format)
    {a b : E3} {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ i, |b i| ≤ B)
    (ha : ∀ i, F.Representable (a i)) (hb : ∀ i, F.Representable (b i))
    (hfinite : ∀ i j, |a i * b j| < F.overflowThreshold)
    (hrmax : F.unitRoundoff ≤ 1 / 4) :
    ‖compensatedCross F a b - exactCross a b‖ ≤
      (2 * F.unitRoundoff + F.unitRoundoff ^ 2) * ‖exactCross a b‖ +
      F.unitRoundoff ^ 2 * (1 + F.unitRoundoff) * (‖a‖ * B) +
      4 * F.minSubnormal := by
  have hr := F.unitRoundoff_pos
  have he : 0 < F.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hv := compensated_vector_bound (le_of_lt hr) (le_of_lt he)
    (r := compensatedCross F a b - exactCross a b) (n := exactCross a b)
    (p := selectedProducts a b) (by
      intro i
      fin_cases i
      · exact kahan_mixed_error F (ha 2) (hb 1) (hfinite 2 1) hrmax
      · exact kahan_mixed_error F (ha 0) (hb 2) (hfinite 0 2) hrmax
      · exact kahan_mixed_error F (ha 1) (hb 0) (hfinite 1 0) hrmax)
  have hp := selectedProducts_bound (a := a) hB hbB
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ F.unitRoundoff ^ 2 * (1 + F.unitRoundoff) by positivity)
  linarith

end DistanceAccuracy.Determinant

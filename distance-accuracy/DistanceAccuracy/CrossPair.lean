import DistanceAccuracy.OrdinaryCross
import DistanceAccuracy.GeometryThin

namespace DistanceAccuracy.Determinant
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge

lemma exactCross_norm_le (a b : E3) : ‖exactCross a b‖ ≤ ‖a‖*‖b‖ := by
  have h := GeometryCoverage.exactCross_sq a b
  change ‖exactCross a b‖^2 = _ at h
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow]
  nlinarith [sq_nonneg (inner ℝ a b)]

lemma ordinary_pair_coefficient {rho : ℝ} (hr : 0 ≤ rho) (hrmax : rho ≤ 1/16777216) :
    2+2*(1+rho)/Real.sqrt 3 ≤ (3.16 : ℝ) := by
  have hs : (173/100 : ℝ) ≤ Real.sqrt 3 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr; norm_num
  have hfrac := div_le_div₀ (by positivity : 0 ≤ 2*(1+rho)) (by rfl : 2*(1+rho) ≤ 2*(1+rho))
    (by norm_num : (0:ℝ) < 173/100) hs
  nlinarith

/-- A pair of actual ordinary cross products has the joint 3.17 envelope.
The tiny absolute cross errors are absorbed using the explicit eta budget. -/
theorem ordinary_cross_pair (I : Interchange) [I.Valid]
    {e f r : Vec3 I} {E F R : Fin 3 → ℚ} {D P : ℝ}
    (he : ∀ k, value? I (e k) = some (E k))
    (hf : ∀ k, value? I (f k) = some (F k))
    (hr : ∀ k, value? I (r k) = some (R k))
    (hD : 0 ≤ D) (hF : ‖realVec F‖ ≤ D) (hR : ‖realVec R‖ ≤ D)
    (hFc : ∀ k, |(F k : ℝ)| ≤ D/Real.sqrt 3)
    (hRc : ∀ k, |(R k : ℝ)| ≤ D/Real.sqrt 3)
    (hP : 0 < P)
    (hEF : ∀ i j, |(E i : ℝ)*(F j : ℝ)| ≤ P)
    (hER : ∀ i j, |(E i : ℝ)*(R j : ℝ)| ≤ P)
    (heta : I.format.minSubnormal ≤ P)
    (hrmax : I.format.unitRoundoff ≤ 1/16777216)
    (hlim : 10*P < I.format.overflowThreshold)
    (habs : I.format.minSubnormal ≤ I.format.unitRoundoff*‖realVec E‖*D/1000) :
    ∃ N K : Fin 3 → ℚ,
      (∀ k, value? I (cross3 I e f k) = some (N k)) ∧
      (∀ k, value? I (cross3 I e r k) = some (K k)) ∧
      ‖realVec N-exactCross (realVec E) (realVec F)‖+
        ‖realVec K-exactCross (realVec E) (realVec R)‖ ≤ 3.17*I.format.unitRoundoff*‖realVec E‖*D ∧
      ‖realVec N‖ ≤ (1+4*I.format.unitRoundoff)*(‖realVec E‖*D) ∧
      ‖realVec K‖ ≤ (1+4*I.format.unitRoundoff)*(‖realVec E‖*D) := by
  have hρ := I.format.unitRoundoff_pos.le
  obtain ⟨N,hN,hNe⟩ := word_cross3_exists_error I he hf (by positivity) hFc hP hEF heta (by linarith) hlim
  obtain ⟨K,hK,hKe⟩ := word_cross3_exists_error I he hr (by positivity) hRc hP hER heta (by linarith) hlim
  have hn : ‖exactCross (realVec E) (realVec F)‖ ≤ ‖realVec E‖*D :=
    (exactCross_norm_le _ _).trans (mul_le_mul_of_nonneg_left hF (norm_nonneg _))
  have hk : ‖exactCross (realVec E) (realVec R)‖ ≤ ‖realVec E‖*D :=
    (exactCross_norm_le _ _).trans (mul_le_mul_of_nonneg_left hR (norm_nonneg _))
  have hn' := mul_le_mul_of_nonneg_left hn hρ
  have hk' := mul_le_mul_of_nonneg_left hk hρ
  have hc := mul_le_mul_of_nonneg_right (ordinary_pair_coefficient hρ hrmax)
    (show 0 ≤ I.format.unitRoundoff*‖realVec E‖*D by positivity)
  have heq : (2+2*(1+I.format.unitRoundoff)/Real.sqrt 3)*(I.format.unitRoundoff*‖realVec E‖*D) =
      2*I.format.unitRoundoff*‖realVec E‖*D+
      2*I.format.unitRoundoff*(1+I.format.unitRoundoff)*(‖realVec E‖*(D/Real.sqrt 3)) := by ring
  rw [heq] at hc
  have hpair : ‖realVec N-exactCross (realVec E) (realVec F)‖+
      ‖realVec K-exactCross (realVec E) (realVec R)‖ ≤ 3.17*I.format.unitRoundoff*‖realVec E‖*D := by
    nlinarith [mul_nonneg hρ (mul_nonneg (norm_nonneg (realVec E)) hD)]
  refine ⟨N,K,hN,hK,hpair,?_,?_⟩
  · have h := norm_sub_le (realVec N-exactCross (realVec E) (realVec F)) (-(exactCross (realVec E) (realVec F)))
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at h
    nlinarith [norm_nonneg (realVec K-exactCross (realVec E) (realVec R)),
      mul_nonneg hρ (mul_nonneg (norm_nonneg (realVec E)) hD)]
  · have h := norm_sub_le (realVec K-exactCross (realVec E) (realVec R)) (-(exactCross (realVec E) (realVec R)))
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at h
    nlinarith [norm_nonneg (realVec N-exactCross (realVec E) (realVec F)),
      mul_nonneg hρ (mul_nonneg (norm_nonneg (realVec E)) hD)]

lemma accurate_pair_coefficient {rho : ℝ} (hr : 0 ≤ rho)
    (hrmax : rho ≤ 1 / 16777216) :
    3 + rho + (1 + rho) ^ 2 / Real.sqrt 3 ≤ (3.58 : ℝ) := by
  have hs : (173 / 100 : ℝ) ≤ Real.sqrt 3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hr2 : rho ^ 2 ≤ rho / 16777216 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrmax)]
  have hU : (1 + rho) ^ 2 ≤ (1000001 / 1000000 : ℝ) := by nlinarith
  have hfrac : (1 + rho) ^ 2 / Real.sqrt 3 ≤ (1000001 / 1000000 : ℝ) / (173 / 100) :=
    div_le_div₀ (by norm_num) hU (by norm_num) hs
  nlinarith

theorem accurate_cross_pair (I : Interchange) [I.Valid]
    {e f r : Vec3 I} {E F R : Fin 3 → ℚ} {D P : ℝ}
    (he : ∀ k, value? I (e k) = some (E k))
    (hf : ∀ k, value? I (f k) = some (F k))
    (hr : ∀ k, value? I (r k) = some (R k))
    (hD : 0 ≤ D) (hF : ‖realVec F‖ ≤ D) (hR : ‖realVec R‖ ≤ D)
    (hFc : ∀ k, |(F k : ℝ)| ≤ D/Real.sqrt 3)
    (hRc : ∀ k, |(R k : ℝ)| ≤ D/Real.sqrt 3)
    (hP : 0 < P)
    (hEF : ∀ i j, |(E i : ℝ)*(F j : ℝ)| ≤ P)
    (hER : ∀ i j, |(E i : ℝ)*(R j : ℝ)| ≤ P)
    (heta : I.format.minSubnormal ≤ P)
    (hrmax : I.format.unitRoundoff ≤ 1/16777216)
    (hlim : 10*P < I.format.overflowThreshold)
    (habs : I.format.minSubnormal ≤ I.format.unitRoundoff*‖realVec E‖*D/1000) :
    ∃ N K : Fin 3 → ℚ,
      (∀ k, value? I (cross3Accurate I e f k) = some (N k)) ∧
      (∀ k, value? I (cross3 I e r k) = some (K k)) ∧
      ‖realVec N-exactCross (realVec E) (realVec F)‖+
        ‖realVec K-exactCross (realVec E) (realVec R)‖ ≤ 3.60*I.format.unitRoundoff*‖realVec E‖*D ∧
      ‖realVec N‖ ≤ (1+4*I.format.unitRoundoff)*(‖realVec E‖*D) ∧
      ‖realVec K‖ ≤ (1+4*I.format.unitRoundoff)*(‖realVec E‖*D) := by
  have hρ := I.format.unitRoundoff_pos.le
  obtain ⟨N,hN,hNe⟩ := word_cross3Accurate_exists_error I he hf (by positivity) hFc hP hEF heta (by linarith) hlim
  obtain ⟨K,hK,hKe⟩ := word_cross3_exists_error I he hr (by positivity) hRc hP hER heta (by linarith) hlim
  have hn : ‖exactCross (realVec E) (realVec F)‖ ≤ ‖realVec E‖*D :=
    (exactCross_norm_le _ _).trans (mul_le_mul_of_nonneg_left hF (norm_nonneg _))
  have hk : ‖exactCross (realVec E) (realVec R)‖ ≤ ‖realVec E‖*D :=
    (exactCross_norm_le _ _).trans (mul_le_mul_of_nonneg_left hR (norm_nonneg _))
  have hn' := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*I.format.unitRoundoff+I.format.unitRoundoff^2 by positivity)
  have hk' := mul_le_mul_of_nonneg_left hk hρ
  have hc := mul_le_mul_of_nonneg_right (accurate_pair_coefficient hρ hrmax)
    (show 0 ≤ I.format.unitRoundoff*‖realVec E‖*D by positivity)
  have heq : (3+I.format.unitRoundoff+(1+I.format.unitRoundoff)^2/Real.sqrt 3)*
      (I.format.unitRoundoff*‖realVec E‖*D) =
      (3*I.format.unitRoundoff+I.format.unitRoundoff^2)*‖realVec E‖*D+
      (I.format.unitRoundoff*(1+I.format.unitRoundoff)+I.format.unitRoundoff^2*(1+I.format.unitRoundoff))*
        (‖realVec E‖*(D/Real.sqrt 3)) := by ring
  rw [heq] at hc
  have hpair : ‖realVec N-exactCross (realVec E) (realVec F)‖+
      ‖realVec K-exactCross (realVec E) (realVec R)‖ ≤ 3.60*I.format.unitRoundoff*‖realVec E‖*D := by
    nlinarith [mul_nonneg hρ (mul_nonneg (norm_nonneg (realVec E)) hD)]
  refine ⟨N,K,hN,hK,hpair,?_,?_⟩
  · have h := norm_sub_le (realVec N-exactCross (realVec E) (realVec F)) (-(exactCross (realVec E) (realVec F)))
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at h
    nlinarith [norm_nonneg (realVec K-exactCross (realVec E) (realVec R)),
      mul_nonneg hρ (mul_nonneg (norm_nonneg (realVec E)) hD)]
  · have h := norm_sub_le (realVec K-exactCross (realVec E) (realVec R)) (-(exactCross (realVec E) (realVec R)))
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at h
    nlinarith [norm_nonneg (realVec N-exactCross (realVec E) (realVec F)),
      mul_nonneg hρ (mul_nonneg (norm_nonneg (realVec E)) hD)]

end DistanceAccuracy.Determinant

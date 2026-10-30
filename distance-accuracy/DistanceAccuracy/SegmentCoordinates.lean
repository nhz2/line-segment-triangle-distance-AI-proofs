import DistanceAccuracy.FaceCoordinates

/-! Common geometry of the independently rounded segment differences. -/
namespace DistanceAccuracy.SegmentCoordinates
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant
open FaceCoordinates

lemma residual_norm (I : Interchange) {P₀ P₁ Q₀ Q₁ P Q R : E3} {L s t : ℝ}
    (hL : 0 ≤ L) (hP0 : ∀ k, |P₀ k| ≤ L) (hP1 : ∀ k, |P₁ k| ≤ L)
    (hQ0 : ∀ k, |Q₀ k| ≤ L) (hQ1 : ∀ k, |Q₁ k| ≤ L)
    (hP : ∀ k, Reconstruction.RoundError I.format.unitRoundoff I.format.minSubnormal (P₁ k-P₀ k) (P k))
    (hQ : ∀ k, Reconstruction.RoundError I.format.unitRoundoff I.format.minSubnormal (Q₁ k-Q₀ k) (Q k))
    (hR : ∀ k, Reconstruction.RoundError I.format.unitRoundoff I.format.minSubnormal (Q₀ k-P₀ k) (R k))
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L) :
    ‖R+t•Q-s•P‖ ≤ (7/2)*L := by
  have hρ := I.format.unitRoundoff_pos.le
  have hη : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  let e := 2*I.format.unitRoundoff*L+I.format.minSubnormal/2
  have he : 0 ≤ e := by dsimp [e]; positivity
  have heP : ∀ k, |P k-(P₁ k-P₀ k)| ≤ e := by
    intro k
    have hh := hP k
    have hd := Reconstruction.difference_abs (hP1 k) (hP0 k)
    have hm := mul_le_mul_of_nonneg_left hd hρ
    unfold Reconstruction.RoundError at hh
    dsimp [e]; nlinarith
  have heQ : ∀ k, |Q k-(Q₁ k-Q₀ k)| ≤ e := by
    intro k
    have hh := hQ k
    have hd := Reconstruction.difference_abs (hQ1 k) (hQ0 k)
    have hm := mul_le_mul_of_nonneg_left hd hρ
    unfold Reconstruction.RoundError at hh
    dsimp [e]; nlinarith
  have heR : ∀ k, |R k-(Q₀ k-P₀ k)| ≤ e := by
    intro k
    have hh := hR k
    have hd := Reconstruction.difference_abs (hQ0 k) (hP0 k)
    have hm := mul_le_mul_of_nonneg_left hd hρ
    unfold Reconstruction.RoundError at hh
    dsimp [e]; nlinarith
  have hc : ∀ k, |(R+t•Q-s•P) k| ≤ 2*L+3*e := by
    intro k
    have hx := Reconstruction.interval_abs hL (hP0 k) (hP1 k) hs0 hs1
    have hy := Reconstruction.interval_abs hL (hQ0 k) (hQ1 k) ht0 ht1
    have hid := Reconstruction.difference_abs hy hx
    have hp := mul_le_mul (show |s| ≤ 1 by rwa [abs_of_nonneg hs0]) (heP k) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have hq := mul_le_mul (show |t| ≤ 1 by rwa [abs_of_nonneg ht0]) (heQ k) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have hsum := abs_add_le (R k-(Q₀ k-P₀ k)) (t*(Q k-(Q₁ k-Q₀ k)))
    have hsum' := abs_sub ((R k-(Q₀ k-P₀ k))+t*(Q k-(Q₁ k-Q₀ k))) (s*(P k-(P₁ k-P₀ k)))
    have htotal := abs_add_le (((R k-(Q₀ k-P₀ k))+t*(Q k-(Q₁ k-Q₀ k)))-s*(P k-(P₁ k-P₀ k)))
      (((1-t)*Q₀ k+t*Q₁ k)-((1-s)*P₀ k+s*P₁ k))
    have heq : (((R k-(Q₀ k-P₀ k))+t*(Q k-(Q₁ k-Q₀ k)))-s*(P k-(P₁ k-P₀ k)))+
      (((1-t)*Q₀ k+t*Q₁ k)-((1-s)*P₀ k+s*P₁ k)) = (R+t•Q-s•P) k := by simp; ring
    rw [heq] at htotal
    simp only [abs_mul] at hsum hsum'
    have hr := heR k
    linarith
  have hn := GeometryCoverage.coordinate_norm_bound (by positivity) hc
  have hsqrt : Real.sqrt 3 ≤ 26/15 := by apply Real.sqrt_le_iff.mpr; norm_num
  have hrs : I.format.unitRoundoff^2 ≤ (1/1024:ℝ)^2 := (sq_le_sq₀ hρ (by norm_num)).2 hrho
  have hb : 2+6*I.format.unitRoundoff+(3/2)*I.format.unitRoundoff^2 ≤ 201/100 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hb hL
  have hscalar : 2*L+3*e ≤ (201/100)*L := by dsimp [e]; nlinarith
  have hp := mul_le_mul hsqrt hscalar (by positivity) (by norm_num : (0:ℝ) ≤ 26/15)
  nlinarith

/-- Actual independent subtractions share one diameter for every segment
    residual, including endpoint and second-solve comparison points. -/
theorem segment_geometry (I : Interchange) [I.Valid] {x y : Segment I}
    {P₀ P₁ Q₀ Q₁ : Fin 3 → ℚ} {L : ℝ}
    (hp0 : ∀ k, value? I (x 0 k) = some (P₀ k)) (hp1 : ∀ k, value? I (x 1 k) = some (P₁ k))
    (hq0 : ∀ k, value? I (y 0 k) = some (Q₀ k)) (hq1 : ∀ k, value? I (y 1 k) = some (Q₁ k))
    (hL : 0 ≤ L) (hP0 : ∀ k, |(P₀ k : ℝ)| ≤ L) (hP1 : ∀ k, |(P₁ k : ℝ)| ≤ L)
    (hQ0 : ∀ k, |(Q₀ k : ℝ)| ≤ L) (hQ1 : ∀ k, |(Q₁ k : ℝ)| ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ∃ p q r : Fin 3 → ℚ,
      (∀ k, value? I (vsub I (x 1) (x 0) k) = some (p k)) ∧
      (∀ k, value? I (vsub I (y 1) (y 0) k) = some (q k)) ∧
      (∀ k, value? I (vsub I (y 0) (x 0) k) = some (r k)) ∧
      (∀ k, |(p k : ℝ)| ≤ ((7/2)*L)/Real.sqrt 3) ∧
      (∀ k, |(q k : ℝ)| ≤ ((7/2)*L)/Real.sqrt 3) ∧
      (∀ k, |(r k : ℝ)| ≤ ((7/2)*L)/Real.sqrt 3) ∧
      ‖realVec p‖ ≤ (7/2)*L ∧ ‖realVec q‖ ≤ (7/2)*L ∧ ‖realVec r‖ ≤ (7/2)*L ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
        ‖realVec r+t•realVec q-s•realVec p‖ ≤ (7/2)*L := by
  obtain ⟨p, hp, hpC, hpN, hpErr⟩ := difference_data I hp0 hp1 hL hP0 hP1 hrho heta hlim
  obtain ⟨q, hq, hqC, hqN, hqErr⟩ := difference_data I hq0 hq1 hL hQ0 hQ1 hrho heta hlim
  obtain ⟨r, hr, hrC, hrN, hrErr⟩ := difference_data I hp0 hq0 hL hP0 hQ0 hrho heta hlim
  have hdiam := (diameter_bound I hL hrho heta).2
  have hdiv := div_le_div_of_nonneg_right hdiam (Real.sqrt_nonneg 3)
  refine ⟨p, q, r, hp, hq, hr, fun k => (hpC k).trans hdiv,
    fun k => (hqC k).trans hdiv, fun k => (hrC k).trans hdiv,
    hpN.trans hdiam, hqN.trans hdiam, hrN.trans hdiam, ?_⟩
  intro s t hs0 hs1 ht0 ht1
  exact residual_norm I (P₀ := realVec P₀) (P₁ := realVec P₁) (Q₀ := realVec Q₀) (Q₁ := realVec Q₁)
    hL hP0 hP1 hQ0 hQ1 hpErr hqErr hrErr hs0 hs1 ht0 ht1 hrho heta

end DistanceAccuracy.SegmentCoordinates

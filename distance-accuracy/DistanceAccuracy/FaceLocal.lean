import DistanceAccuracy.FaceLossCore
import DistanceAccuracy.WordFaceFinite

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant DotWordBounds

noncomputable def scalarDot (a b : Fin 3 → ℚ) : ℝ :=
  (a 0 : ℝ) * (b 0 : ℝ) + (a 1 : ℝ) * (b 1 : ℝ) + (a 2 : ℝ) * (b 2 : ℝ)

lemma scalarDot_inner (a b : Fin 3 → ℚ) : scalarDot a b = inner ℝ (realVec a) (realVec b) := by
  simp [scalarDot, realVec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  ring

lemma scalarDot_self (a : Fin 3 → ℚ) : scalarDot a a = ‖realVec a‖ ^ 2 := by
  rw [scalarDot_inner, real_inner_self_eq_norm_sq]

def faceRaw (I : Interchange) [I.Valid] (E F R : Vec3 I) (v : I.Word) : I.Word :=
  let ia := IEEEAlgorithm.div I (one I) (dot3 I E E)
  fma I (neg I v) (mul I (dot3 I E F) ia) (mul I (neg I (dot3 I E R)) ia)

/-- A local face bound for actual IEEE words. The only non-geometric premises
are explicit format/range bounds; no numerical accuracy certificate is assumed.
The reciprocal and normalized-coefficient range conditions are discharged by
FaceRanges for admissible input scales. -/
theorem word_face_local (I : Interchange) [I.Valid]
    {E F R : Vec3 I} {e f r : Fin 3 → ℚ} {vw : I.Word} {v : ℚ} {D P T : ℝ}
    (hone : value? I (one I) = some 1)
    (hE : ∀ i, value? I (E i) = some (e i))
    (hF : ∀ i, value? I (F i) = some (f i))
    (hR : ∀ i, value? I (R i) = some (r i))
    (hv : value? I vw = some v) (hv0 : (0 : ℝ) ≤ (v : ℝ)) (hv1 : (v : ℝ) ≤ 1)
    (hne : realVec e ≠ 0) (hD : 0 < D)
    (heD : ‖realVec e‖ ≤ D) (hfD : ‖realVec f‖ ≤ D) (hrD : ‖realVec r‖ ≤ D)
    (heC : ∀ i, |(e i : ℝ)| ≤ D / Real.sqrt 3)
    (hfC : ∀ i, |(f i : ℝ)| ≤ D / Real.sqrt 3)
    (hrC : ∀ i, |(r i : ℝ)| ≤ D / Real.sqrt 3)
    (hP : 0 < P) (hpE : ∀ i, |(e i : ℝ) * (e i : ℝ)| ≤ P)
    (hpF : ∀ i, |(e i : ℝ) * (f i : ℝ)| ≤ P)
    (hpR : ∀ i, |(e i : ℝ) * (r i : ℝ)| ≤ P)
    (hetaP : I.format.minSubnormal ≤ P)
    (hrho : I.format.unitRoundoff ≤ 1 / 16777216)
    (hPmax : 6 * P < I.format.overflowThreshold)
    (hetaA : I.format.minSubnormal ≤ ‖realVec e‖ ^ 2 / 8)
    (hT : 0 < T) (hetaT : I.format.minSubnormal ≤ T) (hTmax : 8 * T < I.format.overflowThreshold)
    (hranges : ∀ a b d : ℚ, value? I (dot3 I E E) = some a →
      value? I (dot3 I E F) = some b → value? I (dot3 I E R) = some d →
      I.format.minNormal ≤ 1 / (a : ℝ) ∧ 1 / (a : ℝ) < I.format.overflowThreshold ∧
      |(b : ℝ)| ≤ (a : ℝ) * T ∧ |(d : ℝ)| ≤ (a : ℝ) * T) :
    ∃ q : ℚ, value? I (faceRaw I E F R vw) = some q ∧
      ∀ ustar : ℝ, 0 ≤ ustar → ustar + (v : ℝ) ≤ 1 →
      let u := max 0 (min (1 - (v : ℝ)) (q : ℝ))
      ‖(realVec r + (v : ℝ) • realVec f) + u • realVec e‖ ^ 2 ≤
        ‖(realVec r + (v : ℝ) • realVec f) + ustar • realVec e‖ ^ 2 +
        ((361 / 50) * I.format.unitRoundoff * D) ^ 2 +
        64 * I.format.minSubnormal * (1 + ‖realVec e‖ ^ 2) := by
  have hrho0 := I.format.unitRoundoff_pos.le
  have heta0 : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  obtain ⟨a, ha, haW⟩ := dot3_finite_weighted I hE hE hP hpE hetaP (by linarith only [hrho]) hPmax
  obtain ⟨b, hb, hbW⟩ := dot3_finite_weighted I hE hF hP hpF hetaP (by linarith only [hrho]) hPmax
  obtain ⟨d, hd, hdW⟩ := dot3_finite_weighted I hE hR hP hpR hetaP (by linarith only [hrho]) hPmax
  have haGeom := weighted_self_scaled hD (a := realVec e) heC
  have hbGeom := weighted_general_scaled hD.le (a := realVec e) (b := realVec f) hfC
  have hdGeom := weighted_general_scaled hD.le (a := realVec e) (b := realVec r) hrC
  have haSharp : |(a : ℝ) - ‖realVec e‖ ^ 2| ≤
      (2042 / 1000) * I.format.unitRoundoff * (‖realVec e‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal := by
    have hm := mul_le_mul_of_nonneg_left haGeom (show 0 ≤ I.format.unitRoundoff * (1 + I.format.unitRoundoff) ^ 2 by positivity)
    change |(a : ℝ) - scalarDot e e| ≤ _ at haW
    rw [scalarDot_self] at haW
    simp only [realVec, WithLp.ofLp_toLp, ← sq, abs_sq] at hm haW ⊢
    nlinarith only [hm, haW]
  have hbSharp : |(b : ℝ) - inner ℝ (realVec e) (realVec f)| ≤
      (2161 / 1000) * I.format.unitRoundoff * (‖realVec e‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal := by
    have hm := mul_le_mul_of_nonneg_left hbGeom (show 0 ≤ I.format.unitRoundoff * (1 + I.format.unitRoundoff) ^ 2 by positivity)
    change |(b : ℝ) - scalarDot e f| ≤ _ at hbW
    rw [scalarDot_inner] at hbW
    dsimp [realVec] at hm hbW ⊢
    nlinarith only [hm, hbW]
  have hdSharp : |(d : ℝ) - inner ℝ (realVec e) (realVec r)| ≤
      (2161 / 1000) * I.format.unitRoundoff * (‖realVec e‖ * D) * (1 + I.format.unitRoundoff) ^ 2 + 2 * I.format.minSubnormal := by
    have hm := mul_le_mul_of_nonneg_left hdGeom (show 0 ≤ I.format.unitRoundoff * (1 + I.format.unitRoundoff) ^ 2 by positivity)
    change |(d : ℝ) - scalarDot e r| ≤ _ at hdW
    rw [scalarDot_inner] at hdW
    dsimp [realVec] at hm hdW ⊢
    nlinarith only [hm, hdW]
  obtain ⟨a', ha', haN⟩ := dot3_finite_error I hE hE hP hpE hetaP (by linarith only [hrho]) hPmax
  have haa' : a' = a := Option.some.inj (ha'.symm.trans ha)
  subst a'
  change |(a : ℝ) - scalarDot e e| ≤ _ at haN
  rw [scalarDot_self] at haN
  have hrsmall : 3 * I.format.unitRoundoff * (1 + I.format.unitRoundoff) ^ 2 ≤ (1 / 4 : ℝ) := by
    have hU : (1 + I.format.unitRoundoff) ^ 2 ≤ 2 := by
      nlinarith only [hrho, hrho0, mul_nonneg hrho0 (sub_nonneg.mpr hrho)]
    nlinarith only [hrho, mul_le_mul_of_nonneg_left hU hrho0]
  have hm := mul_le_mul_of_nonneg_right hrsmall (sq_nonneg ‖realVec e‖)
  have haHalf : |(a : ℝ) - ‖realVec e‖ ^ 2| ≤ ‖realVec e‖ ^ 2 / 2 := by
    nlinarith only [haN, hm, hetaA]
  have hnormpos : 0 < ‖realVec e‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hap : 0 < a := by
    have hab := (abs_le.mp haHalf).1
    have : (0 : ℝ) < (a : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨hnormal, hrecip, hbT, hdT⟩ := hranges a b d ha hb hd
  obtain ⟨c, m, q, hc, hmword, hq⟩ := word_face_finite I hone ha hb hd hv hap
    (by rw [abs_of_nonneg hv0]; exact hv1) hT hbT hdT (by linarith) hetaT hnormal hrecip hTmax
  refine ⟨q, hq, ?_⟩
  intro ustar hus0 hus1
  obtain ⟨di, dc, dm, dq, zc, zm, zq, hdi, hdc, hdm, hdq, hzc, hzm, hzq, hKKT⟩ :=
    word_face_effective I hone ha hb hd hv hap hv1 (by linarith) hnormal hrecip hc hmword hq hus0 (by linarith)
  let u := max 0 (min (1 - (v : ℝ)) (q : ℝ))
  have hu0 : 0 ≤ u := le_max_left _ _
  have hu1 : u ≤ 1 - (v : ℝ) := max_le (by linarith) (min_le_left _ _)
  apply face_squared_loss hne hD heD hfD hrD hrho0 hrho heta0
    (by exact_mod_cast hap.le) (haHalf.trans (by linarith)) haSharp hbSharp hdSharp
    hdi hdc hdm hdq hzm hzc hzq hu0 hv0 (by linarith) hus0 hus1 hKKT

end DistanceAccuracy.ProjectionRounding

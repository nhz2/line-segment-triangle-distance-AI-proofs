import DistanceAccuracy.FaceLocal
import DistanceAccuracy.FaceRanges

/-! Concrete face-local optimality with all reciprocal and product range
    obligations discharged from admissible input magnitude. -/
namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant DotWordBounds FaceRanges
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048

theorem word_face_admissible (fmt : Format)
    {E F R : Vec3 fmt.interchange} {e f r : Fin 3 → ℚ}
    {vw : fmt.interchange.Word} {v : ℚ} {D L : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hE : ∀ i, value? fmt.interchange (E i) = some (e i))
    (hF : ∀ i, value? fmt.interchange (F i) = some (f i))
    (hR : ∀ i, value? fmt.interchange (R i) = some (r i))
    (hv : value? fmt.interchange vw = some v) (hv0 : (0 : ℝ) ≤ (v : ℝ)) (hv1 : (v : ℝ) ≤ 1)
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hA : fourthRoot fmt.leastSubnormal < ‖realVec e‖) (hDL : D ≤ 9*L)
    (heD : ‖realVec e‖ ≤ D) (hfD : ‖realVec f‖ ≤ D) (hrD : ‖realVec r‖ ≤ D)
    (heC : ∀ i, |(e i : ℝ)| ≤ D/Real.sqrt 3)
    (hfC : ∀ i, |(f i : ℝ)| ≤ D/Real.sqrt 3)
    (hrC : ∀ i, |(r i : ℝ)| ≤ D/Real.sqrt 3) :
    ∃ q : ℚ, value? fmt.interchange (faceRaw fmt.interchange E F R vw) = some q ∧
      ∀ ustar : ℝ, 0 ≤ ustar → ustar+(v : ℝ) ≤ 1 →
      let u := max 0 (min (1-(v : ℝ)) (q : ℝ))
      ‖(realVec r+(v : ℝ) • realVec f)+u • realVec e‖^2 ≤
        ‖(realVec r+(v : ℝ) • realVec f)+ustar • realVec e‖^2+
        ((361/50)*fmt.interchange.format.unitRoundoff*D)^2+
        64*fmt.interchange.format.minSubnormal*(1+‖realVec e‖^2) := by
  let A := ‖realVec e‖
  let P := D^2+1
  let T := 16*(D+1)/fourthRoot fmt.leastSubnormal
  have hρ : fmt.interchange.format.unitRoundoff = fmt.rho := by
    cases fmt
    · exact fp32_parameters.1
    · exact fp64_parameters.1
  have hη : fmt.interchange.format.minSubnormal = fmt.leastSubnormal := by
    cases fmt
    · exact fp32_parameters.2.2
    · exact fp64_parameters.2.2
  have hη0 := fmt.subnormal_nonneg
  have hρ0 := fmt.rho_nonneg
  have hρmax : fmt.interchange.format.unitRoundoff ≤ 1/16777216 := by
    rw [hρ]; have hh := fmt.rho_le; norm_num at hh; exact hh
  have hrmax : fmt.interchange.format.unitRoundoff ≤ 1/16 := by linarith
  have hA0 : 0 < A := lt_of_le_of_lt (fourthRoot_nonneg _) hA
  have hD0 : 0 < D := hA0.trans_le heD
  have hne : realVec e ≠ 0 := by intro hz; simp [A, hz] at hA0
  have hP : 0 < P := by dsimp [P]; positivity
  have hηP : fmt.interchange.format.minSubnormal ≤ P := by
    have hh : fmt.leastSubnormal ≤ 1 := by
      cases fmt <;> norm_num [Format.leastSubnormal]
    rw [hη]; dsimp [P]; nlinarith [sq_nonneg D]
  have hPmax : 6*P < fmt.interchange.format.overflowThreshold := by
    have hh := fmt.quadratic_range hL hadm
    have hs : D^2 ≤ (9*L)^2 := (sq_le_sq₀ hD0.le (by positivity)).2 hDL
    dsimp [P]; nlinarith [sq_nonneg L]
  have hsqrt : 1 ≤ Real.sqrt (3:ℝ) := by apply (Real.le_sqrt (by norm_num) (by norm_num)).2; norm_num
  have hdiv : D/Real.sqrt 3 ≤ D := div_le_self hD0.le hsqrt
  have product_bound (a b : Fin 3 → ℚ)
      (ha : ∀ i, |(a i : ℝ)| ≤ D/Real.sqrt 3)
      (hb : ∀ i, |(b i : ℝ)| ≤ D/Real.sqrt 3) :
      ∀ i, |(a i : ℝ)*(b i : ℝ)| ≤ P := by
    intro i
    rw [abs_mul]
    have hh := mul_le_mul ((ha i).trans hdiv) ((hb i).trans hdiv) (abs_nonneg _) hD0.le
    dsimp [P]; nlinarith
  have hpE := product_bound e e heC heC
  have hpF := product_bound e f heC hfC
  have hpR := product_bound e r heC hrC
  have dummy := FaceRanges.face_ranges fmt hL hadm hA heD hDL
    (a := A^2) (b := 0) (d := 0) (be := 0) (de := 0)
    (by simp only [A, sub_self, abs_zero]; positivity) (by simp only [A, sub_self, abs_zero]; positivity) (by simp only [A, sub_self, abs_zero]; positivity)
    (by simp only [A, sub_self, abs_zero]; positivity) (by simp only [A, sub_self, abs_zero]; positivity)
  obtain ⟨hηA, _, _, _, _, hT, _, _, hηT, hTmax⟩ := dummy
  apply word_face_local fmt.interchange hone hE hF hR hv hv0 hv1 hne hD0 heD hfD hrD
    heC hfC hrC hP hpE hpF hpR hηP hρmax hPmax
    (by simpa [hη, A] using hηA) hT (by simpa [hη] using hηT) hTmax
  intro a b d ha hb hd
  obtain ⟨a', ha', haErr⟩ := dot3_finite_error fmt.interchange hE hE hP hpE hηP hrmax hPmax
  obtain ⟨b', hb', hbErr⟩ := dot3_finite_error fmt.interchange hE hF hP hpF hηP hrmax hPmax
  obtain ⟨d', hd', hdErr⟩ := dot3_finite_error fmt.interchange hE hR hP hpR hηP hrmax hPmax
  have haa : a' = a := Option.some.inj (ha'.symm.trans ha)
  have hbb : b' = b := Option.some.inj (hb'.symm.trans hb)
  have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst a'; subst b'; subst d'
  change |(a : ℝ)-scalarDot e e| ≤ _ at haErr
  change |(b : ℝ)-scalarDot e f| ≤ _ at hbErr
  change |(d : ℝ)-scalarDot e r| ≤ _ at hdErr
  rw [scalarDot_self, hρ, hη] at haErr
  rw [scalarDot_inner, hρ, hη] at hbErr hdErr
  have haErr' : |(a : ℝ)-A^2| ≤ 3*fmt.rho*(1+fmt.rho)^2*A^2+2*fmt.leastSubnormal := by
    simpa [A, pow_two, mul_assoc] using haErr
  have hcoef : 0 ≤ 3*fmt.rho*(1+fmt.rho)^2*A := by positivity
  have hbErr' : |(b : ℝ)-inner ℝ (realVec e) (realVec f)| ≤
      3*fmt.rho*(1+fmt.rho)^2*A*D+2*fmt.leastSubnormal := by
    have hm := mul_le_mul_of_nonneg_left hfD hcoef
    dsimp [A] at hm; linarith
  have hdErr' : |(d : ℝ)-inner ℝ (realVec e) (realVec r)| ≤
      3*fmt.rho*(1+fmt.rho)^2*A*D+2*fmt.leastSubnormal := by
    have hm := mul_le_mul_of_nonneg_left hrD hcoef
    dsimp [A] at hm; linarith
  have hbe : |inner ℝ (realVec e) (realVec f)| ≤ A*D :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hfD hA0.le)
  have hde : |inner ℝ (realVec e) (realVec r)| ≤ A*D :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hrD hA0.le)
  obtain ⟨_, _, _, hn, hi, _, hbT, hdT, _, _⟩ := FaceRanges.face_ranges fmt hL hadm hA heD hDL
    haErr' hbErr' hdErr' hbe hde
  exact ⟨hn, hi, hbT, hdT⟩

end DistanceAccuracy.ProjectionRounding

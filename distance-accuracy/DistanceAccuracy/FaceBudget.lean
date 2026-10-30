import DistanceAccuracy.FaceCoverage
import DistanceAccuracy.UnderflowAbsorption

namespace DistanceAccuracy.FaceCoverage
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge
open GeometryCoverage Determinant

lemma hypot_comm (a b : ℝ) : hypot a b = hypot b a := by
  simp only [hypot, add_comm]

lemma secondBudget_le {rho eta D A : ℝ} (hr : 0≤rho) (he : 0≤eta)
    (hD : 0≤D) (hA : 0≤A) :
    secondBudget rho eta D A ≤ (361/50)*rho*D+8*Real.sqrt eta*(1+A) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hs := Real.sq_sqrt he
    have hp := mul_nonneg (show 0≤(361/50:ℝ)*rho*D by positivity)
      (show 0≤8*Real.sqrt eta*(1+A) by positivity)
    nlinarith [mul_nonneg he hA]

lemma face_absolute_budget (fmt : Format) {D : ℝ} (hD : 0≤D) :
    8*Real.sqrt fmt.leastSubnormal*(1+D)+
      4*fmt.leastSubnormal*(1+D)+Real.sqrt (2*fmt.leastSubnormal) ≤
    fourthRoot fmt.leastSubnormal+(1/1000)*fmt.rho*D := by
  let h := fourthRoot fmt.leastSubnormal
  have hh0 : 0≤h := fourthRoot_nonneg _
  have hh1 : h≤1/100 := fmt.subnormal_root_small
  have hh2 : h^2=Real.sqrt fmt.leastSubnormal := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hh4 : h^4=fmt.leastSubnormal := fourthRoot_pow_four fmt.subnormal_nonneg
  have heta : fmt.leastSubnormal≤Real.sqrt fmt.leastSubnormal := by
    have hp := mul_nonneg (sq_nonneg h) (show 0≤1-h^2 by nlinarith)
    nlinarith
  have hconst : 12*Real.sqrt fmt.leastSubnormal+4*fmt.leastSubnormal≤h := by
    have hp := mul_nonneg hh0 (show 0≤1-16*h by linarith)
    nlinarith
  have hroot : Real.sqrt (2*fmt.leastSubnormal)≤2*Real.sqrt fmt.leastSubnormal := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt fmt.subnormal_nonneg]
  have hs := mul_le_mul_of_nonneg_right fmt.sqrt_eta_absorption hD
  have heD := mul_le_mul_of_nonneg_right heta hD
  have hz := mul_nonneg (Real.sqrt_nonneg fmt.leastSubnormal) hD
  change _≤h+_
  nlinarith [fmt.subnormal_nonneg]

/-- A clean envelope retaining both actual-score and edge-witness uses.
The whole second solve and norm evaluation consume only one additional h. -/
lemma clean_face_budget (fmt : Format) {D A z c : ℝ}
    (hD : 0≤D) (hA : 0≤A) (hAD : A≤D) (hc : 0≤c) :
    hypot (fmt.rho*D*J c z+4*fourthRoot fmt.leastSubnormal+
        (3/1000000)*fmt.rho*D)
      (secondBudget fmt.rho fmt.leastSubnormal D A)+
      evaluationBudget fmt.rho fmt.leastSubnormal D ≤
    fmt.rho*D*(hypot (J c z) (361/50)+4.532)+5*fourthRoot fmt.leastSubnormal := by
  have hr : 0≤fmt.rho := by cases fmt <;> norm_num [Format.rho]
  have hj : 0≤fmt.rho*D*J c z := mul_nonneg (mul_nonneg hr hD) (J_nonneg hc)
  have ht : 0≤4*fourthRoot fmt.leastSubnormal+(3/1000000)*fmt.rho*D := by
    exact add_nonneg (mul_nonneg (by norm_num) (fourthRoot_nonneg _)) (by positivity)
  have hs := secondBudget_le hr fmt.subnormal_nonneg hD hA
  have hb := hypot_mono (b := fmt.rho*D*J c z+(4*fourthRoot fmt.leastSubnormal+(3/1000000)*fmt.rho*D)) (show 0 ≤ secondBudget fmt.rho fmt.leastSubnormal D A by apply Real.sqrt_nonneg) hs
  rw [hypot_comm] at hb
  have ha := hypot_add_le (b := (361/50)*fmt.rho*D+8*Real.sqrt fmt.leastSubnormal*(1+A)) hj ht
  have hc2 := hypot_add_le (a := (361/50)*fmt.rho*D)
    (b := fmt.rho*D*J c z) (by positivity)
    (show 0≤8*Real.sqrt fmt.leastSubnormal*(1+A) by positivity)
  rw [hypot_comm] at hc2
  have habs := face_absolute_budget fmt hD
  have hmono := mul_le_mul_of_nonneg_left hAD (show 0≤8*Real.sqrt fmt.leastSubnormal by positivity)
  have hscale : hypot (fmt.rho*D*J c z) ((361/50)*fmt.rho*D) =
      fmt.rho*D*hypot (J c z) (361/50) := by
    rw [show (361/50)*fmt.rho*D = (fmt.rho*D)*(361/50) by ring]
    exact hypot_scale (mul_nonneg hr hD)
  rw [hypot_comm ((361/50)*fmt.rho*D) (fmt.rho*D*J c z), hscale] at hc2
  dsimp [evaluationBudget]
  have hb' := hb
  rw [hypot_comm ((361/50)*fmt.rho*D+8*Real.sqrt fmt.leastSubnormal*(1+A))] at hb'
  have hident : fmt.rho*D*J c z+4*fourthRoot fmt.leastSubnormal+(3/1000000)*fmt.rho*D =
      fmt.rho*D*J c z+(4*fourthRoot fmt.leastSubnormal+(3/1000000)*fmt.rho*D) := by ring
  rw [hident]
  nlinarith [mul_nonneg hr hD]

lemma clean_edge_budget (fmt : Format) {D A z c : ℝ}
    (hD : 0≤D) (hA : 0≤A) (hAD : A≤D) (hc : 0≤c) :
    hypot (fmt.rho*D*J c z+4*fourthRoot fmt.leastSubnormal+
        (3/1000000)*fmt.rho*D)
      (secondBudget fmt.rho fmt.leastSubnormal D A) ≤
    fmt.rho*D*(hypot (J c z) (361/50)+0.002)+5*fourthRoot fmt.leastSubnormal := by
  have h := clean_face_budget (z := z) fmt hD hA hAD hc
  have he : (453/100)*fmt.rho*D ≤ evaluationBudget fmt.rho fmt.leastSubnormal D := by
    dsimp [evaluationBudget]
    have hp := mul_nonneg fmt.subnormal_nonneg (show 0≤1+D by linarith)
    linarith [Real.sqrt_nonneg (2*fmt.leastSubnormal)]
  nlinarith only [h,he]

theorem face_admissible_clean (fmt : Format) (accurate : Bool)
    {E F R : Vec3 fmt.interchange} {e f r : Fin 3 → ℚ} {u₀ v₀ d L : ℝ}
    (hE : ∀ i, value? fmt.interchange (E i) = some (e i))
    (hF : ∀ i, value? fmt.interchange (F i) = some (f i))
    (hR : ∀ i, value? fmt.interchange (R i) = some (r i))
    (hL : 0≤L) (hadm : L<fourthRoot fmt.interchange.format.maxFinite/4)
    (hlarge : fourthRoot fmt.leastNormal/64≤L)
    (hA : fourthRoot fmt.leastSubnormal < ‖realVec e‖)
    (heD : ‖realVec e‖≤(7/2)*L) (hfD : ‖realVec f‖≤(7/2)*L) (hrD : ‖realVec r‖≤(7/2)*L)
    (hRE : ‖realVec r+realVec e‖≤(7/2)*L) (hRF : ‖realVec r+realVec f‖≤(7/2)*L)
    (heC : ∀ i, |(e i:ℝ)|≤((7/2)*L)/Real.sqrt 3)
    (hfC : ∀ i, |(f i:ℝ)|≤((7/2)*L)/Real.sqrt 3)
    (hrC : ∀ i, |(r i:ℝ)|≤((7/2)*L)/Real.sqrt 3)
    (hd : 0≤d) (hu₀ : 0≤u₀) (hv₀ : 0≤v₀) (huv₀ : u₀+v₀≤1)
    (hwitness : ‖residual (realVec r) (realVec e) (realVec f) u₀ v₀‖≤d) :
    let N := if accurate then cross3Accurate fmt.interchange E F else cross3 fmt.interchange E F
    let D := (7/2:ℝ)*L
    let W := hypot (J (PointProjection.crossCoefficient accurate) (d/(fmt.rho*D))) (361/50)
    UpperSelection.Upper fmt.interchange (fmt.rho*D*(W+4.532)+5*fourthRoot fmt.leastSubnormal)
      (face fmt.interchange R E F N).q ∨
    ∃ u' v' : ℝ, 0≤u' ∧ 0≤v' ∧ u'+v'≤1 ∧ (u'=0 ∨ u'+v'=1) ∧
      ‖residual (realVec r) (realVec e) (realVec f) u' v'‖≤
        fmt.rho*D*(W+0.002)+5*fourthRoot fmt.leastSubnormal := by
  have h := face_admissible_coverage fmt accurate hE hF hR hL hadm hlarge hA heD hfD hrD
    hRE hRF heC hfC hrC hd hu₀ hv₀ huv₀ hwitness
  have hc : 0≤PointProjection.crossCoefficient accurate := by
    cases accurate <;> norm_num [PointProjection.crossCoefficient]
  have hb := clean_face_budget (z := d/(fmt.rho*((7/2)*L))) fmt
    (show 0≤(7/2:ℝ)*L by positivity) (norm_nonneg (realVec e)) heD hc
  have he := clean_edge_budget (z := d/(fmt.rho*((7/2)*L))) fmt
    (show 0≤(7/2:ℝ)*L by positivity) (norm_nonneg (realVec e)) heD hc
  rcases h with ⟨q,hq,hbound⟩ | ⟨u,v,hu,hv,huv,hbd,hbound⟩
  · exact Or.inl ⟨q,hq,hbound.trans hb⟩
  · exact Or.inr ⟨u,v,hu,hv,huv,hbd,hbound.trans he⟩

/-- The h remainder in plane height is transported with multiplier one
through the face envelope, independent of the ratio h/(rho D). -/
lemma scaled_V_plane {k h d : ℝ} (hk : 0<k) (hh : 0≤h) (hd : 0≤d)
    (hplane : d≤(42/5)*k+h) : k*V (d/k)≤k*V (42/5)+h := by
  have heq : ((42/5)*k+h)/k=(42/5)+h/k := by field_simp <;> ring
  have hm := V_mono (div_nonneg hd hk.le) ((div_le_div_iff_of_pos_right hk).mpr hplane)
  rw [heq] at hm
  have ha := V_add_le (z := (42/5:ℝ)) (by norm_num) (div_nonneg hh hk.le)
  have hh' := mul_le_mul_of_nonneg_left (hm.trans ha) hk.le
  have he : k*(h/k)=h := by field_simp
  nlinarith only [hh',he]

lemma scaled_V_ge {k d : ℝ} (hk : 0<k) : d≤k*V (d/k) := by
  have hJ := le_hypot (d/k+(3.60:ℝ)) (7.02:ℝ)
  have hV := le_hypot (J 3.60 (d/k)) (7.22:ℝ)
  have hh : d/k≤V (d/k) := by dsimp [J,V] at *; linarith only [hJ,hV]
  have hm := mul_le_mul_of_nonneg_left hh hk.le
  have he : k*(d/k)=d := by field_simp
  nlinarith only [hm,he]

lemma crossing_edge_max {k h d : ℝ} (hk : 0<k) (hh : 0≤h) :
    max d (k*(V (d/k)+0.002)+5*h) = k*(V (d/k)+0.002)+5*h := by
  apply max_eq_right
  have hv := scaled_V_ge (d := d) hk
  nlinarith only [hv,hh,hk]

end DistanceAccuracy.FaceCoverage

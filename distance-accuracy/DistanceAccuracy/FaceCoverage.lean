import DistanceAccuracy.FaceLocalAdmissible
import DistanceAccuracy.FaceStoredNorm
import DistanceAccuracy.KernelCoverage
import DistanceAccuracy.CrossReducedAdmissible
import DistanceAccuracy.UpperSelection

namespace DistanceAccuracy.FaceCoverage
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge
open DistanceAccuracy.GeometryCoverage DistanceAccuracy.LineReduction
open DistanceAccuracy.ProjectionRounding DistanceAccuracy.Determinant
set_option exponentiation.threshold 2048

noncomputable def secondBudget (rho eta D A : ℝ) : ℝ :=
  Real.sqrt (((361/50:ℝ)*rho*D)^2+64*eta*(1+A^2))
noncomputable def evaluationBudget (rho eta D : ℝ) : ℝ :=
  (453/100:ℝ)*rho*D+4*eta*(1+D)+Real.sqrt (2*eta)

/-- Connect the actual reciprocal/FMA face solve and its actual stored squared
norm to exact AC/BC witness coverage. Only the reduced first solve remains an
input here; the next theorem supplies it from concrete cross-vector data. -/
theorem word_face_or_edge (fmt : Format)
    {E F R N : Vec3 fmt.interchange} {e f r : Fin 3 → ℚ}
    {v : ℚ} {u₀ v₀ B D L : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hE : ∀ i, value? fmt.interchange (E i) = some (e i))
    (hF : ∀ i, value? fmt.interchange (F i) = some (f i))
    (hR : ∀ i, value? fmt.interchange (R i) = some (r i))
    (hv : value? fmt.interchange (faceV fmt.interchange R E N) = some v)
    (hv0 : 0≤v) (hv1 : v≤1)
    (hL : 0≤L) (hadm : L<fourthRoot fmt.interchange.format.maxFinite/4)
    (hA : fourthRoot fmt.leastSubnormal < ‖realVec e‖) (hDL : D≤9*L)
    (heD : ‖realVec e‖≤D) (hfD : ‖realVec f‖≤D) (hrD : ‖realVec r‖≤D)
    (hRE : ‖realVec r+realVec e‖≤D) (hRF : ‖realVec r+realVec f‖≤D)
    (heC : ∀ i, |(e i:ℝ)|≤D/Real.sqrt 3)
    (hfC : ∀ i, |(f i:ℝ)|≤D/Real.sqrt 3)
    (hrC : ∀ i, |(r i:ℝ)|≤D/Real.sqrt 3)
    (hB : 0≤B) (hu₀ : 0≤u₀) (hv₀ : 0≤v₀) (huv₀ : u₀+v₀≤1)
    (hwitness : ‖residual (realVec r) (realVec e) (realVec f) u₀ v₀‖≤B)
    (hreduced : ‖residual (realVec r) (realVec e) (realVec f)
      (parameter (realVec e) (realVec r) (realVec f) (v:ℝ)) (v:ℝ)‖≤B) :
    let C := secondBudget fmt.interchange.format.unitRoundoff fmt.interchange.format.minSubnormal D ‖realVec e‖
    UpperSelection.Upper fmt.interchange (hypot B C+
      evaluationBudget fmt.interchange.format.unitRoundoff fmt.interchange.format.minSubnormal D)
      (face fmt.interchange R E F N).q ∨
    ∃ u' v' : ℝ, 0≤u' ∧ 0≤v' ∧ u'+v'≤1 ∧ (u'=0 ∨ u'+v'=1) ∧
      ‖residual (realVec r) (realVec e) (realVec f) u' v'‖≤hypot B C := by
  have hv0r : (0:ℝ)≤v := by exact_mod_cast hv0
  have hv1r : (v:ℝ)≤1 := by exact_mod_cast hv1
  have hD : 0≤D := (norm_nonneg (realVec e)).trans heD
  obtain ⟨raw,hraw,hproj⟩ := word_face_admissible fmt hone hE hF hR hv hv0r hv1r
    hL hadm hA hDL heD hfD hrD heC hfC hrC
  let C := secondBudget fmt.interchange.format.unitRoundoff fmt.interchange.format.minSubnormal D ‖realVec e‖
  have heta : 0≤fmt.interchange.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hC : C^2 = ((361/50:ℝ)*fmt.interchange.format.unitRoundoff*D)^2+
      64*fmt.interchange.format.minSubnormal*(1+‖realVec e‖^2) :=
    Real.sq_sqrt (by positivity)
  have reorder (u : ℝ) : residual (realVec r) (realVec e) (realVec f) u (v:ℝ) =
      (realVec r+(v:ℝ) • realVec f)+u • realVec e := by dsimp [GeometryCoverage.residual]; module
  have hvirtual : parameter (realVec e) (realVec r) (realVec f) (v:ℝ) ∈ Set.Icc 0 (1-(v:ℝ)) →
      ‖residual (realVec r) (realVec e) (realVec f) (max 0 (min (1-(v:ℝ)) (raw:ℝ))) (v:ℝ)‖^2 ≤
      ‖residual (realVec r) (realVec e) (realVec f)
        (parameter (realVec e) (realVec r) (realVec f) (v:ℝ)) (v:ℝ)‖^2+C^2 := by
    intro hin
    have hh := hproj (parameter (realVec e) (realVec r) (realVec f) (v:ℝ)) hin.1
      (by linarith only [hin.2])
    rw [hC]
    simpa only [reorder,add_assoc] using hh
  rcases KernelCoverage.face_or_edge hB hu₀ hv₀ huv₀ ⟨hv0r,hv1r⟩ hwitness hreduced hvirtual with hface | hedge
  · left
    have hrep : fmt.interchange.format.Representable 1 := by
      cases fmt <;> refine ⟨1,0,?_,?_,?_,?_⟩ <;>
        norm_num [Format.interchange,fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.precision]
    have hlim1 : (1:ℝ)<fmt.interchange.format.overflowThreshold := by
      cases fmt <;> norm_num [Format.interchange,fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.overflowThreshold]
    have hrmax : fmt.interchange.format.unitRoundoff≤1/16777216 := by
      cases fmt <;> norm_num [Format.interchange,fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.unitRoundoff]
    have heta1 : fmt.interchange.format.minSubnormal≤1 := by
      cases fmt <;> norm_num [Format.interchange,fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.minSubnormal]
    have hceil := fmt.admissible_coordinate_ceiling hadm
    have hDceil : D≤9*fmt.coordinateCeiling := by linarith only [hDL,hceil]
    have hlim : 4*(D+1)<fmt.interchange.format.overflowThreshold := by
      have hh : 4*(9*fmt.coordinateCeiling+1)<fmt.interchange.format.overflowThreshold := by
        cases fmt <;> norm_num [Format.interchange,Format.coordinateCeiling,fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.overflowThreshold]
      linarith only [hDceil,hh]
    have hqlim : 8*(4*(D+1))*(4*(D+1))+4<fmt.interchange.format.overflowThreshold := by
      have hh : 8*(4*(9*fmt.coordinateCeiling+1))^2+4<fmt.interchange.format.overflowThreshold := by
        cases fmt <;> norm_num [Format.interchange,Format.coordinateCeiling,fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.overflowThreshold]
      have hs := mul_self_le_mul_self (show 0≤4*(D+1) by positivity)
        (show 4*(D+1)≤4*(9*fmt.coordinateCeiling+1) by linarith only [hDceil])
      nlinarith only [hs,hh]
    obtain ⟨score,hscore,_,hscoreBound⟩ := face_candidate_score fmt.interchange hone hrep hlim1
      hE hF hR hv hv0 hv1 hraw hD hfD hrD hRE hRF hrmax heta1 hlim hqlim
    refine ⟨score,hscore,?_⟩
    have hid : min (v:ℝ) (1-max 0 (min 1 (raw:ℝ))) • realVec f+
        (max 0 (min 1 (raw:ℝ)) • realVec e+realVec r) =
        residual (realVec r) (realVec e) (realVec f) (max 0 (min 1 (raw:ℝ)))
          (min (v:ℝ) (1-max 0 (min 1 (raw:ℝ)))) := by dsimp [GeometryCoverage.residual]; module
    dsimp only at hscoreBound
    rw [hid] at hscoreBound
    dsimp [evaluationBudget]
    linarith only [hface,hscoreBound]
  · exact Or.inr hedge

noncomputable def reducedBudget (rho eta A D c d : ℝ) : ℝ :=
  rho*D*J c (d/(rho*D))+4*Real.sqrt eta/A+2*Real.sqrt eta*(1+4*rho)*D

lemma reducedBudget_ge {rho eta A D c d : ℝ} (hr : 0<rho) (he : 0≤eta)
    (hA : 0<A) (hD : 0<D) (hc : 0≤c) : d≤reducedBudget rho eta A D c d := by
  have hj : d/(rho*D)≤J c (d/(rho*D)) := by
    have hh := le_hypot (d/(rho*D)+c) (7.02:ℝ)
    dsimp [J]
    linarith only [hh,hc]
  have hm := mul_le_mul_of_nonneg_left hj (show 0≤rho*D by positivity)
  have hid : rho*D*(d/(rho*D))=d := by field_simp
  rw [hid] at hm
  dsimp [reducedBudget]
  have h1 : 0≤4*Real.sqrt eta/A := by positivity
  have h2 : 0≤2*Real.sqrt eta*(1+4*rho)*D := by positivity
  linarith only [hm,h1,h2]

/-- Both actual face solves, actual capping, and stored-norm evaluation are now
connected to the exact edge-witness alternative. Joint cross-product error and
range premises are supplied by CrossPair and admissible-coordinate arithmetic. -/
theorem face_from_cross_data (fmt : Format)
    {E F R N : Vec3 fmt.interchange} {e f r n k : Fin 3 → ℚ}
    {u₀ v₀ d D L c P : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hE : ∀ i, value? fmt.interchange (E i) = some (e i))
    (hF : ∀ i, value? fmt.interchange (F i) = some (f i))
    (hR : ∀ i, value? fmt.interchange (R i) = some (r i))
    (hN : ∀ i, value? fmt.interchange (N i) = some (n i))
    (hK : ∀ i, value? fmt.interchange (cross3 fmt.interchange E R i) = some (k i))
    (hL : 0≤L) (hadm : L<fourthRoot fmt.interchange.format.maxFinite/4)
    (hA : fourthRoot fmt.leastSubnormal < ‖realVec e‖) (hD : 0<D) (hDL : D≤9*L)
    (heD : ‖realVec e‖≤D) (hfD : ‖realVec f‖≤D) (hrD : ‖realVec r‖≤D)
    (hRE : ‖realVec r+realVec e‖≤D) (hRF : ‖realVec r+realVec f‖≤D)
    (heC : ∀ i, |(e i:ℝ)|≤D/Real.sqrt 3)
    (hfC : ∀ i, |(f i:ℝ)|≤D/Real.sqrt 3)
    (hrC : ∀ i, |(r i:ℝ)|≤D/Real.sqrt 3)
    (hd : 0≤d) (hc : 0≤c) (hu₀ : 0≤u₀) (hv₀ : 0≤v₀) (huv₀ : u₀+v₀≤1)
    (hwitness : ‖residual (realVec r) (realVec e) (realVec f) u₀ v₀‖≤d)
    (hnD : ‖realVec n‖≤(1+4*fmt.interchange.format.unitRoundoff)*(‖realVec e‖*D))
    (hkD : ‖realVec k‖≤(1+4*fmt.interchange.format.unitRoundoff)*(‖realVec e‖*D))
    (he : ‖realVec n-Determinant.exactCross (realVec e) (realVec f)‖+
      ‖realVec k-Determinant.exactCross (realVec e) (realVec r)‖≤c*fmt.interchange.format.unitRoundoff*‖realVec e‖*D)
    (hP : 0<P) (hbound : ((1+4*fmt.interchange.format.unitRoundoff)*(‖realVec e‖*D))^2≤P)
    (heta : fmt.interchange.format.minSubnormal≤fmt.interchange.format.unitRoundoff*P)
    (hlim : (11/10:ℝ)*P<fmt.interchange.format.overflowThreshold) :
    let B := reducedBudget fmt.interchange.format.unitRoundoff fmt.interchange.format.minSubnormal ‖realVec e‖ D c d
    let C := secondBudget fmt.interchange.format.unitRoundoff fmt.interchange.format.minSubnormal D ‖realVec e‖
    UpperSelection.Upper fmt.interchange (hypot B C+
      evaluationBudget fmt.interchange.format.unitRoundoff fmt.interchange.format.minSubnormal D)
      (face fmt.interchange R E F N).q ∨
    ∃ u' v' : ℝ, 0≤u' ∧ 0≤v' ∧ u'+v'≤1 ∧ (u'=0 ∨ u'+v'=1) ∧
      ‖residual (realVec r) (realVec e) (realVec f) u' v'‖≤hypot B C := by
  have hApos : 0<‖realVec e‖ := (fourthRoot_nonneg _).trans_lt hA
  have hene : realVec e ≠ 0 := norm_pos_iff.mp hApos
  have hrmax : fmt.interchange.format.unitRoundoff≤1/16777216 := by
    cases fmt <;> norm_num [Format.interchange,fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.unitRoundoff]
  have hlim1 : (1:ℝ)<fmt.interchange.format.overflowThreshold := by
    cases fmt <;> norm_num [Format.interchange,fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.overflowThreshold]
  obtain ⟨v,hv,hv0,hv1,hr⟩ := PointProjection.cross_reduced_from_data fmt.interchange hone hN hK
    hene hD hd hc hv₀ (by linarith only [hu₀,huv₀]) hrmax hlim1 hnD hkD he hwitness hP hbound heta hlim
  have heta0 : 0≤fmt.interchange.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hdB := reducedBudget_ge (d := d) fmt.interchange.format.unitRoundoff_pos heta0 hApos hD hc
  apply word_face_or_edge fmt hone hE hF hR hv hv0 hv1 hL hadm hA hDL heD hfD hrD hRE hRF heC hfC hrC
    (hd.trans hdB) hu₀ hv₀ huv₀ (hwitness.trans hdB) hr

/-- Face candidate-or-edge coverage from admissible local word geometry, with
all arithmetic range and first-projection obligations discharged. -/
theorem face_admissible_coverage (fmt : Format) (accurate : Bool)
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
    let B := fmt.rho*D*J (PointProjection.crossCoefficient accurate) (d/(fmt.rho*D))+
      4*fourthRoot fmt.leastSubnormal+(3/1000000)*fmt.rho*D
    let C := secondBudget fmt.rho fmt.leastSubnormal D ‖realVec e‖
    UpperSelection.Upper fmt.interchange (hypot B C+evaluationBudget fmt.rho fmt.leastSubnormal D)
      (face fmt.interchange R E F N).q ∨
    ∃ u' v' : ℝ, 0≤u' ∧ 0≤v' ∧ u'+v'≤1 ∧ (u'=0 ∨ u'+v'=1) ∧
      ‖residual (realVec r) (realVec e) (realVec f) u' v'‖≤hypot B C := by
  have hρ : fmt.interchange.format.unitRoundoff=fmt.rho := by
    cases fmt with
    | binary32 => exact fp32_parameters.1
    | binary64 => exact fp64_parameters.1
  have hη : fmt.interchange.format.minSubnormal=fmt.leastSubnormal := by
    cases fmt with
    | binary32 => exact fp32_parameters.2.2
    | binary64 => exact fp64_parameters.2.2
  have hone : value? fmt.interchange (one fmt.interchange)=some 1 := by
    cases fmt with
    | binary32 => exact OperationBounds.one_fp32
    | binary64 => exact OperationBounds.one_fp64
  obtain ⟨v,hv,hv0,hv1,hreduced⟩ := PointProjection.cross_reduced_admissible fmt accurate hE hF hR hL hadm
    hlarge hA heD hfD hrD heC hfC hrC hd hv₀ (by linarith only [hu₀,huv₀]) hwitness
  let D := (7/2:ℝ)*L
  let B := fmt.rho*D*J (PointProjection.crossCoefficient accurate) (d/(fmt.rho*D))+
      4*fourthRoot fmt.leastSubnormal+(3/1000000)*fmt.rho*D
  have hρpos : 0<fmt.rho := by rw [← hρ]; exact fmt.interchange.format.unitRoundoff_pos
  have hDpos : 0<D := ((fourthRoot_nonneg _).trans_lt hA).trans_le heD
  have hc : 0≤PointProjection.crossCoefficient accurate := by
    cases accurate <;> norm_num [PointProjection.crossCoefficient]
  have hge : d≤B := by
    have hj : d/(fmt.rho*D)≤J (PointProjection.crossCoefficient accurate) (d/(fmt.rho*D)) := by
      have hh := le_hypot (d/(fmt.rho*D)+PointProjection.crossCoefficient accurate) (7.02:ℝ)
      dsimp [J]
      linarith only [hh,hc]
    have hm := mul_le_mul_of_nonneg_left hj (show 0≤fmt.rho*D by positivity)
    have hid : fmt.rho*D*(d/(fmt.rho*D))=d := by field_simp
    rw [hid] at hm
    dsimp [B]
    nlinarith only [hm,fourthRoot_nonneg fmt.leastSubnormal,mul_nonneg hρpos.le hDpos.le]
  have hh := word_face_or_edge fmt hone hE hF hR hv hv0 hv1 hL hadm hA
    (show D≤9*L by dsimp [D]; linarith only [hL]) heD hfD hrD hRE hRF heC hfC hrC
    (hd.trans hge) hu₀ hv₀ huv₀ (hwitness.trans hge) hreduced
  simpa only [hρ,hη] using hh

end DistanceAccuracy.FaceCoverage

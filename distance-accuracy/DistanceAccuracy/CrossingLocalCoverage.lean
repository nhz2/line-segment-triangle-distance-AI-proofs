import DistanceAccuracy.FaceBudget
import DistanceAccuracy.CrossingCoverage

namespace DistanceAccuracy
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant

theorem crossing_local_coverage (fmt : Format)
    {E F R : Vec3 fmt.interchange} {e f r : Fin 3 → ℚ} {u₀ v₀ d L s₀ s₁ delta : ℝ} {R₀ P₀ : Geometry.E3}
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
    (hd : 0≤d) (hs₀ : s₀ ∈ Set.Icc (0:ℝ) 1) (hs₁ : s₁ ∈ Set.Icc (0:ℝ) 1)
    (hu₀ : 0≤u₀) (hv₀ : 0≤v₀) (huv₀ : u₀+v₀≤1)
    (hN : GeometryCoverage.exactCross (realVec e) (realVec f) ≠ 0)
    (hwitness : ‖R₀+s₀ • P₀+u₀ • realVec e+v₀ • realVec f‖≤d+delta)
    (hshift : ‖R₀+s₁ • P₀-realVec r‖≤delta)
    (hheight : |inner ℝ (GeometryCoverage.exactCross (realVec e) (realVec f)) (realVec r)|/
      ‖GeometryCoverage.exactCross (realVec e) (realVec f)‖≤d) :
    let D := (7/2:ℝ)*L
    let W := V (d/(fmt.rho*D))
    UpperSelection.Upper fmt.interchange (fmt.rho*D*(W+4.532)+5*fourthRoot fmt.leastSubnormal)
      (face fmt.interchange R E F (cross3Accurate fmt.interchange E F)).q ∨
    ∃ s u v : ℝ, s ∈ Set.Icc (0:ℝ) 1 ∧ 0≤u ∧ 0≤v ∧ u+v≤1 ∧
      (u=0 ∨ v=0 ∨ u+v=1) ∧ ‖R₀+s • P₀+u • realVec e+v • realVec f‖≤
        max d (fmt.rho*D*(W+0.002)+5*fourthRoot fmt.leastSubnormal)+delta := by
  apply GeometryCoverage.crossing_face_or_edge hN hs₀ hs₁ hu₀ hv₀ huv₀ hwitness hshift hheight
  intro u v hu hv huv hw
  have h := FaceCoverage.face_admissible_clean fmt true hE hF hR hL hadm hlarge hA heD hfD hrD
    hRE hRF heC hfC hrC hd hu hv huv hw
  norm_num only [Bool.true_eq,ite_true,PointProjection.crossCoefficient,V,
    GeometryCoverage.residual,show (361/50:ℝ)=7.22 by norm_num] at h ⊢
  exact h

end DistanceAccuracy

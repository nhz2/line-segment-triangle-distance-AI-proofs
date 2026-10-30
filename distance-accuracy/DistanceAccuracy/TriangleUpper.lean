import DistanceAccuracy.PositiveFeatureUpper
import DistanceAccuracy.CrossingFinal
import DistanceAccuracy.UpperCandidateFiniteness

namespace DistanceAccuracy.TriangleUpper
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge
open DistanceAccuracy.Geometry UpperSelection
set_option maxHeartbeats 1000000

theorem segment_triangle_large (fmt : Format) (x : Segment fmt.interchange)
    (y : Triangle fmt.interchange) (L : ℝ)
    (hadm : admissible fmt.interchange (.segment x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L) :
    Upper fmt.interchange (distance fmt.interchange (.segment x) (.triangle y)+
      36.4*fmt.rho*((7/2)*L)+32*fourthRoot fmt.leastSubnormal)
      (segmentTriangle fmt.interchange x y).q := by
  have hs := mul_nonneg fmt.rho_nonneg hadm.1
  have hh := fourthRoot_nonneg fmt.leastSubnormal
  have hfinite := GlobalUpperAssembly.segment_family_finite fmt x y hadm
  have hresult : Upper fmt.interchange (distance fmt.interchange (.segment x) (.triangle y)+
      (36.4*fmt.rho*((7/2)*L)+32*fourthRoot fmt.leastSubnormal))
      (segmentTriangle fmt.interchange x y).q := by
    apply SharpGlobalUpperAssembly.segment_triangle fmt.interchange x y
      (ssErr := 19*fmt.rho*((7/2)*L)+6*fourthRoot fmt.leastSubnormal)
      (faceErr := 36*fmt.rho*((7/2)*L)+11*fourthRoot fmt.leastSubnormal)
      (crossErr := 36.4*fmt.rho*((7/2)*L)+13*fourthRoot fmt.leastSubnormal)
      (by nlinarith) (by nlinarith) (by nlinarith)
    · intro e
      simpa only [add_assoc] using SegmentUpper.large_upper fmt
        ⟨hadm.1,hadm.2.1,hadm.2.2.1,bounded_edge _ y hadm.2.2.2 e⟩ hlarge
    · exact hfinite.faces
    · exact hfinite.crossing
    · intro k
      simpa only [add_assoc] using PositiveFeatureUpper.segment_face_cover fmt x y L hadm hlarge k
    · intro hzero
      rcases CrossingFinal.large_cover fmt x y L hadm hlarge hzero with h | h | ⟨e,he,hf,hr⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨e,he,hf⟩)
  simpa only [add_assoc] using hresult

theorem triangle_triangle_large (fmt : Format) (x y : Triangle fmt.interchange) (L : ℝ)
    (hadm : admissible fmt.interchange (.triangle x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L) :
    Upper fmt.interchange (distance fmt.interchange (.triangle x) (.triangle y)+
      36.4*fmt.rho*((7/2)*L)+32*fourthRoot fmt.leastSubnormal)
      (triangleTriangle fmt.interchange x y).q := by
  have hs := mul_nonneg fmt.rho_nonneg hadm.1
  have hh := fourthRoot_nonneg fmt.leastSubnormal
  have hfinite := GlobalUpperAssembly.triangle_family_finite fmt x y hadm
  have hresult : Upper fmt.interchange (distance fmt.interchange (.triangle x) (.triangle y)+
      (36.4*fmt.rho*((7/2)*L)+32*fourthRoot fmt.leastSubnormal))
      (triangleTriangle fmt.interchange x y).q := by
    apply SharpGlobalUpperAssembly.triangle_triangle fmt.interchange x y
      (ssErr := 19*fmt.rho*((7/2)*L)+6*fourthRoot fmt.leastSubnormal)
      (faceErr := 36*fmt.rho*((7/2)*L)+11*fourthRoot fmt.leastSubnormal)
      (crossErr := 36.4*fmt.rho*((7/2)*L)+13*fourthRoot fmt.leastSubnormal)
      (by nlinarith) (by nlinarith) (by nlinarith) hfinite.point
    · intro e f
      simpa only [add_assoc] using SegmentUpper.large_upper fmt
        ⟨hadm.1,hadm.2.1,bounded_edge _ x hadm.2.2.1 e,bounded_edge _ y hadm.2.2.2 f⟩ hlarge
    · exact hfinite.facesRight
    · exact hfinite.facesLeft
    · exact hfinite.crossingRight
    · exact hfinite.crossingLeft
    · intro k
      simpa only [add_assoc] using PositiveFeatureUpper.triangle_face_coverR fmt x y L hadm hlarge k
    · intro k
      simpa only [add_assoc] using PositiveFeatureUpper.triangle_face_coverL fmt x y L hadm hlarge k
    · intro e he hzero
      have heAd : admissible fmt.interchange (.segment (edge fmt.interchange x e)) (.triangle y) L :=
        ⟨hadm.1,hadm.2.1,bounded_edge _ x hadm.2.2.1 e,hadm.2.2.2⟩
      rcases CrossingFinal.large_cover fmt (edge fmt.interchange x e) y L heAd hlarge hzero with h | ⟨k,hk⟩ | ⟨f,hf,hb,_⟩
      · exact Or.inl h
      · right; left
        fin_cases k
        · exact ⟨e.1,hk⟩
        · exact ⟨e.2,hk⟩
      · exact Or.inr (Or.inr ⟨e,he,f,hf,hb⟩)
    · intro f hf hzero
      have hfAd : admissible fmt.interchange (.segment (edge fmt.interchange y f)) (.triangle x) L :=
        ⟨hadm.1,hadm.2.1,bounded_edge _ y hadm.2.2.2 f,hadm.2.2.1⟩
      rw [distance_symm fmt.interchange (.triangle x) (.segment (edge fmt.interchange y f))] at hzero
      rcases CrossingFinal.large_cover fmt (edge fmt.interchange y f) x L hfAd hlarge hzero with h | ⟨k,hk⟩ | ⟨e,he,_,hb⟩
      · exact Or.inl h
      · right; left
        fin_cases k
        · exact ⟨f.1,hk⟩
        · exact ⟨f.2,hk⟩
      · exact Or.inr (Or.inr ⟨e,he,f,hf,hb⟩)
  simpa only [add_assoc] using hresult

end DistanceAccuracy.TriangleUpper

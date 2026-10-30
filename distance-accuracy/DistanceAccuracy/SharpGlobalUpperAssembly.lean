import DistanceAccuracy.UpperSelection
import DistanceAccuracy.GeometryFeatures

/-! Global upper-bound assembly from local face/crossing coverage and segment
kernel bounds. The local numerical obligations remain explicit; this module
proves the feature selection and minimum-selection implications. -/
namespace DistanceAccuracy.SharpGlobalUpperAssembly
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge
open UpperSelection DistanceAccuracy.Geometry
variable (I : Interchange) [I.Valid]

lemma upper_mono {a b : ℝ} {w : I.Word} (h : Upper I a w) (hab : a≤b) : Upper I b w := by
  obtain ⟨q,hq,hb⟩ := h
  exact ⟨q,hq,hb.trans hab⟩

def segFace (x : Segment I) (y : Triangle I) (k : Fin 2) : Candidate I :=
  face I (vsub I (y 0) (x k)) (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
    (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))
def segCross (x : Segment I) (y : Triangle I) : Candidate I :=
  crossing I x (y 0) (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
    (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))

/-- Disjoint pairs use exact closest-feature coverage. Intersecting pairs use
the local crossing-or-edge witness theorem. The edge alternatives carry actual score bounds, preserving nonlinear
local error envelopes through the witness-to-kernel transition. -/
theorem segment_triangle (x : Segment I) (y : Triangle I)
    {ssErr faceErr crossErr C : ℝ}
    (hssC : ssErr≤C) (hfC : faceErr≤C)
    (hcC : crossErr≤C)
    (hss : ∀ e, Upper I (distance I (.segment x) (.segment (edge I y e))+ssErr)
      (segmentSegment I x (edge I y e)).q)
    (hf : ∀ k, UpperSelection.Finite I (segFace I x y k).q)
    (hc : UpperSelection.Finite I (segCross I x y).q)
    (faceCover : ∀ k,
      Upper I (distance I (.point (x k)) (.triangle y)+faceErr) (segFace I x y k).q ∨
      ∃ e ∈ edges, Upper I (distance I (.point (x k)) (.triangle y)+faceErr)
        (segmentSegment I x (edge I y e)).q)
    (crossCover : distance I (.segment x) (.triangle y)=0 →
      Upper I crossErr (segCross I x y).q ∨
      (∃ k, Upper I crossErr (segFace I x y k).q) ∨
      ∃ e ∈ edges, Upper I crossErr (segmentSegment I x (edge I y e)).q) :
    Upper I (distance I (.segment x) (.triangle y)+C) (segmentTriangle I x y).q := by
  apply UpperSelection.segmentTriangle_upper I x y (fun e => (hss e).finite I) hf hc
  by_cases hd : distance I (.segment x) (.triangle y)=0
  · rcases crossCover hd with h | ⟨k,h⟩ | ⟨e,he,hgap⟩
    · right; right
      exact upper_mono I h (by rw [hd]; linarith only [hcC])
    · right; left; exact ⟨k,upper_mono I h (by rw [hd]; linarith only [hcC])⟩
    · left; refine ⟨e,he,upper_mono I hgap ?_⟩
      rw [hd]; linarith only [hcC]
  · have hdpos : 0 < distance I (.segment x) (.triangle y) :=
      lt_of_le_of_ne (distance_nonneg I _ _) (Ne.symm hd)
    rcases GeometryFeatures.segment_triangle_positive_features I x y hdpos with ⟨k,hk⟩ | ⟨e,he,hde⟩
    · rcases faceCover k with h | ⟨e,he,hgap⟩
      · right; left; refine ⟨k,upper_mono I h ?_⟩
        rw [hk]; linarith only [hfC]
      · left; refine ⟨e,he,upper_mono I hgap ?_⟩
        rw [hk]; linarith only [hfC]
    · left; refine ⟨e,he,upper_mono I (hss e) ?_⟩
      rw [hde]; linarith only [hssC]

/-- Global triangle coverage. Face coverage returns either the corresponding
face candidate or an exact edge/edge witness. Crossing coverage has the same
form, so the implementation's fixed edge/edge orientation is preserved. -/
theorem triangle_triangle (x y : Triangle I)
    {ssErr faceErr crossErr C : ℝ}
    (hssC : ssErr≤C) (hfC : faceErr≤C)
    (hcC : crossErr≤C)
    (hpp : UpperSelection.Finite I (pointPoint I (x 0) (y 0)).q)
    (hss : ∀ e f, Upper I (distance I (.segment (edge I x e)) (.segment (edge I y f))+ssErr)
      (segmentSegment I (edge I x e) (edge I y f)).q)
    (hfr : ∀ k, UpperSelection.Finite I (triFaceR I x y k).q)
    (hfl : ∀ k, UpperSelection.Finite I (triFaceL I x y k).q)
    (hcr : ∀ e, UpperSelection.Finite I (triCrossR I x y e).q)
    (hcl : ∀ e, UpperSelection.Finite I (triCrossL I x y e).q)
    (faceCoverR : ∀ k,
      Upper I (distance I (.point (x k)) (.triangle y)+faceErr) (triFaceR I x y k).q ∨
      ∃ e ∈ edges, ∃ f ∈ edges, Upper I (distance I (.point (x k)) (.triangle y)+faceErr)
        (segmentSegment I (edge I x e) (edge I y f)).q)
    (faceCoverL : ∀ k,
      Upper I (distance I (.triangle x) (.point (y k))+faceErr) (triFaceL I x y k).q ∨
      ∃ e ∈ edges, ∃ f ∈ edges, Upper I (distance I (.triangle x) (.point (y k))+faceErr)
        (segmentSegment I (edge I x e) (edge I y f)).q)
    (crossCoverR : ∀ e ∈ edges, distance I (.segment (edge I x e)) (.triangle y)=0 →
      Upper I crossErr (triCrossR I x y e).q ∨
      (∃ k, Upper I crossErr (triFaceR I x y k).q) ∨
      ∃ e' ∈ edges, ∃ f ∈ edges, Upper I crossErr (segmentSegment I (edge I x e') (edge I y f)).q)
    (crossCoverL : ∀ f ∈ edges, distance I (.triangle x) (.segment (edge I y f))=0 →
      Upper I crossErr (triCrossL I x y f).q ∨
      (∃ k, Upper I crossErr (triFaceL I x y k).q) ∨
      ∃ e ∈ edges, ∃ f' ∈ edges, Upper I crossErr (segmentSegment I (edge I x e) (edge I y f')).q) :
    Upper I (distance I (.triangle x) (.triangle y)+C) (triangleTriangle I x y).q := by
  apply UpperSelection.triangleTriangle_upper I x y hpp (fun e f => (hss e f).finite I) hfr hfl hcr hcl
  by_cases hd : distance I (.triangle x) (.triangle y)=0
  · rcases GeometryFeatures.triangle_triangle_intersection_features I x y hd with ⟨e,he,hzero⟩ | ⟨f,hf,hzero⟩
    · rcases crossCoverR e he hzero with h | ⟨k,h⟩ | ⟨e',he',f,hf,hgap⟩
      · right; right; right; right; left
        exact ⟨e,he,upper_mono I h (by rw [hd]; linarith only [hcC])⟩
      · right; right; left
        exact ⟨k,upper_mono I h (by rw [hd]; linarith only [hcC])⟩
      · right; left; refine ⟨e',he',f,hf,upper_mono I hgap ?_⟩
        rw [hd]; linarith only [hcC]
    · rcases crossCoverL f hf hzero with h | ⟨k,h⟩ | ⟨e,he,f',hf',hgap⟩
      · right; right; right; right; right
        exact ⟨f,hf,upper_mono I h (by rw [hd]; linarith only [hcC])⟩
      · right; right; right; left
        exact ⟨k,upper_mono I h (by rw [hd]; linarith only [hcC])⟩
      · right; left; refine ⟨e,he,f',hf',upper_mono I hgap ?_⟩
        rw [hd]; linarith only [hcC]
  · have hdpos : 0 < distance I (.triangle x) (.triangle y) :=
      lt_of_le_of_ne (distance_nonneg I _ _) (Ne.symm hd)
    rcases GeometryFeatures.triangle_triangle_positive_features I x y hdpos with
      ⟨i,hi⟩ | ⟨j,hj⟩ | ⟨e,he,f,hf,hde⟩
    · rcases faceCoverR i with h | ⟨e,he,f,hf,hgap⟩
      · right; right; left; refine ⟨i,upper_mono I h ?_⟩
        rw [hi]; linarith only [hfC]
      · right; left; refine ⟨e,he,f,hf,upper_mono I hgap ?_⟩
        rw [hi]; linarith only [hfC]
    · rcases faceCoverL j with h | ⟨e,he,f,hf,hgap⟩
      · right; right; right; left; refine ⟨j,upper_mono I h ?_⟩
        rw [hj]; linarith only [hfC]
      · right; left; refine ⟨e,he,f,hf,upper_mono I hgap ?_⟩
        rw [hj]; linarith only [hfC]
    · right; left; refine ⟨e,he,f,hf,upper_mono I (hss e f) ?_⟩
      rw [hde]; linarith only [hssC]

end DistanceAccuracy.SharpGlobalUpperAssembly

import DistanceAccuracy.UpperSelection
import DistanceAccuracy.GeometryFeatures

/-! Global upper-bound assembly from local face/crossing coverage and segment
kernel bounds. The local numerical obligations remain explicit; this module
proves the feature selection and minimum-selection implications. -/
namespace DistanceAccuracy.GlobalUpperAssembly
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
the local crossing-or-edge witness theorem. Numerical errors add only at the
local witness-to-edge-kernel transition. -/
theorem segment_triangle (x : Segment I) (y : Triangle I)
    {ssErr faceErr faceGap crossErr crossGap C : ℝ}
    (hssC : ssErr≤C) (hfC : faceErr≤C) (hfgC : faceGap+ssErr≤C)
    (hcC : crossErr≤C) (hcgC : crossGap+ssErr≤C)
    (hss : ∀ e, Upper I (distance I (.segment x) (.segment (edge I y e))+ssErr)
      (segmentSegment I x (edge I y e)).q)
    (hf : ∀ k, UpperSelection.Finite I (segFace I x y k).q)
    (hc : UpperSelection.Finite I (segCross I x y).q)
    (faceCover : ∀ k,
      Upper I (distance I (.point (x k)) (.triangle y)+faceErr) (segFace I x y k).q ∨
      ∃ e ∈ edges, distance I (.segment x) (.segment (edge I y e)) ≤
        distance I (.point (x k)) (.triangle y)+faceGap)
    (crossCover : distance I (.segment x) (.triangle y)=0 →
      Upper I crossErr (segCross I x y).q ∨
      (∃ k, Upper I crossErr (segFace I x y k).q) ∨
      ∃ e ∈ edges, distance I (.segment x) (.segment (edge I y e))≤crossGap) :
    Upper I (distance I (.segment x) (.triangle y)+C) (segmentTriangle I x y).q := by
  apply UpperSelection.segmentTriangle_upper I x y (fun e => (hss e).finite I) hf hc
  by_cases hd : distance I (.segment x) (.triangle y)=0
  · rcases crossCover hd with h | ⟨k,h⟩ | ⟨e,he,hgap⟩
    · right; right
      exact upper_mono I h (by rw [hd]; linarith only [hcC])
    · right; left; exact ⟨k,upper_mono I h (by rw [hd]; linarith only [hcC])⟩
    · left; refine ⟨e,he,upper_mono I (hss e) ?_⟩
      rw [hd]; linarith only [hgap,hcgC]
  · have hdpos : 0 < distance I (.segment x) (.triangle y) :=
      lt_of_le_of_ne (distance_nonneg I _ _) (Ne.symm hd)
    rcases GeometryFeatures.segment_triangle_positive_features I x y hdpos with ⟨k,hk⟩ | ⟨e,he,hde⟩
    · rcases faceCover k with h | ⟨e,he,hgap⟩
      · right; left; refine ⟨k,upper_mono I h ?_⟩
        rw [hk]; linarith only [hfC]
      · left; refine ⟨e,he,upper_mono I (hss e) ?_⟩
        rw [hk]; linarith only [hgap,hfgC]
    · left; refine ⟨e,he,upper_mono I (hss e) ?_⟩
      rw [hde]; linarith only [hssC]

/-- Global triangle coverage. Face coverage returns either the corresponding
face candidate or an exact edge/edge witness. Crossing coverage has the same
form, so the implementation's fixed edge/edge orientation is preserved. -/
theorem triangle_triangle (x y : Triangle I)
    {ssErr faceErr faceGap crossErr crossGap C : ℝ}
    (hssC : ssErr≤C) (hfC : faceErr≤C) (hfgC : faceGap+ssErr≤C)
    (hcC : crossErr≤C) (hcgC : crossGap+ssErr≤C)
    (hpp : UpperSelection.Finite I (pointPoint I (x 0) (y 0)).q)
    (hss : ∀ e f, Upper I (distance I (.segment (edge I x e)) (.segment (edge I y f))+ssErr)
      (segmentSegment I (edge I x e) (edge I y f)).q)
    (hfr : ∀ k, UpperSelection.Finite I (triFaceR I x y k).q)
    (hfl : ∀ k, UpperSelection.Finite I (triFaceL I x y k).q)
    (hcr : ∀ e, UpperSelection.Finite I (triCrossR I x y e).q)
    (hcl : ∀ e, UpperSelection.Finite I (triCrossL I x y e).q)
    (faceCoverR : ∀ k,
      Upper I (distance I (.point (x k)) (.triangle y)+faceErr) (triFaceR I x y k).q ∨
      ∃ e ∈ edges, ∃ f ∈ edges, distance I (.segment (edge I x e)) (.segment (edge I y f)) ≤
        distance I (.point (x k)) (.triangle y)+faceGap)
    (faceCoverL : ∀ k,
      Upper I (distance I (.triangle x) (.point (y k))+faceErr) (triFaceL I x y k).q ∨
      ∃ e ∈ edges, ∃ f ∈ edges, distance I (.segment (edge I x e)) (.segment (edge I y f)) ≤
        distance I (.triangle x) (.point (y k))+faceGap)
    (crossCoverR : ∀ e ∈ edges, distance I (.segment (edge I x e)) (.triangle y)=0 →
      Upper I crossErr (triCrossR I x y e).q ∨
      (∃ k, Upper I crossErr (triFaceR I x y k).q) ∨
      ∃ e' ∈ edges, ∃ f ∈ edges, distance I (.segment (edge I x e')) (.segment (edge I y f))≤crossGap)
    (crossCoverL : ∀ f ∈ edges, distance I (.triangle x) (.segment (edge I y f))=0 →
      Upper I crossErr (triCrossL I x y f).q ∨
      (∃ k, Upper I crossErr (triFaceL I x y k).q) ∨
      ∃ e ∈ edges, ∃ f' ∈ edges, distance I (.segment (edge I x e)) (.segment (edge I y f'))≤crossGap) :
    Upper I (distance I (.triangle x) (.triangle y)+C) (triangleTriangle I x y).q := by
  apply UpperSelection.triangleTriangle_upper I x y hpp (fun e f => (hss e f).finite I) hfr hfl hcr hcl
  by_cases hd : distance I (.triangle x) (.triangle y)=0
  · rcases GeometryFeatures.triangle_triangle_intersection_features I x y hd with ⟨e,he,hzero⟩ | ⟨f,hf,hzero⟩
    · rcases crossCoverR e he hzero with h | ⟨k,h⟩ | ⟨e',he',f,hf,hgap⟩
      · right; right; right; right; left
        exact ⟨e,he,upper_mono I h (by rw [hd]; linarith only [hcC])⟩
      · right; right; left
        exact ⟨k,upper_mono I h (by rw [hd]; linarith only [hcC])⟩
      · right; left; refine ⟨e',he',f,hf,upper_mono I (hss e' f) ?_⟩
        rw [hd]; linarith only [hgap,hcgC]
    · rcases crossCoverL f hf hzero with h | ⟨k,h⟩ | ⟨e,he,f',hf',hgap⟩
      · right; right; right; right; right
        exact ⟨f,hf,upper_mono I h (by rw [hd]; linarith only [hcC])⟩
      · right; right; right; left
        exact ⟨k,upper_mono I h (by rw [hd]; linarith only [hcC])⟩
      · right; left; refine ⟨e,he,f',hf',upper_mono I (hss e f') ?_⟩
        rw [hd]; linarith only [hgap,hcgC]
  · have hdpos : 0 < distance I (.triangle x) (.triangle y) :=
      lt_of_le_of_ne (distance_nonneg I _ _) (Ne.symm hd)
    rcases GeometryFeatures.triangle_triangle_positive_features I x y hdpos with
      ⟨i,hi⟩ | ⟨j,hj⟩ | ⟨e,he,f,hf,hde⟩
    · rcases faceCoverR i with h | ⟨e,he,f,hf,hgap⟩
      · right; right; left; refine ⟨i,upper_mono I h ?_⟩
        rw [hi]; linarith only [hfC]
      · right; left; refine ⟨e,he,f,hf,upper_mono I (hss e f) ?_⟩
        rw [hi]; linarith only [hgap,hfgC]
    · rcases faceCoverL j with h | ⟨e,he,f,hf,hgap⟩
      · right; right; right; left; refine ⟨j,upper_mono I h ?_⟩
        rw [hj]; linarith only [hfC]
      · right; left; refine ⟨e,he,f,hf,upper_mono I (hss e f) ?_⟩
        rw [hj]; linarith only [hgap,hfgC]
    · right; left; refine ⟨e,he,f,hf,upper_mono I (hss e f) ?_⟩
      rw [hde]; linarith only [hssC]

omit [I.Valid] in
/-- The larger 36.4 coefficient still fits the requested constant 64 when the
geometric scale is D=3.5L. Thirty-two subnormal fourth-root remainders fit as well. -/
lemma final_constant_budget (f : DistanceAccuracy.Format) {L : ℝ} (hL : 0≤L) :
    (36.4:ℝ)*f.rho*((7/2:ℝ)*L)+32*fourthRoot f.leastSubnormal ≤
      64*(2*f.rho)*L+fourthRoot f.leastNormal := by
  have hh := f.underflow_budget
  have hr := mul_nonneg f.rho_nonneg hL
  have hs := fourthRoot_nonneg f.leastSubnormal
  nlinarith only [hh,hr,hs]

end DistanceAccuracy.GlobalUpperAssembly

import DistanceAccuracy.FeatureEmbedding
import DistanceAccuracy.SegmentUpper
import DistanceAccuracy.EnvelopeBudget
import DistanceAccuracy.AccurateFaceBoundary
import DistanceAccuracy.SharpGlobalUpperAssembly

namespace DistanceAccuracy.PositiveFeatureUpper
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds
open DistanceAccuracy.Geometry UpperSelection
set_option maxHeartbeats 800000

lemma edge_bound (fmt : Format) {x y : Segment fmt.interchange} {L d : ℝ}
    (hadm : Geometry.admissible fmt.interchange (.segment x) (.segment y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L) (hd : 0 ≤ d)
    (hbound : Geometry.distance fmt.interchange (.segment x) (.segment y) ≤
      d+18.01*fmt.rho*((7/2)*L)+5*fourthRoot fmt.leastSubnormal) :
    Upper fmt.interchange (d+36*fmt.rho*((7/2)*L)+11*fourthRoot fmt.leastSubnormal)
      (segmentSegment fmt.interchange x y).q := by
  let S := fmt.rho*((7/2)*L)
  let h := fourthRoot fmt.leastSubnormal
  have hh : 0 ≤ h := fourthRoot_nonneg _
  have hS : 0 < S := by
    have hL : 0 < L := by
      have hH : 0 < fourthRoot fmt.leastNormal := by
        unfold fourthRoot
        apply Real.sqrt_pos.mpr
        apply Real.sqrt_pos.mpr
        cases fmt <;> norm_num [Format.leastNormal]
      linarith
    have hr : 0 < fmt.rho := by cases fmt <;> norm_num [Format.rho]
    dsimp [S]; positivity
  have hrho := fmt.rho_nonneg
  have hL := hadm.1
  obtain ⟨q,hq,hb⟩ := SegmentUpper.distance_upper_sharp fmt hadm hlarge
    (by positivity : 0 ≤ d+18.01*fmt.rho*((7/2)*L)+5*fourthRoot fmt.leastSubnormal) hbound
  refine ⟨q,hq,?_⟩
  have hs := scaled_F_bound hS
    (show 0 ≤ (d+18.01*S+5*h)+3*S by positivity)
    (show 0 ≤ (21.01:ℝ) by norm_num) (show 0 ≤ d+5*h by positivity)
    (show (d+18.01*S+5*h)+3*S ≤ S*21.01+(d+5*h) by ring_nf; rfl)
  have hc := (F_mono (show (0:ℝ) ≤ 21.01 by norm_num) (show (21.01:ℝ) ≤ 23 by norm_num))
  have hcoef : F 21.01+3.55 ≤ (36:ℝ) := by linarith [thin_final_coefficient]
  have hm := mul_le_mul_of_nonneg_left hcoef hS.le
  dsimp [S,h] at *
  simp only [mul_assoc] at hb hs
  nlinarith only [hb,hs,hm]

noncomputable def accurateFace (fmt : Format) (x : Vec3 fmt.interchange) (y : Triangle fmt.interchange) :=
  face fmt.interchange (vsub fmt.interchange (y 0) x) (vsub fmt.interchange (y 1) (y 0))
    (vsub fmt.interchange (y 2) (y 0))
    (cross3Accurate fmt.interchange (vsub fmt.interchange (y 1) (y 0)) (vsub fmt.interchange (y 2) (y 0)))

/-- A closest point of the original triangle supplies either the actual
accurate face candidate or a nearby original boundary edge. -/
lemma face_or_edge_distance (fmt : Format) (x : Vec3 fmt.interchange) (y : Triangle fmt.interchange) (L : ℝ)
    (hadm : Geometry.admissible fmt.interchange (.point x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L) :
    Upper fmt.interchange (distance fmt.interchange (.point x) (.triangle y)+
      21*fmt.rho*((7/2)*L)+5*fourthRoot fmt.leastSubnormal) (accurateFace fmt x y).q ∨
    ∃ e ∈ edges, distance fmt.interchange (.point x) (.segment (edge fmt.interchange y e)) ≤
      distance fmt.interchange (.point x) (.triangle y)+18.01*fmt.rho*((7/2)*L)+5*fourthRoot fmt.leastSubnormal := by
  obtain ⟨X,hx,hX⟩ := PointTriangleUpper.bounded_vertex fmt hadm.2.2.1 0
  obtain ⟨A,ha,hA⟩ := PointTriangleUpper.bounded_vertex fmt hadm.2.2.2 0
  obtain ⟨B,hb,hB⟩ := PointTriangleUpper.bounded_vertex fmt hadm.2.2.2 1
  obtain ⟨C,hc,hC⟩ := PointTriangleUpper.bounded_vertex fmt hadm.2.2.2 2
  obtain ⟨u,v,hu,hv,huv,hw⟩ := closest_point_triangle fmt.interchange x y
  have conv {w : Vec3 fmt.interchange} {v : Fin 3 → ℚ}
      (hv : ∀ i, value? fmt.interchange (w i) = some (v i)) :
      Determinant.realVec v = decodeVec fmt.interchange w := by
    ext i
    simp [Determinant.realVec,decodeVec,real_decode fmt.interchange (hv i)]
  have hw' : ‖Determinant.realVec A-Determinant.realVec X+
      u•(Determinant.realVec B-Determinant.realVec A)+v•(Determinant.realVec C-Determinant.realVec A)‖ ≤
      distance fmt.interchange (.point x) (.triangle y) := by
    rw [conv ha,conv hb,conv hc,conv hx]
    exact hw.ge
  rcases PointTriangleUpper.accurate_face_or_original_boundary fmt hx ha hb hc hX hA hB hC hadm.1 hadm.2.1 hlarge
      (distance_nonneg _ _ _) hu hv huv hw' with hf | ⟨u',v',hu',hv',huv',hboundary,hbound⟩
  · exact Or.inl hf
  · obtain ⟨e,he,hm⟩ := boundary_incident_edge fmt.interchange y hu' hv' huv' hboundary
    right
    refine ⟨e,he,?_⟩
    have hd := distance_le fmt.interchange (vertex_mem fmt.interchange (.point x) 0) hm
    rw [conv ha,conv hb,conv hc,conv hx] at hbound
    have hid :
        decodeVec fmt.interchange (y 0)+u'•(decodeVec fmt.interchange (y 1)-decodeVec fmt.interchange (y 0))+
        v'•(decodeVec fmt.interchange (y 2)-decodeVec fmt.interchange (y 0))-decodeVec fmt.interchange x =
        decodeVec fmt.interchange (y 0)-decodeVec fmt.interchange x+
        u'•(decodeVec fmt.interchange (y 1)-decodeVec fmt.interchange (y 0))+
        v'•(decodeVec fmt.interchange (y 2)-decodeVec fmt.interchange (y 0)) := by module
    change distance _ _ _ ≤ ‖_ -decodeVec fmt.interchange x‖ at hd
    rw [hid] at hd
    exact hd.trans (by simpa [vertices, show (1801/100:ℝ) = 18.01 by norm_num] using hbound)

lemma point_carrier_subset_of_mem (I : Interchange) {x : Vec3 I} {s : Simplex I}
    (hm : decodeVec I x ∈ carrier I s) : carrier I (.point x) ⊆ carrier I s := by
  rw [point_carrier]
  exact Set.singleton_subset_iff.mpr hm

lemma face_cover_forward (fmt : Format) (p : Vec3 fmt.interchange) (x : Segment fmt.interchange)
    (y : Triangle fmt.interchange) (L : ℝ)
    (hadm : admissible fmt.interchange (.segment x) (.triangle y) L)
    (hp : boundedInput fmt.interchange (.point p) L)
    (hmem : decodeVec fmt.interchange p ∈ carrier fmt.interchange (.segment x))
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L) :
    Upper fmt.interchange (distance fmt.interchange (.point p) (.triangle y)+
      36*fmt.rho*((7/2)*L)+11*fourthRoot fmt.leastSubnormal) (accurateFace fmt p y).q ∨
    ∃ e ∈ edges, Upper fmt.interchange (distance fmt.interchange (.point p) (.triangle y)+
      36*fmt.rho*((7/2)*L)+11*fourthRoot fmt.leastSubnormal) (segmentSegment fmt.interchange x (edge fmt.interchange y e)).q := by
  have hsmall := face_or_edge_distance fmt p y L ⟨hadm.1,hadm.2.1,hp,hadm.2.2.2⟩ hlarge
  rcases hsmall with hf | ⟨e,he,hb⟩
  · left
    apply PointTriangleUpper.upper_mono hf
    have hs := mul_nonneg fmt.rho_nonneg hadm.1
    have hh := fourthRoot_nonneg fmt.leastSubnormal
    nlinarith
  · right; refine ⟨e,he,?_⟩
    apply edge_bound fmt ⟨hadm.1,hadm.2.1,hadm.2.2.1,bounded_edge _ y hadm.2.2.2 e⟩ hlarge (distance_nonneg _ _ _)
    exact (distance_mono fmt.interchange (point_carrier_subset_of_mem _ hmem) (Set.Subset.refl _)).trans hb

lemma face_cover_reverse (fmt : Format) (p : Vec3 fmt.interchange) (x : Triangle fmt.interchange)
    (y : Segment fmt.interchange) (L : ℝ)
    (hadm : admissible fmt.interchange (.triangle x) (.segment y) L)
    (hp : boundedInput fmt.interchange (.point p) L)
    (hmem : decodeVec fmt.interchange p ∈ carrier fmt.interchange (.segment y))
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L) :
    Upper fmt.interchange (distance fmt.interchange (.triangle x) (.point p)+
      36*fmt.rho*((7/2)*L)+11*fourthRoot fmt.leastSubnormal) (accurateFace fmt p x).q ∨
    ∃ e ∈ edges, Upper fmt.interchange (distance fmt.interchange (.triangle x) (.point p)+
      36*fmt.rho*((7/2)*L)+11*fourthRoot fmt.leastSubnormal) (segmentSegment fmt.interchange (edge fmt.interchange x e) y).q := by
  have hsmall := face_or_edge_distance fmt p x L ⟨hadm.1,hadm.2.1,hp,hadm.2.2.1⟩ hlarge
  rw [distance_symm fmt.interchange (.triangle x) (.point p)]
  rcases hsmall with hf | ⟨e,he,hb⟩
  · left
    apply PointTriangleUpper.upper_mono hf
    have hs := mul_nonneg fmt.rho_nonneg hadm.1
    have hh := fourthRoot_nonneg fmt.leastSubnormal
    nlinarith
  · right; refine ⟨e,he,?_⟩
    apply edge_bound fmt ⟨hadm.1,hadm.2.1,bounded_edge _ x hadm.2.2.1 e,hadm.2.2.2⟩ hlarge (distance_nonneg _ _ _)
    have hd := distance_mono fmt.interchange (Set.Subset.refl (carrier fmt.interchange (.segment (edge fmt.interchange x e))))
      (point_carrier_subset_of_mem _ hmem)
    rw [distance_symm fmt.interchange (.segment (edge fmt.interchange x e)) (.point p)] at hd
    exact hd.trans hb

lemma segment_vertex_bounded (I : Interchange) {x : Segment I} {L : ℝ}
    (hx : boundedInput I (.segment x) L) (k : Fin 2) : boundedInput I (.point (x k)) L := by
  fin_cases k
  · exact bounded_point I (.segment x) hx 0
  · exact bounded_point I (.segment x) hx 1

lemma segment_vertex_mem (I : Interchange) (x : Segment I) (k : Fin 2) :
    decodeVec I (x k) ∈ carrier I (.segment x) := by
  fin_cases k
  · exact vertex_mem I (.segment x) 0
  · exact vertex_mem I (.segment x) 1

lemma segment_face_cover (fmt : Format) (x : Segment fmt.interchange) (y : Triangle fmt.interchange) (L : ℝ)
    (hadm : admissible fmt.interchange (.segment x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L) (k : Fin 2) :
    Upper fmt.interchange (distance fmt.interchange (.point (x k)) (.triangle y)+
      36*fmt.rho*((7/2)*L)+11*fourthRoot fmt.leastSubnormal) (SharpGlobalUpperAssembly.segFace fmt.interchange x y k).q ∨
    ∃ e ∈ edges, Upper fmt.interchange (distance fmt.interchange (.point (x k)) (.triangle y)+
      36*fmt.rho*((7/2)*L)+11*fourthRoot fmt.leastSubnormal) (segmentSegment fmt.interchange x (edge fmt.interchange y e)).q :=
  face_cover_forward fmt (x k) x y L hadm (segment_vertex_bounded _ hadm.2.2.1 k)
    (segment_vertex_mem _ x k) hlarge

lemma triangle_face_coverR (fmt : Format) (x y : Triangle fmt.interchange) (L : ℝ)
    (hadm : admissible fmt.interchange (.triangle x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L) (k : Fin 3) :
    Upper fmt.interchange (distance fmt.interchange (.point (x k)) (.triangle y)+
      36*fmt.rho*((7/2)*L)+11*fourthRoot fmt.leastSubnormal) (triFaceR fmt.interchange x y k).q ∨
    ∃ e ∈ edges, ∃ f ∈ edges, Upper fmt.interchange (distance fmt.interchange (.point (x k)) (.triangle y)+
      36*fmt.rho*((7/2)*L)+11*fourthRoot fmt.leastSubnormal)
      (segmentSegment fmt.interchange (edge fmt.interchange x e) (edge fmt.interchange y f)).q := by
  obtain ⟨e,he,hm⟩ := vertex_incident_edge fmt.interchange x k
  have hh := face_cover_forward fmt (x k) (edge fmt.interchange x e) y L
    ⟨hadm.1,hadm.2.1,bounded_edge _ x hadm.2.2.1 e,hadm.2.2.2⟩
    (bounded_point _ (.triangle x) hadm.2.2.1 k) hm hlarge
  rcases hh with hf | ⟨f,hf,hb⟩
  · exact Or.inl hf
  · exact Or.inr ⟨e,he,f,hf,hb⟩

lemma triangle_face_coverL (fmt : Format) (x y : Triangle fmt.interchange) (L : ℝ)
    (hadm : admissible fmt.interchange (.triangle x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L) (k : Fin 3) :
    Upper fmt.interchange (distance fmt.interchange (.triangle x) (.point (y k))+
      36*fmt.rho*((7/2)*L)+11*fourthRoot fmt.leastSubnormal) (triFaceL fmt.interchange x y k).q ∨
    ∃ e ∈ edges, ∃ f ∈ edges, Upper fmt.interchange (distance fmt.interchange (.triangle x) (.point (y k))+
      36*fmt.rho*((7/2)*L)+11*fourthRoot fmt.leastSubnormal)
      (segmentSegment fmt.interchange (edge fmt.interchange x e) (edge fmt.interchange y f)).q := by
  obtain ⟨f,hf,hm⟩ := vertex_incident_edge fmt.interchange y k
  have hh := face_cover_reverse fmt (y k) x (edge fmt.interchange y f) L
    ⟨hadm.1,hadm.2.1,hadm.2.2.1,bounded_edge _ y hadm.2.2.2 f⟩
    (bounded_point _ (.triangle y) hadm.2.2.2 k) hm hlarge
  rcases hh with hface | ⟨e,he,hb⟩
  · exact Or.inl hface
  · exact Or.inr ⟨e,he,f,hf,hb⟩

end DistanceAccuracy.PositiveFeatureUpper

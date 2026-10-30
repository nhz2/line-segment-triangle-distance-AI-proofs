import DistanceAccuracy.GeometrySubsimplex
import DistanceAccuracy.LowerBound
namespace DistanceAccuracy.Geometry
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm
variable (I : Interchange)

lemma triangle_carrier (y : Triangle I) (p : E3) : p ∈ carrier I (.triangle y) ↔
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u+v ≤ 1 ∧
      p = decodeVec I (y 0)+u•(decodeVec I (y 1)-decodeVec I (y 0))+
        v•(decodeVec I (y 2)-decodeVec I (y 0)) := by
  let A := decodeVec I (y 0)
  let B := decodeVec I (y 1)
  let C := decodeVec I (y 2)
  let S : Set E3 := {p | ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u+v ≤ 1 ∧
    p = A+u•(B-A)+v•(C-A)}
  have hc : Convex ℝ S := by
    rintro x ⟨u,v,hu,hv,hs,rfl⟩ z ⟨u',v',hu',hv',hs',rfl⟩ a b ha hb hab
    refine ⟨a*u+b*u',a*v+b*v',by positivity,by positivity,?_,?_⟩
    · nlinarith [mul_nonneg ha (sub_nonneg.mpr hs), mul_nonneg hb (sub_nonneg.mpr hs')]
    · have hbEq : b = 1-a := by linarith
      rw [hbEq]
      module
  constructor
  · intro hp
    apply convexHull_min (t := S) ?_ hc hp
    rintro z ⟨j,rfl⟩
    fin_cases j
    · exact ⟨0,0,by norm_num,by norm_num,by norm_num,by simp [A,S,vertices]⟩
    · exact ⟨1,0,by norm_num,by norm_num,by norm_num,by simp [A,B,S,vertices]⟩
    · exact ⟨0,1,by norm_num,by norm_num,by norm_num,by simp [A,C,S,vertices]⟩
  · rintro ⟨u,v,hu,hv,hs,rfl⟩
    exact LowerBound.bary_mem (carrier_convex I (.triangle y))
      (vertex_mem I (.triangle y) 0) (vertex_mem I (.triangle y) 1)
      (vertex_mem I (.triangle y) 2) hu hv hs

lemma closest_point_triangle (x : Vec3 I) (y : Triangle I) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u+v ≤ 1 ∧
      distance I (.point x) (.triangle y) =
      ‖decodeVec I (y 0)-decodeVec I x+u•(decodeVec I (y 1)-decodeVec I (y 0))+
        v•(decodeVec I (y 2)-decodeVec I (y 0))‖ := by
  obtain ⟨a,ha,b,hb,he⟩ := closest_pair I (.point x) (.triangle y)
  rw [point_carrier] at ha
  have ha' : a = decodeVec I x := ha
  obtain ⟨u,v,hu,hv,hs,rfl⟩ := (triangle_carrier I y b).mp hb
  refine ⟨u,v,hu,hv,hs,?_⟩
  rw [he,ha']
  congr 1
  module

lemma closest_segment_triangle (x : Segment I) (y : Triangle I) :
    ∃ s u v : ℝ, s ∈ Set.Icc (0:ℝ) 1 ∧ 0 ≤ u ∧ 0 ≤ v ∧ u+v ≤ 1 ∧
      distance I (.segment x) (.triangle y) =
      ‖decodeVec I (y 0)+u•(decodeVec I (y 1)-decodeVec I (y 0))+
        v•(decodeVec I (y 2)-decodeVec I (y 0))-
        (decodeVec I (x 0)+s•(decodeVec I (x 1)-decodeVec I (x 0)))‖ := by
  obtain ⟨a,ha,b,hb,he⟩ := closest_pair I (.segment x) (.triangle y)
  rw [segment_carrier] at ha
  obtain ⟨s,hs,rfl⟩ := ha
  obtain ⟨u,v,hu,hv,huv,rfl⟩ := (triangle_carrier I y b).mp hb
  exact ⟨s,u,v,hs,hu,hv,huv,he⟩
end DistanceAccuracy.Geometry

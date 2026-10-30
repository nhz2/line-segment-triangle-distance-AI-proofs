import DistanceAccuracy.TriangleCarrier

namespace DistanceAccuracy.Geometry
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm
variable (I : Interchange)

lemma vertex_incident_edge (x : Triangle I) (j : Fin 3) :
    ∃ e ∈ edges, decodeVec I (x j) ∈ carrier I (.segment (edge I x e)) := by
  fin_cases j
  · refine ⟨(0,1),by simp [edges],?_⟩
    exact vertex_mem I (.segment (edge I x (0,1))) 0
  · refine ⟨(0,1),by simp [edges],?_⟩
    exact vertex_mem I (.segment (edge I x (0,1))) 1
  · refine ⟨(0,2),by simp [edges],?_⟩
    exact vertex_mem I (.segment (edge I x (0,2))) 1

lemma boundary_incident_edge (x : Triangle I) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v ≤ 1) (hb : u=0 ∨ u+v=1) :
    ∃ e ∈ edges,
      decodeVec I (x 0)+u•(decodeVec I (x 1)-decodeVec I (x 0))+
        v•(decodeVec I (x 2)-decodeVec I (x 0)) ∈ carrier I (.segment (edge I x e)) := by
  rcases hb with rfl | hb
  · refine ⟨(0,2),by simp [edges],?_⟩
    rw [segment_carrier]
    refine ⟨v,⟨hv,by linarith⟩,?_⟩
    simp [edge]
  · refine ⟨(1,2),by simp [edges],?_⟩
    rw [segment_carrier]
    refine ⟨v,⟨hv,by linarith⟩,?_⟩
    simp only [edge, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,Fin.isValue,Fin.reduceFinMk]
    have he : u=1-v := by linarith
    rw [he]
    module

end DistanceAccuracy.Geometry

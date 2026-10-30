import DistanceAccuracy.Geometry

namespace DistanceAccuracy.Geometry
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm
variable (I : Interchange)

lemma carrier_subset_of_vertices {x y : Simplex I}
    (h : ∀ j, decodeVec I (vertices I x j) ∈ carrier I y) :
    carrier I x ⊆ carrier I y := by
  apply convexHull_min
  · rintro p ⟨j, rfl⟩; exact h j
  · exact carrier_convex I y

lemma point_carrier_subset (x : Simplex I) (j : Fin 3) :
    carrier I (.point (vertices I x j)) ⊆ carrier I x := by
  apply carrier_subset_of_vertices I
  intro k
  exact vertex_mem I x j

lemma edge_carrier_subset (x : Triangle I) (e : Fin 3 × Fin 3) :
    carrier I (.segment (edge I x e)) ⊆ carrier I (.triangle x) := by
  apply carrier_subset_of_vertices I
  intro j
  fin_cases j <;> simp only [vertices, edge, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue, Fin.reduceFinMk]
  all_goals apply vertex_mem I (.triangle x)

lemma point_carrier (x : Vec3 I) : carrier I (.point x) = {decodeVec I x} := by
  simp [carrier, vertices]

lemma distance_point_point (x y : Vec3 I) :
    distance I (.point x) (.point y) = ‖decodeVec I y-decodeVec I x‖ := by
  obtain ⟨a, ha, b, hb, h⟩ := closest_pair I (.point x) (.point y)
  rw [point_carrier] at ha hb
  simp only [Set.mem_singleton_iff] at ha hb
  simpa [ha, hb] using h

lemma segment_carrier (x : Segment I) : carrier I (.segment x) =
    (fun t : ℝ => decodeVec I (x 0)+t•(decodeVec I (x 1)-decodeVec I (x 0))) '' Set.Icc 0 1 := by
  have hr : Set.range (fun j => decodeVec I (vertices I (.segment x) j)) =
      {decodeVec I (x 0), decodeVec I (x 1)} := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [vertices]
    · intro hz
      rcases hz with hz | hz
      · exact ⟨0, by simpa [vertices] using hz.symm⟩
      · exact ⟨1, by simpa [vertices] using hz.symm⟩
  unfold carrier
  rw [hr, convexHull_pair, segment_eq_image']

lemma closest_point_segment (x : Vec3 I) (y : Segment I) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ distance I (.point x) (.segment y) =
      ‖decodeVec I (y 0)-decodeVec I x+t•(decodeVec I (y 1)-decodeVec I (y 0))‖ := by
  obtain ⟨a, ha, b, hb, he⟩ := closest_pair I (.point x) (.segment y)
  rw [point_carrier] at ha
  have ha' : a = decodeVec I x := ha
  rw [segment_carrier] at hb
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hb
  refine ⟨t, ht0, ht1, ?_⟩
  rw [he, ha']
  congr 1
  module

lemma closest_segments (x y : Segment I) :
    ∃ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 ∧ t ∈ Set.Icc (0:ℝ) 1 ∧
      distance I (.segment x) (.segment y) =
      ‖decodeVec I (y 0)-decodeVec I (x 0)+t•(decodeVec I (y 1)-decodeVec I (y 0))-
        s•(decodeVec I (x 1)-decodeVec I (x 0))‖ := by
  obtain ⟨a, ha, b, hb, he⟩ := closest_pair I (.segment x) (.segment y)
  rw [segment_carrier] at ha hb
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  refine ⟨s,t,hs,ht,?_⟩
  rw [he]
  congr 1
  module

lemma distance_symm (x y : Simplex I) : distance I x y = distance I y x := by
  obtain ⟨a, ha, b, hb, h⟩ := closest_pair I x y
  obtain ⟨c, hc, d, hd, h'⟩ := closest_pair I y x
  have hxy := distance_le I hd hc
  have hyx := distance_le I hb ha
  rw [norm_sub_rev] at hxy hyx
  linarith

lemma distance_mono {x y x' y' : Simplex I}
    (hx : carrier I x' ⊆ carrier I x) (hy : carrier I y' ⊆ carrier I y) :
    distance I x y ≤ distance I x' y' := by
  obtain ⟨a, ha, b, hb, h⟩ := closest_pair I x' y'
  rw [h]
  exact distance_le I (hx ha) (hy hb)

lemma bounded_point (x : Simplex I) {L : ℝ} (h : boundedInput I x L) (j : Fin 3) :
    boundedInput I (.point (vertices I x j)) L := by
  intro _ k
  exact h j k

lemma bounded_edge (x : Triangle I) {L : ℝ} (h : boundedInput I (.triangle x) L)
    (e : Fin 3 × Fin 3) : boundedInput I (.segment (edge I x e)) L := by
  intro j k
  fin_cases j <;> simp only [vertices, edge, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue, Fin.reduceFinMk]
  all_goals apply h

end DistanceAccuracy.Geometry

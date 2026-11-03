import DistanceAccuracy.ThreeDivideGlobalUpperAssembly
import DistanceAccuracy.ThreeDivideEvaluation

/-! Upper-bound assembly for the three-division model. The numerical budgets
are unchanged; the new kernel theorem discharges the same segment envelope. -/
namespace DistanceAccuracy.ThreeDivideGlobalUpperAssembly
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge DistanceAccuracy.Geometry ThreeDivideUpperSelection

lemma finite_of_safe {I : Interchange} [I.Valid] {d B : ℝ} {w : I.Word}
    (h : CandidateLower.Safe I d B w) : ThreeDivideUpperSelection.Finite I w := by
  obtain ⟨q,hq,_⟩ := h
  exact ⟨q,hq⟩

structure SegmentFamilyFinite (I : Interchange) [I.Valid] (x : Segment I) (y : Triangle I) : Prop where
  edges : ∀ e, ThreeDivideUpperSelection.Finite I (ThreeDivideAlgorithm.segmentSegment I x (edge I y e)).q
  faces : ∀ k, ThreeDivideUpperSelection.Finite I (segFace I x y k).q
  crossing : ThreeDivideUpperSelection.Finite I (segCross I x y).q

structure TriangleFamilyFinite (I : Interchange) [I.Valid] (x y : Triangle I) : Prop where
  point : ThreeDivideUpperSelection.Finite I (pointPoint I (x 0) (y 0)).q
  edges : ∀ e f, ThreeDivideUpperSelection.Finite I (ThreeDivideAlgorithm.segmentSegment I (edge I x e) (edge I y f)).q
  facesRight : ∀ k, ThreeDivideUpperSelection.Finite I (triFaceR I x y k).q
  facesLeft : ∀ k, ThreeDivideUpperSelection.Finite I (triFaceL I x y k).q
  crossingRight : ∀ e, ThreeDivideUpperSelection.Finite I (triCrossR I x y e).q
  crossingLeft : ∀ e, ThreeDivideUpperSelection.Finite I (triCrossL I x y e).q

/-- A harmless increase in the scale used for range analysis proves candidate
finiteness even in the smallest-subnormal regime. -/
lemma finite_budget_scale (f : DistanceAccuracy.Format) {L : ℝ} (hL0 : 0≤L)
    (hL : L<fourthRoot f.interchange.format.maxFinite/4) :
    ∃ K : ℝ, L≤K ∧ ThreeDivideEvaluation.Budget f.interchange K := by
  let K := max L (fourthRoot f.leastNormal/64)
  have hK0 : 0≤K := hL0.trans (le_max_left _ _)
  have hKlim : K<fourthRoot f.interchange.format.maxFinite/4 :=
    max_lt hL f.small_scale_admissible
  exact ⟨K,le_max_left _ _,ThreeDivideEvaluation.format_budget f hK0 hKlim (le_max_right _ _)⟩

/-- Every candidate actually participating in triangle-triangle selection has
a finite squared distance, from the original admissibility hypothesis alone. -/
theorem triangle_family_finite (f : DistanceAccuracy.Format) (x y : Triangle f.interchange)
    {L : ℝ} (h : admissible f.interchange (.triangle x) (.triangle y) L) :
    TriangleFamilyFinite f.interchange x y := by
  obtain ⟨K,hLK,budget⟩ := finite_budget_scale f h.1 h.2.1
  have hx := ThreeDivideEvaluation.bounded_mono h.2.2.1 hLK
  have hy := ThreeDivideEvaluation.bounded_mono h.2.2.2 hLK
  let vx := ThreeDivideEvaluation.vertex_of_bounded hx
  let vy := ThreeDivideEvaluation.vertex_of_bounded hy
  let pair : ThreeDivideEvaluation.Pair (carrier f.interchange (.triangle x))
      (carrier f.interchange (.triangle y)) 0 :=
    ⟨carrier_convex _ _,carrier_convex _ _,fun _ _ _ _ => norm_nonneg _⟩
  refine ⟨finite_of_safe (ThreeDivideEvaluation.point budget pair (vx 0) (vy 0)),?_,?_,?_,?_,?_⟩
  · intro e g
    exact finite_of_safe (ThreeDivideEvaluation.segmentSegment budget pair
      (ThreeDivideEvaluation.vertex_edge vx e) (ThreeDivideEvaluation.vertex_edge vy g))
  · intro k
    exact finite_of_safe (ThreeDivideEvaluation.face budget pair (vx k) (vy 0) (vy 1) (vy 2))
  · intro k
    exact finite_of_safe (ThreeDivideEvaluation.face budget pair.swap (vy k) (vx 0) (vx 1) (vx 2))
  · intro e
    exact finite_of_safe (ThreeDivideEvaluation.crossing budget pair (ThreeDivideEvaluation.vertex_edge vx e) (vy 0) (vy 1) (vy 2))
  · intro e
    exact finite_of_safe (ThreeDivideEvaluation.crossing budget pair.swap (ThreeDivideEvaluation.vertex_edge vy e) (vx 0) (vx 1) (vx 2))

theorem segment_family_finite (f : DistanceAccuracy.Format)
    (x : Segment f.interchange) (y : Triangle f.interchange)
    {L : ℝ} (h : admissible f.interchange (.segment x) (.triangle y) L) :
    SegmentFamilyFinite f.interchange x y := by
  obtain ⟨K,hLK,budget⟩ := finite_budget_scale f h.1 h.2.1
  have hx := ThreeDivideEvaluation.bounded_mono h.2.2.1 hLK
  have hy := ThreeDivideEvaluation.bounded_mono h.2.2.2 hLK
  let vx : ∀ k, ThreeDivideEvaluation.Vertex f.interchange (carrier f.interchange (.segment x)) K (x k) := by
    intro k
    refine Fin.cases (motive := fun k => ThreeDivideEvaluation.Vertex f.interchange
      (carrier f.interchange (.segment x)) K (x k)) (ThreeDivideEvaluation.vertex_of_bounded hx 0) ?_ k
    intro j
    have hj : j=0 := Fin.eq_zero j
    subst j
    exact ThreeDivideEvaluation.vertex_of_bounded hx 1
  let vy := ThreeDivideEvaluation.vertex_of_bounded hy
  let pair : ThreeDivideEvaluation.Pair (carrier f.interchange (.segment x))
      (carrier f.interchange (.triangle y)) 0 :=
    ⟨carrier_convex _ _,carrier_convex _ _,fun _ _ _ _ => norm_nonneg _⟩
  refine ⟨?_,?_,?_⟩
  · intro e
    exact finite_of_safe (ThreeDivideEvaluation.segmentSegment budget pair vx (ThreeDivideEvaluation.vertex_edge vy e))
  · intro k
    exact finite_of_safe (ThreeDivideEvaluation.face budget pair (vx k) (vy 0) (vy 1) (vy 2))
  · exact finite_of_safe (ThreeDivideEvaluation.crossing budget pair vx (vy 0) (vy 1) (vy 2))

end DistanceAccuracy.ThreeDivideGlobalUpperAssembly

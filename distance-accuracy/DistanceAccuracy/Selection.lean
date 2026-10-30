import DistanceAccuracy.IEEEAlgorithm

/-! Candidate selection preserves any property of q shared by all candidates.
These lemmas cover the actual nested folds and weight updates in the model. -/
namespace DistanceAccuracy.Selection
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm
variable (I : Interchange) [I.Valid]

omit [I.Valid] in
lemma choose_property {P : I.Word → Prop} {a b : Candidate I}
    (ha : P a.q) (hb : P b.q) : P (choose I a b).q := by
  unfold choose
  split <;> assumption

omit [I.Valid] in
lemma fold_property {α : Type} {P : I.Word → Prop} (l : List α)
    (step : Candidate I → α → Candidate I) (best : Candidate I)
    (hbest : P best.q) (hstep : ∀ best e, P best.q → P (step best e).q) :
    P (l.foldl step best).q := by
  induction l generalizing best with
  | nil => exact hbest
  | cons a l ih => exact ih _ (hstep best a hbest)

lemma segmentTriangle_property {P : I.Word → Prop} (x : Segment I) (y : Triangle I)
    (hss : ∀ e, P (segmentSegment I x (edge I y e)).q)
    (hf : ∀ k, P (face I (vsub I (y 0) (x k))
      (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
      (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))).q)
    (hc : P (crossing I x (y 0) (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
      (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))).q) :
    P (segmentTriangle I x y).q := by
  unfold segmentTriangle
  exact choose_property I (choose_property I (choose_property I
    (choose_property I (choose_property I (hss _) (hss _)) (hss _)) (hf _)) (hf _)) hc

lemma triangleTriangle_property {P : I.Word → Prop} (x y : Triangle I)
    (hpp : P (pointPoint I (x 0) (y 0)).q)
    (hss : ∀ e f, P (segmentSegment I (edge I x e) (edge I y f)).q)
    (hfy : ∀ k, P (face I (vsub I (y 0) (x k))
      (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
      (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))).q)
    (hfx : ∀ k, P (face I (vsub I (x 0) (y k))
      (vsub I (x 1) (x 0)) (vsub I (x 2) (x 0))
      (cross3Accurate I (vsub I (x 1) (x 0)) (vsub I (x 2) (x 0)))).q)
    (hcy : ∀ e, P (crossing I (edge I x e) (y 0) (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
      (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))).q)
    (hcx : ∀ e, P (crossing I (edge I y e) (x 0) (vsub I (x 1) (x 0)) (vsub I (x 2) (x 0))
      (cross3Accurate I (vsub I (x 1) (x 0)) (vsub I (x 2) (x 0)))).q) :
    P (triangleTriangle I x y).q := by
  unfold triangleTriangle
  apply fold_property I
  · apply fold_property I
    · apply fold_property I
      · exact hpp
      · intro best e hbest
        apply fold_property I
        · exact hbest
        · intro best f hbest
          exact choose_property I hbest (hss e f)
    · intro best k hbest
      exact choose_property I (choose_property I hbest (hfy k)) (hfx k)
  · intro best e hbest
    exact choose_property I (choose_property I hbest (hcy e)) (hcx e)

end DistanceAccuracy.Selection

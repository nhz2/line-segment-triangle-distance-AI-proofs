import DistanceAccuracy.OperationBounds
import DistanceAccuracy.Selection

namespace DistanceAccuracy.UpperSelection
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds
variable (I : Interchange) [I.Valid]

def Finite (w : I.Word) : Prop := ∃ q : ℚ, value? I w=some q

def Upper (B : ℝ) (w : I.Word) : Prop := ∃ q : ℚ, value? I w=some q ∧ Real.sqrt (q:ℝ)≤B

lemma Upper.finite {B : ℝ} {w : I.Word} (h : Upper I B w) : Finite I w := by
  obtain ⟨q,hq,_⟩ := h
  exact ⟨q,hq⟩

lemma choose_finite {a b : Candidate I} (ha : Finite I a.q) (hb : Finite I b.q) :
    Finite I (choose I a b).q := by
  obtain ⟨qa,ha⟩ := ha
  obtain ⟨qb,hb⟩ := hb
  exact ⟨min qa qb,choose_value I ha hb⟩

lemma choose_upper_left {a b : Candidate I} {B : ℝ}
    (ha : Upper I B a.q) (hb : Finite I b.q) : Upper I B (choose I a b).q := by
  obtain ⟨qa,ha,haB⟩ := ha
  obtain ⟨qb,hb⟩ := hb
  refine ⟨min qa qb,choose_value I ha hb,?_⟩
  exact (Real.sqrt_le_sqrt (by exact_mod_cast min_le_left qa qb)).trans haB

lemma choose_upper_right {a b : Candidate I} {B : ℝ}
    (ha : Finite I a.q) (hb : Upper I B b.q) : Upper I B (choose I a b).q := by
  obtain ⟨qa,ha⟩ := ha
  obtain ⟨qb,hb,hbB⟩ := hb
  refine ⟨min qa qb,choose_value I ha hb,?_⟩
  exact (Real.sqrt_le_sqrt (by exact_mod_cast min_le_right qa qb)).trans hbB

/-- A candidate selected at any position of an actual fold bounds its final
result. Unlike a shared-property argument, only one candidate needs an upper
bound; all other candidates need finiteness. -/
theorem fold_upper_member {α : Type} (l : List α) (step : Candidate I → α → Candidate I)
    (best : Candidate I) {a : α} {B : ℝ} (ha : a ∈ l)
    (hbest : Finite I best.q)
    (hfinite : ∀ c e, Finite I c.q → Finite I (step c e).q)
    (hkeep : ∀ c e, Upper I B c.q → Upper I B (step c e).q)
    (hhit : ∀ c, Finite I c.q → Upper I B (step c a).q) :
    Upper I B (l.foldl step best).q := by
  induction l generalizing best with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Selection.fold_property I l step (step best a) (hhit best hbest) hkeep
    · exact ih (step best b) ha (hfinite best b hbest)

/-- Point-triangle selection from any one of its three actual candidates. -/
theorem choose_three_upper {a b c : Candidate I} {B : ℝ}
    (ha : Finite I a.q) (hb : Finite I b.q) (hc : Finite I c.q)
    (h : Upper I B a.q ∨ Upper I B b.q ∨ Upper I B c.q) :
    Upper I B (choose I (choose I a b) c).q := by
  rcases h with h | h | h
  · exact choose_upper_left I (choose_upper_left I h hb) hc
  · exact choose_upper_left I (choose_upper_right I ha h) hc
  · exact choose_upper_right I (choose_finite I ha hb) h

/-- The six-candidate segment-triangle minimum is bounded by any member. -/
theorem segmentTriangle_upper (x : Segment I) (y : Triangle I) {B : ℝ}
    (hss : ∀ e, Finite I (segmentSegment I x (edge I y e)).q)
    (hf : ∀ k, Finite I (face I (vsub I (y 0) (x k))
      (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
      (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))).q)
    (hc : Finite I (crossing I x (y 0) (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
      (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))).q)
    (h : (∃ e ∈ edges, Upper I B (segmentSegment I x (edge I y e)).q) ∨
      (∃ k, Upper I B (face I (vsub I (y 0) (x k))
        (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
        (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))).q) ∨
      Upper I B (crossing I x (y 0) (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
        (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))).q) :
    Upper I B (segmentTriangle I x y).q := by
  unfold segmentTriangle
  rcases h with ⟨e,he,hu⟩ | ⟨k,hu⟩ | hu
  · have hu' : Upper I B (segmentSegment I x (edge I y (0,1))).q ∨
        Upper I B (segmentSegment I x (edge I y (0,2))).q ∨
        Upper I B (segmentSegment I x (edge I y (1,2))).q := by
      simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl | rfl
      · exact Or.inl hu
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr hu)
    exact choose_upper_left I (choose_upper_left I (choose_upper_left I
      (choose_three_upper I (hss _) (hss _) (hss _) hu') (hf _)) (hf _)) hc
  · fin_cases k
    · exact choose_upper_left I (choose_upper_left I (choose_upper_right I
        (choose_finite I (choose_finite I (hss _) (hss _)) (hss _)) hu) (hf _)) hc
    · exact choose_upper_left I (choose_upper_right I (choose_finite I
        (choose_finite I (choose_finite I (hss _) (hss _)) (hss _)) (hf _)) hu) hc
  · exact choose_upper_right I (choose_finite I (choose_finite I
      (choose_finite I (choose_finite I (hss _) (hss _)) (hss _)) (hf _)) (hf _)) hu

def triFaceR (x y : Triangle I) (k : Fin 3) : Candidate I :=
  face I (vsub I (y 0) (x k)) (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
    (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))
def triFaceL (x y : Triangle I) (k : Fin 3) : Candidate I := triFaceR I y x k
def triCrossR (x y : Triangle I) (e : Fin 3 × Fin 3) : Candidate I :=
  crossing I (edge I x e) (y 0) (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
    (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))
def triCrossL (x y : Triangle I) (e : Fin 3 × Fin 3) : Candidate I := triCrossR I y x e

/-- The exact triangle-triangle folds select a squared distance no larger than
any one included candidate. All weight remappings and reversals are retained. -/
theorem triangleTriangle_upper (x y : Triangle I) {B : ℝ}
    (hpp : Finite I (pointPoint I (x 0) (y 0)).q)
    (hss : ∀ e f, Finite I (segmentSegment I (edge I x e) (edge I y f)).q)
    (hfr : ∀ k, Finite I (triFaceR I x y k).q)
    (hfl : ∀ k, Finite I (triFaceL I x y k).q)
    (hcr : ∀ e, Finite I (triCrossR I x y e).q)
    (hcl : ∀ e, Finite I (triCrossL I x y e).q)
    (h : Upper I B (pointPoint I (x 0) (y 0)).q ∨
      (∃ e ∈ edges, ∃ f ∈ edges, Upper I B (segmentSegment I (edge I x e) (edge I y f)).q) ∨
      (∃ k, Upper I B (triFaceR I x y k).q) ∨
      (∃ k, Upper I B (triFaceL I x y k).q) ∨
      (∃ e ∈ edges, Upper I B (triCrossR I x y e).q) ∨
      (∃ e ∈ edges, Upper I B (triCrossL I x y e).q)) :
    Upper I B (triangleTriangle I x y).q := by
  let ss (c : Candidate I) (e f : Fin 3 × Fin 3) : Candidate I :=
    let q := segmentSegment I (edge I x e) (edge I y f)
    choose I c {q with left:=edgeWeights I e.1 e.2 (q.left 0),right:=edgeWeights I f.1 f.2 (q.right 0)}
  let se (c : Candidate I) (e : Fin 3 × Fin 3) := edges.foldl (fun c f => ss c e f) c
  let sf (c : Candidate I) (k : Fin 3) : Candidate I :=
    let a := triFaceR I x y k
    let b := reverse I (triFaceL I x y k)
    choose I (choose I c {a with left:=edgeWeights I k k (zero I)})
      {b with right:=edgeWeights I k k (zero I)}
  let sc (c : Candidate I) (e : Fin 3 × Fin 3) : Candidate I :=
    let a := triCrossR I x y e
    let b := reverse I (triCrossL I x y e)
    choose I (choose I c {a with left:=edgeWeights I e.1 e.2 (a.left 0)})
      {b with right:=edgeWeights I e.1 e.2 (b.right 0)}
  let pp := pointPoint I (x 0) (y 0)
  let edgeBest := edges.foldl se pp
  let faceBest := ([0,1,2]:List (Fin 3)).foldl sf edgeBest
  change Upper I B (edges.foldl sc faceBest).q
  have hssfin (e : Fin 3 × Fin 3) (c : Candidate I) (f : Fin 3 × Fin 3) :
      Finite I c.q → Finite I (ss c e f).q := fun hc => choose_finite I hc (hss e f)
  have hsskeep (e : Fin 3 × Fin 3) (c : Candidate I) (f : Fin 3 × Fin 3) :
      Upper I B c.q → Upper I B (ss c e f).q := fun hc => choose_upper_left I hc (hss e f)
  have hsefin (c : Candidate I) (e : Fin 3 × Fin 3) (hc : Finite I c.q) : Finite I (se c e).q :=
    Selection.fold_property I edges (fun c f => ss c e f) c hc (hssfin e)
  have hsekeep (c : Candidate I) (e : Fin 3 × Fin 3) (hc : Upper I B c.q) : Upper I B (se c e).q :=
    Selection.fold_property I edges (fun c f => ss c e f) c hc (hsskeep e)
  have hsffin (c : Candidate I) (k : Fin 3) (hc : Finite I c.q) : Finite I (sf c k).q :=
    choose_finite I (choose_finite I hc (hfr k)) (hfl k)
  have hsfkeep (c : Candidate I) (k : Fin 3) (hc : Upper I B c.q) : Upper I B (sf c k).q :=
    choose_upper_left I (choose_upper_left I hc (hfr k)) (hfl k)
  have hscfin (c : Candidate I) (e : Fin 3 × Fin 3) (hc : Finite I c.q) : Finite I (sc c e).q :=
    choose_finite I (choose_finite I hc (hcr e)) (hcl e)
  have hsckeep (c : Candidate I) (e : Fin 3 × Fin 3) (hc : Upper I B c.q) : Upper I B (sc c e).q :=
    choose_upper_left I (choose_upper_left I hc (hcr e)) (hcl e)
  have hefin : Finite I edgeBest.q := Selection.fold_property I edges se pp hpp hsefin
  have hffin : Finite I faceBest.q := Selection.fold_property I _ sf edgeBest hefin hsffin
  have face_of_edge (he : Upper I B edgeBest.q) : Upper I B faceBest.q :=
    Selection.fold_property I _ sf edgeBest he hsfkeep
  have final_of_face (hf : Upper I B faceBest.q) : Upper I B (edges.foldl sc faceBest).q :=
    Selection.fold_property I _ sc faceBest hf hsckeep
  have hk (k : Fin 3) : k ∈ ([0,1,2]:List (Fin 3)) := by fin_cases k <;> decide
  rcases h with h | ⟨e,he,f,hf,h⟩ | ⟨k,h⟩ | ⟨k,h⟩ | ⟨e,he,h⟩ | ⟨e,he,h⟩
  · exact final_of_face (face_of_edge (Selection.fold_property I edges se pp h hsekeep))
  · apply final_of_face; apply face_of_edge
    apply fold_upper_member I edges se pp he hpp hsefin hsekeep
    intro c hc
    exact fold_upper_member I edges (fun c f => ss c e f) c hf hc (hssfin e) (hsskeep e)
      (fun c hc => choose_upper_right I hc h)
  · apply final_of_face
    apply fold_upper_member I _ sf edgeBest (hk k) hefin hsffin hsfkeep
    intro c hc
    exact choose_upper_left I (choose_upper_right I hc h) (hfl k)
  · apply final_of_face
    apply fold_upper_member I _ sf edgeBest (hk k) hefin hsffin hsfkeep
    intro c hc
    exact choose_upper_right I (choose_finite I hc (hfr k)) h
  · apply fold_upper_member I edges sc faceBest he hffin hscfin hsckeep
    intro c hc
    exact choose_upper_left I (choose_upper_right I hc h) (hcl e)
  · apply fold_upper_member I edges sc faceBest he hffin hscfin hsckeep
    intro c hc
    exact choose_upper_right I (choose_finite I hc (hcr e)) h

end DistanceAccuracy.UpperSelection

import DistanceAccuracy.SegmentUpper
import DistanceAccuracy.TriangleCarrier
namespace DistanceAccuracy.BoundaryEdgeUpper
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Geometry
open DistanceAccuracy.Determinant ProjectionRounding UpperSelection
set_option maxHeartbeats 1500000

lemma vertex_difference (I : Interchange) [I.Valid] {L : ℝ} {a b : Vec3 I}
    {S T : Set Geometry.E3} (A : EvaluateLower.Vertex I S L a)
    (B : EvaluateLower.Vertex I T L b) (budget : EvaluateLower.Budget I L) :
    ‖decodeVec I (vsub I a b)-(decodeVec I a-decodeVec I b)‖ ≤
      I.format.unitRoundoff*((7/2)*L) := by
  obtain ⟨r,hr,_⟩ := FaceCoordinates.difference_data I B.decode A.decode budget.nonneg
    B.bound A.bound budget.rho budget.eta budget.linear
  have he := WordGeometryTransfer.difference_error I A.decode B.decode hr budget.nonneg
    A.bound B.bound budget.rho budget.eta budget.linear
  have conv {w : Vec3 I} {v : Fin 3 → ℚ} (hv : ∀ i, value? I (w i) = some (v i)) :
      realVec v = decodeVec I w := by
    ext i; simp [realVec, decodeVec, real_decode I (hv i)]
  simpa only [conv hr,conv A.decode,conv B.decode] using he

lemma boundary_parameter (I : Interchange) (y : Triangle I) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v ≤ 1)
    (hb : u=0 ∨ v=0 ∨ u+v=1) :
    ∃ e ∈ edges, ∃ t ∈ Set.Icc (0:ℝ) 1,
      decodeVec I (y 0)+u•(decodeVec I (y 1)-decodeVec I (y 0))+
        v•(decodeVec I (y 2)-decodeVec I (y 0)) =
      decodeVec I (y e.1)+t•(decodeVec I (y e.2)-decodeVec I (y e.1)) := by
  rcases hb with rfl | rfl | hab
  · refine ⟨(0,2),by simp [edges],v,⟨hv,by linarith⟩,?_⟩; simp
  · refine ⟨(0,1),by simp [edges],u,⟨hu,by linarith⟩,?_⟩; simp
  · refine ⟨(1,2),by simp [edges],v,⟨hv,by linarith⟩,?_⟩
    have hu' : u=1-v := by linarith
    rw [hu']; module

lemma affine_triangle_error {R E F R₀ E₀ F₀ : Geometry.E3} {u v S : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v ≤ 1) (hS : 0 ≤ S)
    (hR : ‖R-R₀‖ ≤ S) (hE : ‖E-E₀‖ ≤ S) (hF : ‖F-F₀‖ ≤ S) :
    ‖(R+u•E+v•F)-(R₀+u•E₀+v•F₀)‖ ≤ 2*S := by
  have hid : (R+u•E+v•F)-(R₀+u•E₀+v•F₀) = (R-R₀)+u•(E-E₀)+v•(F-F₀) := by module
  rw [hid]
  have h1 := norm_add_le (R-R₀) (u•(E-E₀))
  have h2 := norm_add_le ((R-R₀)+u•(E-E₀)) (v•(F-F₀))
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hu] at h1
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hv] at h2
  nlinarith [mul_le_mul_of_nonneg_left hE hu, mul_le_mul_of_nonneg_left hF hv,
    mul_le_mul_of_nonneg_right huv hS]

/-- A boundary witness transfers to either ordering of the actual segment/edge
    pair. The common segment-direction subtraction cancels, so the loss is 4ρD. -/
theorem boundary_data (fmt : DistanceAccuracy.Format)
    {x : Segment fmt.interchange} {y : Triangle fmt.interchange} {L s u v B : ℝ}
    (hadm : Geometry.admissible fmt.interchange (.segment x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v ≤ 1)
    (hb : u=0 ∨ v=0 ∨ u+v=1)
    (hw : ‖decodeVec fmt.interchange (vsub fmt.interchange (y 0) (x 0))+
      u•decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0))+
      v•decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0))-
      s•decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0))‖ ≤ B) :
    ∃ e ∈ edges, ∃ t ∈ Set.Icc (0:ℝ) 1,
      ‖decodeVec fmt.interchange (vsub fmt.interchange (y e.1) (x 0))+
        t•decodeVec fmt.interchange (vsub fmt.interchange (y e.2) (y e.1))-
        s•decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0))‖ ≤ B+4*fmt.rho*((7/2)*L) ∧
      ‖decodeVec fmt.interchange (vsub fmt.interchange (x 0) (y e.1))+
        s•decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0))-
        t•decodeVec fmt.interchange (vsub fmt.interchange (y e.2) (y e.1))‖ ≤ B+4*fmt.rho*((7/2)*L) := by
  let I := fmt.interchange
  let X0 := EvaluateLower.vertex_of_bounded hadm.2.2.1 0
  let Y := fun j => EvaluateLower.vertex_of_bounded hadm.2.2.2 j
  have budget := EvaluateLower.format_budget fmt hadm.1 hadm.2.1 hlarge
  have hrho : I.format.unitRoundoff = fmt.rho := by
    cases fmt with
    | binary32 => exact fp32_parameters.1
    | binary64 => exact fp64_parameters.1
  have hdiff (i j : Fin 3) := vertex_difference I (Y i) (Y j) budget
  have hbase (i : Fin 3) := vertex_difference I (Y i) X0 budget
  have hrev (i : Fin 3) := vertex_difference I X0 (Y i) budget
  simp only [hrho, vertices, Matrix.cons_val_zero] at hdiff hbase hrev
  obtain ⟨e,he,t,ht,heq⟩ := boundary_parameter I y hu hv huv hb
  refine ⟨e,he,t,ht,?_⟩
  let S := fmt.rho*((7/2)*L)
  have hS : 0 ≤ S := by dsimp [S]; exact mul_nonneg fmt.rho_nonneg (by linarith [hadm.1])
  let R := decodeVec I (vsub I (y 0) (x 0))
  let E := decodeVec I (vsub I (y 1) (y 0))
  let F := decodeVec I (vsub I (y 2) (y 0))
  let P := decodeVec I (vsub I (x 1) (x 0))
  let W := R+u•E+v•F
  let W₀ := decodeVec I (y 0)-decodeVec I (x 0)+u•(decodeVec I (y 1)-decodeVec I (y 0))+
    v•(decodeVec I (y 2)-decodeVec I (y 0))
  have hW : ‖W-W₀‖ ≤ 2*S := affine_triangle_error hu hv huv hS (hbase 0) (hdiff 1 0) (hdiff 2 0)
  let Q := decodeVec I (vsub I (y e.2) (y e.1))
  let V := decodeVec I (vsub I (y e.1) (x 0))+t•Q
  let V' := decodeVec I (vsub I (x 0) (y e.1))-t•Q
  have heq' : W₀ = decodeVec I (y e.1)-decodeVec I (x 0)+t•(decodeVec I (y e.2)-decodeVec I (y e.1)) := by
    dsimp [W₀]
    have h := congrArg (fun z => z-decodeVec I (x 0)) heq
    convert h using 1 <;> module
  have hV : ‖V-W₀‖ ≤ 2*S := by
    rw [heq']
    simpa [V,Q] using affine_triangle_error ht.1 (le_refl (0:ℝ)) (by linarith [ht.2]) hS
      (hbase e.1) (hdiff e.2 e.1) (hdiff e.2 e.1) (v:=0)
  have hV' : ‖V'+W₀‖ ≤ 2*S := by
    rw [heq']
    have he' : ‖(-Q)-(-(decodeVec I (y e.2)-decodeVec I (y e.1)))‖ ≤ S := by
      simpa only [Q, neg_sub_neg,norm_sub_rev] using hdiff e.2 e.1
    have hh := affine_triangle_error ht.1 (le_refl (0:ℝ)) (by linarith [ht.2]) hS
      (hrev e.1) he' he' (v:=0)
    convert hh using 1
    congr 1
    dsimp [V']
    module
  constructor
  · have hid : V-s•P = (V-W₀)+(W₀-W)+(W-s•P) := by module
    have h1 := norm_add_le (V-W₀) (W₀-W)
    rw [norm_sub_rev W₀ W] at h1
    have h2 := norm_add_le ((V-W₀)+(W₀-W)) (W-s•P)
    rw [←hid] at h2
    change ‖V-s•P‖ ≤ B+4*fmt.rho*((7/2)*L)
    change ‖W-s•P‖ ≤ B at hw
    dsimp [S] at hW hV
    linarith
  · have hid : V'+s•P = (V'+W₀)+(W-W₀)-(W-s•P) := by module
    have h1 := norm_add_le (V'+W₀) (W-W₀)
    have h2 := norm_sub_le ((V'+W₀)+(W-W₀)) (W-s•P)
    rw [←hid] at h2
    have hid' : decodeVec I (vsub I (x 0) (y e.1))+s•P-t•Q = V'+s•P := by dsimp [V']; module
    change ‖decodeVec I (vsub I (x 0) (y e.1))+s•P-t•Q‖ ≤ _
    rw [hid']
    change ‖W-s•P‖ ≤ B at hw
    dsimp [S] at hW hV'
    linarith

/-- Both orientations of the actual boundary edge candidate satisfy the same
sharp segment envelope. -/
theorem boundary_upper (fmt : DistanceAccuracy.Format)
    {x : Segment fmt.interchange} {y : Triangle fmt.interchange} {L s u v B : ℝ}
    (hadm : Geometry.admissible fmt.interchange (.segment x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L)
    (hs : s ∈ Set.Icc (0:ℝ) 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v ≤ 1)
    (hb : u=0 ∨ v=0 ∨ u+v=1)
    (hw : ‖decodeVec fmt.interchange (vsub fmt.interchange (y 0) (x 0))+
      u•decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0))+
      v•decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0))-
      s•decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0))‖ ≤ B) :
    ∃ e ∈ edges,
      let bound := fmt.rho*((7/2)*L)*F ((B+4*fmt.rho*((7/2)*L))/(fmt.rho*((7/2)*L)))+
        3.55*fmt.rho*((7/2)*L)+6*fourthRoot fmt.leastSubnormal
      Upper fmt.interchange bound (segmentSegment fmt.interchange x (edge fmt.interchange y e)).q ∧
      Upper fmt.interchange bound (segmentSegment fmt.interchange (edge fmt.interchange y e) x).q := by
  obtain ⟨e,he,t,ht,hf,hr⟩ := boundary_data fmt hadm hlarge hu hv huv hb hw
  have hB : 0 ≤ B := (norm_nonneg _).trans hw
  have hD : 0 ≤ B+4*fmt.rho*((7/2)*L) := by
    have := fmt.rho_nonneg
    have := hadm.1
    positivity
  have heBound := Geometry.bounded_edge fmt.interchange y hadm.2.2.2 e
  have hadmF : Geometry.admissible fmt.interchange (.segment x)
      (.segment (edge fmt.interchange y e)) L := ⟨hadm.1,hadm.2.1,hadm.2.2.1,heBound⟩
  have hadmR : Geometry.admissible fmt.interchange (.segment (edge fmt.interchange y e))
      (.segment x) L := ⟨hadm.1,hadm.2.1,heBound,hadm.2.2.1⟩
  refine ⟨e,he,?_,?_⟩
  · apply SegmentUpper.common_witness fmt hadmF hlarge hs ht hD
    simpa only [edge, Matrix.cons_val_zero, Matrix.cons_val_one] using hf
  · apply SegmentUpper.common_witness fmt hadmR hlarge ht hs hD
    simpa only [edge, Matrix.cons_val_zero, Matrix.cons_val_one] using hr
end DistanceAccuracy.BoundaryEdgeUpper

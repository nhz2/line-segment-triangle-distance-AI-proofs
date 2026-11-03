import DistanceAccuracy.IEEEAlgorithm

/-! IEEE-word transcription of the three-division checkout. The old model and
its proven accuracy theorem are deliberately retained under IEEEAlgorithm.
Source: an uncommitted ../SimplexCellLists.jl/src/distances.jl based on commit
7c12846, SHA256 7f2278c09656a309a70e5c2fa9d5882d42b521cc718c93bda9dedf6cd3529e6b.
It was never merged; commit 287e746 uses InvMultiplyAlgorithm's reciprocals.
The higher kernels below call this namespace's replacement segment kernel. -/
namespace DistanceAccuracy.ThreeDivideAlgorithm
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm
variable (I : Interchange) [I.Valid]

def segmentSegment (x y : Segment I) : Candidate I :=
  let P := vsub I (x 1) (x 0)
  let Q := vsub I (y 1) (y 0)
  let R := vsub I (y 0) (x 0)
  let b := dot3 I P Q
  let c := dot3 I Q Q
  let e := dot3 I Q R
  let n := cross3 I P Q
  let t := clamp01nan I (div I (neg I (dot3 I n (cross3 I P R))) (dot3 I n n))
  let s := clamp01nan I (div I (fma I t b (dot3 I P R)) (dot3 I P P))
  let t := clamp01nan I (div I (fma I s b (neg I e)) c)
  make I (fma3 I (neg I s) P (fma3 I t Q R))
    (weights I s (zero I)) (weights I t (zero I))

def segmentTriangle (x : Segment I) (y : Triangle I) : Candidate I :=
  let A := y 0
  let E0 := vsub I (y 1) A
  let E1 := vsub I (y 2) A
  let N := cross3Accurate I E0 E1
  let ab := segmentSegment I x (edge I y (0, 1))
  let ac := segmentSegment I x (edge I y (0, 2))
  let bc := segmentSegment I x (edge I y (1, 2))
  let best := choose I ab { ac with right := weights I (zero I) (ac.right 0) }
  let best := choose I best { bc with right := weights I (sub I (one I) (bc.right 0)) (bc.right 0) }
  let best := choose I best (face I (vsub I A (x 0)) E0 E1 N)
  let end1 := face I (vsub I A (x 1)) E0 E1 N
  let best := choose I best { end1 with left := weights I (one I) (zero I) }
  choose I best (crossing I x A E0 E1 N)

def triangleTriangle (x y : Triangle I) : Candidate I :=
  let Ax := x 0
  let E0x := vsub I (x 1) Ax
  let E1x := vsub I (x 2) Ax
  let Nx := cross3Accurate I E0x E1x
  let Ay := y 0
  let E0y := vsub I (y 1) Ay
  let E1y := vsub I (y 2) Ay
  let Ny := cross3Accurate I E0y E1y
  let best := pointPoint I Ax Ay
  let best := edges.foldl (fun best e => edges.foldl (fun best f =>
    let c := segmentSegment I (edge I x e) (edge I y f)
    choose I best { c with left := edgeWeights I e.1 e.2 (c.left 0), right := edgeWeights I f.1 f.2 (c.right 0) }) best) best
  let best := ([0, 1, 2] : List (Fin 3)).foldl (fun best k =>
    let c := face I (vsub I Ay (x k)) E0y E1y Ny
    let best := choose I best { c with left := edgeWeights I k k (zero I) }
    let c := reverse I (face I (vsub I Ax (y k)) E0x E1x Nx)
    choose I best { c with right := edgeWeights I k k (zero I) }) best
  edges.foldl (fun best e =>
    let c := crossing I (edge I x e) Ay E0y E1y Ny
    let best := choose I best { c with left := edgeWeights I e.1 e.2 (c.left 0) }
    let c := reverse I (crossing I (edge I y e) Ax E0x E1x Nx)
    choose I best { c with right := edgeWeights I e.1 e.2 (c.right 0) }) best

def evaluate : Simplex I → Simplex I → Candidate I
  | .point x, .point y => pointPoint I x y
  | .point x, .segment y => pointSegment I x y
  | .point x, .triangle y => pointTriangle I x y
  | .segment x, .point y => reverse I (pointSegment I y x)
  | .segment x, .segment y => segmentSegment I x y
  | .segment x, .triangle y => segmentTriangle I x y
  | .triangle x, .point y => reverse I (pointTriangle I y x)
  | .triangle x, .segment y => reverse I (segmentTriangle I y x)
  | .triangle x, .triangle y => triangleTriangle I x y

end DistanceAccuracy.ThreeDivideAlgorithm

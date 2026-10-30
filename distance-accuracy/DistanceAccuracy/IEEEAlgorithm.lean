import FP.IEEE.Software.FMA
import FP.IEEE.Software.Division
import FP.IEEE.Software.Comparison
import FP.IEEE.Software.Sign

/-!
# The distance algorithm over explicit IEEE encodings

This is a value-level transcription of `src/distances.jl` and `src/util.jl`.
Every arithmetic node uses the pinned FP library's executable IEEE operation
with round-to-nearest/ties-to-even. Division by zero, NaNs, infinities, signed
zeros, and underflow are retained. Exception flags are discarded because the
source does not inspect them. Weights are padded to two entries for all shapes.

Definitions are not an accuracy proof. The mathematical error analysis must be
connected to these operations; see `README.md` for the current status.
-/
namespace DistanceAccuracy.IEEEAlgorithm
open FP.IEEE
open FP.IEEE.Interchange

variable (I : Interchange) [I.Valid]

abbrev Vec3 := Fin 3 → I.Word
abbrev Segment := Fin 2 → Vec3 I
abbrev Triangle := Fin 3 → Vec3 I
abbrev Weights := Fin 2 → I.Word

def zero : I.Word := (Datum.zero (I := I) false).encode
def one : I.Word := (Software.roundWithMode I .nearestEven 1 false).value
def add (a b : I.Word) : I.Word := (Software.add I .nearestEven a b).value
def sub (a b : I.Word) : I.Word := (Software.sub I .nearestEven a b).value
def mul (a b : I.Word) : I.Word := (Software.mul I .nearestEven a b).value
def div (a b : I.Word) : I.Word := (Software.div I .nearestEven a b).value
def neg (a : I.Word) : I.Word := (Software.negate I a).value
def fma (a b c : I.Word) : I.Word := (Software.fma I .nearestEven a b c).value
def lt (a b : I.Word) : Bool := (Software.compare I I .quiet .lt a b).value
def gt (a b : I.Word) : Bool := (Software.compare I I .quiet .gt a b).value

def clamp01nan (x : I.Word) : I.Word :=
  let y := if gt I x (zero I) then x else zero I
  if lt I y (one I) then y else one I

def vsub (a b : Vec3 I) : Vec3 I := fun k => sub I (a k) (b k)
def vadd (a b : Vec3 I) : Vec3 I := fun k => add I (a k) (b k)
def vneg (a : Vec3 I) : Vec3 I := fun k => neg I (a k)
def fma3 (t : I.Word) (a b : Vec3 I) : Vec3 I := fun k => fma I t (a k) (b k)

def dot3 (a b : Vec3 I) : I.Word :=
  fma I (a 2) (b 2) (fma I (a 1) (b 1) (mul I (a 0) (b 0)))

def cross3 (a b : Vec3 I) : Vec3 I :=
  ![fma I (a 1) (b 2) (neg I (mul I (a 2) (b 1))),
    fma I (a 2) (b 0) (neg I (mul I (a 0) (b 2))),
    fma I (a 0) (b 1) (neg I (mul I (a 1) (b 0)))]

def det2 (p q u v : I.Word) : I.Word :=
  let uv := mul I u v
  add I (fma I p q (neg I uv)) (fma I (neg I u) v uv)

def cross3Accurate (a b : Vec3 I) : Vec3 I :=
  ![det2 I (a 1) (b 2) (a 2) (b 1),
    det2 I (a 2) (b 0) (a 0) (b 2),
    det2 I (a 0) (b 1) (a 1) (b 0)]

structure Candidate where
  q : I.Word
  r : Vec3 I
  left : Weights I
  right : Weights I

def weights (u v : I.Word) : Weights I := ![u, v]
def emptyWeights : Weights I := weights I (zero I) (zero I)

def make (r : Vec3 I) (s t : Weights I) : Candidate I := ⟨dot3 I r r, r, s, t⟩

def choose (best cand : Candidate I) : Candidate I :=
  if lt I cand.q best.q || Software.isNaN I cand.q then cand else best

def reverse (c : Candidate I) : Candidate I :=
  ⟨c.q, vneg I c.r, c.right, c.left⟩

def pointPoint (x y : Vec3 I) : Candidate I :=
  make I (vsub I y x) (emptyWeights I) (emptyWeights I)

def pointSegment (x : Vec3 I) (y : Segment I) : Candidate I :=
  let r := vsub I (y 1) (y 0)
  let p := vsub I (y 0) x
  let t := clamp01nan I (div I (neg I (dot3 I p r)) (dot3 I r r))
  make I (fma3 I t r p) (emptyWeights I) (weights I t (zero I))

def face (AX E0 E1 N : Vec3 I) : Candidate I :=
  let ia := div I (one I) (dot3 I E0 E0)
  let c1 := mul I (dot3 I E0 E1) ia
  let v := clamp01nan I (div I (neg I (dot3 I N (cross3 I E0 AX))) (dot3 I N N))
  let u := clamp01nan I (fma I (neg I v) c1 (mul I (neg I (dot3 I E0 AX)) ia))
  let w := sub I (one I) u
  let v := if lt I v w then v else w
  make I (fma3 I v E1 (fma3 I u E0 AX)) (emptyWeights I) (weights I u v)

def pointTriangle (x : Vec3 I) (y : Triangle I) : Candidate I :=
  let A := y 0
  let E0 := vsub I (y 1) A
  let E1 := vsub I (y 2) A
  let AX := vsub I A x
  let inside := face I AX E0 E1 (cross3 I E0 E1)
  let u1 := clamp01nan I (div I (neg I (dot3 I E1 AX)) (dot3 I E1 E1))
  let best := make I (fma3 I u1 E1 AX) (emptyWeights I) (weights I (zero I) u1)
  let E2 := vsub I E1 E0
  let BX := vadd I AX E0
  let u2 := clamp01nan I (div I (neg I (dot3 I BX E2)) (dot3 I E2 E2))
  let bc := make I (fma3 I u2 E2 BX) (emptyWeights I) (weights I (sub I (one I) u2) u2)
  choose I (choose I best bc) inside

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
  let inside := make I (fma3 I (neg I s) P (fma3 I t Q R))
    (weights I s (zero I)) (weights I t (zero I))
  let t0 := clamp01nan I (div I (neg I e) c)
  let best := make I (fma3 I t0 Q R) (emptyWeights I) (weights I t0 (zero I))
  let t1 := clamp01nan I (div I (sub I b e) c)
  let end1 := make I (fma3 I t1 Q (vsub I R P))
    (weights I (one I) (zero I)) (weights I t1 (zero I))
  choose I (choose I best end1) inside

def crossing (x : Segment I) (A E0 E1 N : Vec3 I) : Candidate I :=
  let P := vsub I (x 1) (x 0)
  let AP := vsub I A (x 0)
  let s := clamp01nan I (div I (dot3 I N AP) (dot3 I N P))
  let c := face I (fma3 I (neg I s) P AP) E0 E1 N
  { c with left := weights I s (zero I) }

def edgeWeights (i j : Fin 3) (w : I.Word) : Weights I :=
  let wi := sub I (one I) w
  weights I (if i = 1 then wi else if j = 1 then w else zero I)
    (if i = 2 then wi else if j = 2 then w else zero I)

def edges : List (Fin 3 × Fin 3) := [(0, 1), (0, 2), (1, 2)]
def edge (x : Triangle I) (e : Fin 3 × Fin 3) : Segment I := ![x e.1, x e.2]

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

inductive Simplex where
  | point : Vec3 I → Simplex
  | segment : Segment I → Simplex
  | triangle : Triangle I → Simplex

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

end DistanceAccuracy.IEEEAlgorithm

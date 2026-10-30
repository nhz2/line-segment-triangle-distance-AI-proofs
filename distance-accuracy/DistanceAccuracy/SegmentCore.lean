import DistanceAccuracy.UpperSelection

namespace DistanceAccuracy.SegmentCore
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm
variable (I : Interchange) [I.Valid]

def parameter (P Q R : Vec3 I) : I.Word :=
  let n := cross3 I P Q
  clamp01nan I (IEEEAlgorithm.div I (neg I (dot3 I n (cross3 I P R))) (dot3 I n n))

def inside (P Q R : Vec3 I) : Candidate I :=
  let t := parameter I P Q R
  let s := clamp01nan I (IEEEAlgorithm.div I (fma I t (dot3 I P Q) (dot3 I P R)) (dot3 I P P))
  make I (fma3 I (neg I s) P (fma3 I t Q R)) (weights I s (zero I)) (weights I t (zero I))

def endpoint0 (P Q R : Vec3 I) : Candidate I :=
  let t := clamp01nan I (IEEEAlgorithm.div I (neg I (dot3 I Q R)) (dot3 I Q Q))
  make I (fma3 I t Q R) (emptyWeights I) (weights I t (zero I))

def endpoint1 (P Q R : Vec3 I) : Candidate I :=
  let t := clamp01nan I (IEEEAlgorithm.div I (sub I (dot3 I P Q) (dot3 I Q R)) (dot3 I Q Q))
  make I (fma3 I t Q (vsub I R P)) (weights I (one I) (zero I)) (weights I t (zero I))

def core (P Q R : Vec3 I) : Candidate I :=
  choose I (choose I (endpoint0 I P Q R) (endpoint1 I P Q R)) (inside I P Q R)

lemma segmentSegment_eq (x y : Segment I) : segmentSegment I x y =
    core I (vsub I (x 1) (x 0)) (vsub I (y 1) (y 0)) (vsub I (y 0) (x 0)) := rfl

lemma upper {P Q R : Vec3 I} {B : ℝ}
    (h0 : UpperSelection.Finite I (endpoint0 I P Q R).q)
    (h1 : UpperSelection.Finite I (endpoint1 I P Q R).q)
    (hi : UpperSelection.Finite I (inside I P Q R).q)
    (h : UpperSelection.Upper I B (endpoint0 I P Q R).q ∨
      UpperSelection.Upper I B (endpoint1 I P Q R).q ∨ UpperSelection.Upper I B (inside I P Q R).q) :
    UpperSelection.Upper I B (core I P Q R).q := UpperSelection.choose_three_upper I h0 h1 hi h

end DistanceAccuracy.SegmentCore

import DistanceAccuracy.ThreeDivideAlgorithm
import DistanceAccuracy.SegmentCore
namespace DistanceAccuracy.ThreeDivideCore
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm
variable (I : Interchange) [I.Valid]
def initial (P Q R : Vec3 I) : I.Word := SegmentCore.parameter I P Q R
def second (P Q R : Vec3 I) : I.Word :=
  clamp01nan I (div I (fma I (initial I P Q R) (dot3 I P Q) (dot3 I P R)) (dot3 I P P))
def third (P Q R : Vec3 I) : I.Word :=
  clamp01nan I (div I (fma I (second I P Q R) (dot3 I P Q) (neg I (dot3 I Q R))) (dot3 I Q Q))
def core (P Q R : Vec3 I) : Candidate I :=
  make I (fma3 I (neg I (second I P Q R)) P (fma3 I (third I P Q R) Q R))
    (weights I (second I P Q R) (zero I)) (weights I (third I P Q R) (zero I))
lemma segmentSegment_eq (x y : Segment I) : ThreeDivideAlgorithm.segmentSegment I x y =
    core I (vsub I (x 1) (x 0)) (vsub I (y 1) (y 0)) (vsub I (y 0) (x 0)) := rfl
end DistanceAccuracy.ThreeDivideCore

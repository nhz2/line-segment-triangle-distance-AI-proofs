import DistanceAccuracy.FmaSwapAlgorithm
import DistanceAccuracy.InvMultiplyCore
namespace DistanceAccuracy.FmaSwapCore
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm
variable (I : Interchange) [I.Valid]
abbrev initial := InvMultiplyCore.initial I
abbrev second := InvMultiplyCore.second I
abbrev third := InvMultiplyCore.third I
def core (P Q R : Vec3 I) : Candidate I :=
  make I (fma3 I (third I P Q R) Q (fma3 I (neg I (second I P Q R)) P R))
    (weights I (second I P Q R) (zero I)) (weights I (third I P Q R) (zero I))
lemma segmentSegment_eq (x y : Segment I) : FmaSwapAlgorithm.segmentSegment I x y =
    core I (vsub I (x 1) (x 0)) (vsub I (y 1) (y 0)) (vsub I (y 0) (x 0)) := rfl
end DistanceAccuracy.FmaSwapCore

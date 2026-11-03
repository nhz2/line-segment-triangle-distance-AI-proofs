import DistanceAccuracy.ThreeDivideGeometry
import DistanceAccuracy.ThreeDivideEvaluation
import DistanceAccuracy.ThreeDivideFinal

-- Exact arithmetic: the actual three scalar formulas attain the segment minimum.
#check DistanceAccuracy.ThreeDivideGeometry.minimizes
#print axioms DistanceAccuracy.ThreeDivideGeometry.minimizes
#print axioms DistanceAccuracy.ThreeDivideGeometry.first_formula
#print axioms DistanceAccuracy.ThreeDivideGeometry.second_formula
#print axioms DistanceAccuracy.ThreeDivideGeometry.third_formula

-- IEEE arithmetic: all nine ordered pairings use the NEW kernel.
#check DistanceAccuracy.ThreeDivideEvaluation.lower
#print axioms DistanceAccuracy.ThreeDivideEvaluation.lower
#check DistanceAccuracy.ThreeDivideEvaluation.small_accuracy
#print axioms DistanceAccuracy.ThreeDivideEvaluation.small_accuracy

-- Full upper and two-sided bounds, with no output-accuracy certificates,
-- local error assumptions, or finite-intermediate hypotheses.
#print DistanceAccuracy.threeDivideAccuracyStatement
#check DistanceAccuracy.threeDivideUpper
#print axioms DistanceAccuracy.ThreeDivideKernelUpper.kernel_upper
#print axioms DistanceAccuracy.ThreeDivideSegmentUpper.accuracy
#print axioms DistanceAccuracy.ThreeDivideTriangleUpper.segment_triangle_large
#print axioms DistanceAccuracy.ThreeDivideTriangleUpper.triangle_triangle_large
#print axioms DistanceAccuracy.threeDivideUpper
#print axioms DistanceAccuracy.threeDivideClaim4
#print axioms DistanceAccuracy.threeDivideClaim4_binary32
#print axioms DistanceAccuracy.threeDivideClaim4_binary64

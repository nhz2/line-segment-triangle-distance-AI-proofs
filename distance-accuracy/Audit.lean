import DistanceAccuracy

-- Audit the formal theorem's premises as well as its logical dependencies.
#check DistanceAccuracy.format_claim4_conditional
#print axioms DistanceAccuracy.projection_loss
#print axioms DistanceAccuracy.projection_loss_absolute
#print axioms DistanceAccuracy.clamp_optimal
#print axioms DistanceAccuracy.dot3_error
#print axioms DistanceAccuracy.crossing_coefficient
#print axioms DistanceAccuracy.Format.underflow_budget
#print axioms DistanceAccuracy.format_claim4_conditional
#print axioms DistanceAccuracy.claim4_rounded_of_certificates
#print axioms DistanceAccuracy.Counterexample.exceeds_nine_with_floor

#print DistanceAccuracy.Geometry.accuracyStatement
#print axioms DistanceAccuracy.IEEEBridge.mul_error
#print axioms DistanceAccuracy.IEEEBridge.fma_error
#print axioms DistanceAccuracy.IEEEBridge.dot3_error
#print axioms DistanceAccuracy.Geometry.closest_pair
#print axioms DistanceAccuracy.clamped_affine_root_error

-- New implementation-level results: inspect both premises and axioms.
#check DistanceAccuracy.PointUpper.pointPoint_accuracyStatement
#print axioms DistanceAccuracy.PointUpper.pointPoint_accuracyStatement
#print axioms DistanceAccuracy.OperationBounds.clamp01nan_bounded
#print axioms DistanceAccuracy.Determinant.word_cross3Accurate_thick
#print axioms DistanceAccuracy.ReconstructionIEEE.dot3_self_finite_error
#print axioms DistanceAccuracy.CandidateLower.face_safe
#print axioms DistanceAccuracy.CandidateLower.crossing_safe
#print axioms DistanceAccuracy.CandidateLower.segmentSegment_safe
#print axioms DistanceAccuracy.BCLower.pointTriangle_safe
#print axioms DistanceAccuracy.GeometryCoverage.triangle_boundary_witness
#print axioms DistanceAccuracy.GeometryCoverage.roundoff_thin_edge_witness
#print axioms DistanceAccuracy.Selection.triangleTriangle_property
#print axioms DistanceAccuracy.PlaneCrossing.plane_height
#print axioms DistanceAccuracy.revised_claim4_of_bounds

#check DistanceAccuracy.PointUpper.pointSegment_accuracyStatement
#print axioms DistanceAccuracy.PointUpper.pointSegment_accuracyStatement
#print axioms DistanceAccuracy.PointUpper.segmentPoint_accuracyStatement

#check DistanceAccuracy.EvaluateLower.lower
#check DistanceAccuracy.EvaluateLower.small_accuracy
#print axioms DistanceAccuracy.EvaluateLower.lower
#print axioms DistanceAccuracy.EvaluateLower.small_accuracy

-- Final universal result: only admissibility premises, all ordered shape pairs.
#check DistanceAccuracy.finalClaim4
#print DistanceAccuracy.finalClaim4_binary32
#print DistanceAccuracy.finalClaim4_binary64
#print axioms DistanceAccuracy.finalClaim4
#print axioms DistanceAccuracy.finalClaim4_binary32
#print axioms DistanceAccuracy.finalClaim4_binary64
#print axioms DistanceAccuracy.PointTriangleUpper.pointTriangle_accuracyStatement
#print axioms DistanceAccuracy.PointTriangleUpper.trianglePoint_accuracyStatement
#print axioms DistanceAccuracy.SegmentUpper.accuracy
#print axioms DistanceAccuracy.TriangleUpper.segment_triangle_large
#print axioms DistanceAccuracy.TriangleUpper.triangle_triangle_large

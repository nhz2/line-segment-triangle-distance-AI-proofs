import DistanceAccuracy.PointUpper
import DistanceAccuracy.PointSegmentComplete
import DistanceAccuracy.PointTriangleUpper
import DistanceAccuracy.SegmentUpper
import DistanceAccuracy.TriangleUpper
import DistanceAccuracy.AccuracyAssembly

/-! Claim 4 for every pairing of the executable IEEE-word implementation.
The only premises are the finite coordinate bounds in Geometry.admissible. -/
namespace DistanceAccuracy
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm

/-- The complete, certificate-free claim4 theorem for either supported format. -/
theorem finalClaim4 (fmt : Format) : Geometry.accuracyStatement fmt.interchange := by
  intro x y L hadm
  cases x with
  | point x =>
    cases y with
    | point y => exact PointUpper.pointPoint_accuracyStatement fmt x y L hadm
    | segment y => exact PointUpper.pointSegment_accuracyStatement fmt x y L hadm
    | triangle y => exact PointTriangleUpper.pointTriangle_accuracyStatement fmt x y L hadm
  | segment x =>
    cases y with
    | point y => exact PointUpper.segmentPoint_accuracyStatement fmt x y L hadm
    | segment y => exact SegmentUpper.accuracy fmt x y L hadm
    | triangle y =>
      exact AccuracyAssembly.of_upper fmt (.segment x) (.triangle y) L hadm
        (TriangleUpper.segment_triangle_large fmt x y L hadm)
  | triangle x =>
    cases y with
    | point y => exact PointTriangleUpper.trianglePoint_accuracyStatement fmt x y L hadm
    | segment y =>
      obtain ⟨q,hq,hb⟩ := AccuracyAssembly.of_upper fmt (.segment y) (.triangle x) L
        ⟨hadm.1,hadm.2.1,hadm.2.2.2,hadm.2.2.1⟩
        (TriangleUpper.segment_triangle_large fmt y x L ⟨hadm.1,hadm.2.1,hadm.2.2.2,hadm.2.2.1⟩)
      exact ⟨q,hq,by rw [Geometry.distance_symm]; exact hb⟩
    | triangle y =>
      exact AccuracyAssembly.of_upper fmt (.triangle x) (.triangle y) L hadm
        (TriangleUpper.triangle_triangle_large fmt x y L hadm)

/-- Claim4 for all admissible binary32 words and all nine ordered shape pairs. -/
theorem finalClaim4_binary32 : Geometry.accuracyStatement fp32 := finalClaim4 .binary32

/-- Claim4 for all admissible binary64 words and all nine ordered shape pairs. -/
theorem finalClaim4_binary64 : Geometry.accuracyStatement fp64 := finalClaim4 .binary64

end DistanceAccuracy

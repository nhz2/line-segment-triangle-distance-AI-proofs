import DistanceAccuracy.PointUpper
import DistanceAccuracy.PointSegmentComplete
import DistanceAccuracy.PointTriangleUpper
import DistanceAccuracy.ThreeDivideSegmentUpper
import DistanceAccuracy.ThreeDivideTriangleUpper
import DistanceAccuracy.ThreeDivideAccuracyAssembly

/-! Claim 4 for every pairing of the executable IEEE-word implementation.
The only premises are the finite coordinate bounds in Geometry.admissible. -/
namespace DistanceAccuracy
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm

/-- The original constant-64 contract, now for the revised executable model. -/
def threeDivideAccuracyStatement (I : Interchange) [I.Valid] : Prop :=
  ∀ (x y : Simplex I) (L : ℝ), Geometry.admissible I x y L →
    ∃ q : ℝ, I.decode? (ThreeDivideAlgorithm.evaluate I x y).q = some q ∧
      |Real.sqrt q-Geometry.distance I x y| ≤
        64*(2*I.format.unitRoundoff)*L+fourthRoot I.format.minNormal

/-- The complete, certificate-free claim4 theorem for either supported format. -/
theorem threeDivideClaim4 (fmt : Format) : threeDivideAccuracyStatement fmt.interchange := by
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
    | segment y => exact ThreeDivideSegmentUpper.accuracy fmt x y L hadm
    | triangle y =>
      exact ThreeDivideAccuracyAssembly.of_upper fmt (.segment x) (.triangle y) L hadm
        (ThreeDivideTriangleUpper.segment_triangle_large fmt x y L hadm)
  | triangle x =>
    cases y with
    | point y => exact PointTriangleUpper.trianglePoint_accuracyStatement fmt x y L hadm
    | segment y =>
      obtain ⟨q,hq,hb⟩ := ThreeDivideAccuracyAssembly.of_upper fmt (.segment y) (.triangle x) L
        ⟨hadm.1,hadm.2.1,hadm.2.2.2,hadm.2.2.1⟩
        (ThreeDivideTriangleUpper.segment_triangle_large fmt y x L ⟨hadm.1,hadm.2.1,hadm.2.2.2,hadm.2.2.1⟩)
      exact ⟨q,hq,by rw [Geometry.distance_symm]; exact hb⟩
    | triangle y =>
      exact ThreeDivideAccuracyAssembly.of_upper fmt (.triangle x) (.triangle y) L hadm
        (ThreeDivideTriangleUpper.triangle_triangle_large fmt x y L hadm)

/-- Claim4 for all admissible binary32 words and all nine ordered shape pairs. -/
theorem threeDivideClaim4_binary32 : threeDivideAccuracyStatement fp32 := threeDivideClaim4 .binary32

/-- Claim4 for all admissible binary64 words and all nine ordered shape pairs. -/
theorem threeDivideClaim4_binary64 : threeDivideAccuracyStatement fp64 := threeDivideClaim4 .binary64

/-- The requested upper side, for every pairing of the revised executable
implementation, with only the original admissibility assumptions. -/
theorem threeDivideUpper (fmt : Format) (x y : Simplex fmt.interchange) (L : ℝ)
    (hadm : Geometry.admissible fmt.interchange x y L) :
    ∃ q : ℝ, fmt.interchange.decode? (ThreeDivideAlgorithm.evaluate fmt.interchange x y).q = some q ∧
      Real.sqrt q-Geometry.distance fmt.interchange x y ≤
        64*(2*fmt.interchange.format.unitRoundoff)*L+fourthRoot fmt.interchange.format.minNormal := by
  obtain ⟨q,hq,hbound⟩ := threeDivideClaim4 fmt x y L hadm
  exact ⟨q,hq,(abs_le.mp hbound).2⟩

end DistanceAccuracy

import DistanceAccuracy.PointUpper
import DistanceAccuracy.PointSegmentComplete
import DistanceAccuracy.PointTriangleUpper
import DistanceAccuracy.InvMultiplySegmentUpper
import DistanceAccuracy.InvMultiplyTriangleUpper
import DistanceAccuracy.InvMultiplyAccuracyAssembly

/-! Claim 4 for every pairing of the executable IEEE-word implementation.
The only premises are the finite coordinate bounds in Geometry.admissible. -/
namespace DistanceAccuracy
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm

/-- The original constant-64 contract, now for the revised executable model. -/
def invMultiplyAccuracyStatement (I : Interchange) [I.Valid] : Prop :=
  ∀ (x y : Simplex I) (L : ℝ), Geometry.admissible I x y L →
    ∃ q : ℝ, I.decode? (InvMultiplyAlgorithm.evaluate I x y).q = some q ∧
      |Real.sqrt q-Geometry.distance I x y| ≤
        64*(2*I.format.unitRoundoff)*L+fourthRoot I.format.minNormal

/-- The complete, certificate-free claim4 theorem for either supported format. -/
theorem invMultiplyClaim4 (fmt : Format) : invMultiplyAccuracyStatement fmt.interchange := by
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
    | segment y => exact InvMultiplySegmentUpper.accuracy fmt x y L hadm
    | triangle y =>
      exact InvMultiplyAccuracyAssembly.of_upper fmt (.segment x) (.triangle y) L hadm
        (InvMultiplyTriangleUpper.segment_triangle_large fmt x y L hadm)
  | triangle x =>
    cases y with
    | point y => exact PointTriangleUpper.trianglePoint_accuracyStatement fmt x y L hadm
    | segment y =>
      obtain ⟨q,hq,hb⟩ := InvMultiplyAccuracyAssembly.of_upper fmt (.segment y) (.triangle x) L
        ⟨hadm.1,hadm.2.1,hadm.2.2.2,hadm.2.2.1⟩
        (InvMultiplyTriangleUpper.segment_triangle_large fmt y x L ⟨hadm.1,hadm.2.1,hadm.2.2.2,hadm.2.2.1⟩)
      exact ⟨q,hq,by rw [Geometry.distance_symm]; exact hb⟩
    | triangle y =>
      exact InvMultiplyAccuracyAssembly.of_upper fmt (.triangle x) (.triangle y) L hadm
        (InvMultiplyTriangleUpper.triangle_triangle_large fmt x y L hadm)

/-- Claim4 for all admissible binary32 words and all nine ordered shape pairs. -/
theorem invMultiplyClaim4_binary32 : invMultiplyAccuracyStatement fp32 := invMultiplyClaim4 .binary32

/-- Claim4 for all admissible binary64 words and all nine ordered shape pairs. -/
theorem invMultiplyClaim4_binary64 : invMultiplyAccuracyStatement fp64 := invMultiplyClaim4 .binary64

/-- The requested upper side, for every pairing of the revised executable
implementation, with only the original admissibility assumptions. -/
theorem invMultiplyUpper (fmt : Format) (x y : Simplex fmt.interchange) (L : ℝ)
    (hadm : Geometry.admissible fmt.interchange x y L) :
    ∃ q : ℝ, fmt.interchange.decode? (InvMultiplyAlgorithm.evaluate fmt.interchange x y).q = some q ∧
      Real.sqrt q-Geometry.distance fmt.interchange x y ≤
        64*(2*fmt.interchange.format.unitRoundoff)*L+fourthRoot fmt.interchange.format.minNormal := by
  obtain ⟨q,hq,hbound⟩ := invMultiplyClaim4 fmt x y L hadm
  exact ⟨q,hq,(abs_le.mp hbound).2⟩

end DistanceAccuracy

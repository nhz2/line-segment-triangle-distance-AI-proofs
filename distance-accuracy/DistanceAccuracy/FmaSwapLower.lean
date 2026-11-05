import DistanceAccuracy.EvaluateLower
import DistanceAccuracy.FmaSwapReconstruction
import DistanceAccuracy.FmaSwapSelection

/-! Lower bound and small-coordinate accuracy for the NEW executable model.
This file does not assert the large-coordinate upper bound. -/
namespace DistanceAccuracy.FmaSwapLower
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds DistanceAccuracy.Geometry CandidateLower
variable (I : Interchange) [I.Valid]

theorem segmentSegment_safe {S T : Set E3} {x y : Segment I}
    {P₀ P₁ Q₀ Q₁ : Fin 3 → ℚ} {d L : ℝ}
    (hp0 : ∀ k, value? I (x 0 k) = some (P₀ k))
    (hp1 : ∀ k, value? I (x 1 k) = some (P₁ k))
    (hq0 : ∀ k, value? I (y 0 k) = some (Q₀ k))
    (hq1 : ∀ k, value? I (y 1 k) = some (Q₁ k))
    (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hp0m : ratVec P₀ ∈ S) (hp1m : ratVec P₁ ∈ S)
    (hq0m : ratVec Q₀ ∈ T) (hq1m : ratVec Q₁ ∈ T)
    (hd : ∀ p ∈ S, ∀ q ∈ T, d ≤ ‖q-p‖)
    (hL : 0 ≤ L) (hP0 : ∀ k, |(P₀ k : ℝ)| ≤ L) (hP1 : ∀ k, |(P₁ k : ℝ)| ≤ L)
    (hQ0 : ∀ k, |(Q₀ k : ℝ)| ≤ L) (hQ1 : ∀ k, |(Q₁ k : ℝ)| ≤ L)
    (hone : value? I (one I) = some 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024) (heta1 : I.format.minSubnormal ≤ 1)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hunder : 2*Real.sqrt I.format.minSubnormal ≤ I.format.unitRoundoff*L)
    (hlin : 32*L < I.format.overflowThreshold)
    (hquad : 512*L*L+4 < I.format.overflowThreshold) :
    Safe I d (120*I.format.unitRoundoff*L) (FmaSwapAlgorithm.segmentSegment I x y).q := by
  let P := vsub I (x 1) (x 0)
  let Q := vsub I (y 1) (y 0)
  let R := vsub I (y 0) (x 0)
  let b := dot3 I P Q
  let c := dot3 I Q Q
  let e := dot3 I Q R
  let n := cross3 I P Q
  let tw := clamp01nan I (div I (neg I (dot3 I n (cross3 I P R))) (dot3 I n n))
  let sw := clamp01nan I (InvProjectionRounding.rdiv I (fma I tw b (dot3 I P R)) (dot3 I P P))
  let tf := clamp01nan I (InvProjectionRounding.rdiv I (fma I sw b (neg I e)) c)
  obtain ⟨s, hs, hs0, hs1⟩ := clamp01nan_bounded I hone (InvProjectionRounding.rdiv I (fma I tw b (dot3 I P R)) (dot3 I P P))
  obtain ⟨t, ht, ht0, ht1⟩ := clamp01nan_bounded I hone (InvProjectionRounding.rdiv I (fma I sw b (neg I e)) c)
  choose rv hrv herr using fun k => FmaSwapReconstruction.segment_trace I
    (hp0 k) (hp1 k) (hq0 k) (hq1 k) hs ht hL (hP0 k) (hP1 k) (hQ0 k) (hQ1 k)
    hs0 hs1 ht0 ht1 hrho heta hlin
  exact segment_data_safe I hS hT hp0m hp1m hq0m hq1m hd hL hP0 hP1 hQ0 hQ1
    (by exact_mod_cast hs0) (by exact_mod_cast hs1) (by exact_mod_cast ht0) (by exact_mod_cast ht1)
    hrv herr hrho heta1 hunder hquad

end DistanceAccuracy.FmaSwapLower

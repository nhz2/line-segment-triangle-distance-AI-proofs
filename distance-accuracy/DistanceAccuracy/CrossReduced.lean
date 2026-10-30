import DistanceAccuracy.CrossPair
import DistanceAccuracy.WordReducedGeometry
import DistanceAccuracy.LineReduction

namespace DistanceAccuracy.PointProjection
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds
open DistanceAccuracy.Determinant

/-- Connect actual cross-vector data to the exact line minimizer. The supplied
joint perturbation estimate is produced by CrossPair's concrete IEEE theorems. -/
theorem cross_reduced_from_data (I : Interchange) [I.Valid]
    {nw kw : Vec3 I} {N K E F R : Fin 3 → ℚ} {u v D d c P : ℝ}
    (hone : value? I (one I) = some 1)
    (hn : ∀ i, value? I (nw i) = some (N i))
    (hk : ∀ i, value? I (kw i) = some (K i))
    (hE : realVec E ≠ 0) (hD : 0 < D) (hd : 0 ≤ d) (hc : 0 ≤ c)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hrmax : I.format.unitRoundoff ≤ 1/16777216)
    (hlim1 : (1:ℝ) < I.format.overflowThreshold)
    (hnD : ‖realVec N‖ ≤ (1+4*I.format.unitRoundoff)*(‖realVec E‖*D))
    (hkD : ‖realVec K‖ ≤ (1+4*I.format.unitRoundoff)*(‖realVec E‖*D))
    (he : ‖realVec N-exactCross (realVec E) (realVec F)‖+
      ‖realVec K-exactCross (realVec E) (realVec R)‖ ≤ c*I.format.unitRoundoff*‖realVec E‖*D)
    (hwitness : ‖GeometryCoverage.residual (realVec R) (realVec E) (realVec F) u v‖ ≤ d)
    (hP : 0 < P) (hbound : ((1+4*I.format.unitRoundoff)*(‖realVec E‖*D))^2 ≤ P)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff*P)
    (hlim : (11/10:ℝ)*P < I.format.overflowThreshold) :
    ∃ t : ℚ, value? I (clamp01nan I (IEEEAlgorithm.div I (neg I (dot3 I nw kw)) (dot3 I nw nw))) = some t ∧
      0 ≤ t ∧ t ≤ 1 ∧
      ‖GeometryCoverage.residual (realVec R) (realVec E) (realVec F)
        (LineReduction.parameter (realVec E) (realVec R) (realVec F) (t:ℝ)) (t:ℝ)‖ ≤
        I.format.unitRoundoff*D*J c (d/(I.format.unitRoundoff*D))+
        4*Real.sqrt I.format.minSubnormal/‖realVec E‖+
        2*Real.sqrt I.format.minSubnormal*(1+4*I.format.unitRoundoff)*D := by
  have hA := norm_pos_iff.mpr hE
  have hstar : ‖exactCross (realVec E) (realVec R)+v•exactCross (realVec E) (realVec F)‖ ≤ ‖realVec E‖*d := by
    have h := (LineReduction.line_minimizes hE u v).trans hwitness
    rw [LineReduction.reduced_norm_raw hE] at h
    exact (div_le_iff₀ hA).mp h |>.trans_eq (mul_comm _ _)
  have he' : ‖realVec K-exactCross (realVec E) (realVec R)‖+
      ‖realVec N-exactCross (realVec E) (realVec F)‖ ≤ ‖realVec E‖*(c*I.format.unitRoundoff*D) := by
    nlinarith only [he]
  obtain ⟨t,ht,ht0,ht1,hh⟩ := word_reduced_geometry I hone hn hk hA hD hd hc hv0 hv1 hrmax hlim1
    hnD hkD he' hstar hP hbound heta hlim
  refine ⟨t,ht,ht0,ht1,?_⟩
  rw [LineReduction.reduced_norm_raw hE]
  have hs := Real.sqrt_nonneg I.format.minSubnormal
  have hmul := mul_le_mul_of_nonneg_left hnD (show 0 ≤ 2*Real.sqrt I.format.minSubnormal by positivity)
  have hdiv := div_le_div_of_nonneg_right hmul hA.le
  have heq : (2*Real.sqrt I.format.minSubnormal*((1+4*I.format.unitRoundoff)*(‖realVec E‖*D)))/‖realVec E‖ =
      2*Real.sqrt I.format.minSubnormal*(1+4*I.format.unitRoundoff)*D := by field_simp <;> ring
  rw [heq] at hdiv
  change ‖exactCross (realVec E) (realVec R)+(t:ℝ)•exactCross (realVec E) (realVec F)‖/‖realVec E‖ ≤ _
  linarith

end DistanceAccuracy.PointProjection

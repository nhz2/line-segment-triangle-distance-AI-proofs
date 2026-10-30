import DistanceAccuracy.ReducedGeometry
import DistanceAccuracy.DotSumRange

namespace DistanceAccuracy.PointProjection
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds
open DistanceAccuracy.Determinant

lemma products_sum_le_norm (a b : E3) :
    |a 0*b 0|+|a 1*b 1|+|a 2*b 2| ≤ ‖a‖*‖b‖ := by
  have h := real_inner_le_norm (absVec a) (absVec b)
  simp only [norm_absVec] at h
  simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_succ,absVec,abs_mul,mul_comm,add_assoc] using h

/-- All dot products and parameter operations of the reduced solve, with the
range bound on the sum of products rather than a per-coordinate sixfold bound. -/
theorem word_reduced_geometry (I : Interchange) [I.Valid]
    {nw kw : Vec3 I} {N K : Fin 3 → ℚ} {n k : E3} {v A D d c P : ℝ}
    (hone : value? I (one I) = some 1)
    (hn : ∀ i, value? I (nw i) = some (N i))
    (hk : ∀ i, value? I (kw i) = some (K i))
    (hA : 0 < A) (hD : 0 < D) (hd : 0 ≤ d) (hc : 0 ≤ c)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hrmax : I.format.unitRoundoff ≤ 1/16777216)
    (hlim1 : (1:ℝ) < I.format.overflowThreshold)
    (hnD : ‖realVec N‖ ≤ (1+4*I.format.unitRoundoff)*(A*D))
    (hkD : ‖realVec K‖ ≤ (1+4*I.format.unitRoundoff)*(A*D))
    (he : ‖realVec K-k‖+‖realVec N-n‖ ≤ A*(c*I.format.unitRoundoff*D))
    (hstar : ‖k+v•n‖ ≤ A*d)
    (hP : 0 < P) (hbound : ((1+4*I.format.unitRoundoff)*(A*D))^2 ≤ P)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff*P)
    (hlim : (11/10:ℝ)*P < I.format.overflowThreshold) :
    ∃ t : ℚ, value? I (clamp01nan I (IEEEAlgorithm.div I (neg I (dot3 I nw kw)) (dot3 I nw nw))) = some t ∧
      0 ≤ t ∧ t ≤ 1 ∧
      ‖k+(t:ℝ)•n‖/A ≤ I.format.unitRoundoff*D*J c (d/(I.format.unitRoundoff*D))+
        4*Real.sqrt I.format.minSubnormal/A+2*Real.sqrt I.format.minSubnormal*‖realVec N‖/A := by
  have hr := I.format.unitRoundoff_pos.le
  have hU : 0 ≤ (1+4*I.format.unitRoundoff)*(A*D) := by positivity
  have sum_bound (V W : Fin 3 → ℚ)
      (hv : ‖realVec V‖ ≤ (1+4*I.format.unitRoundoff)*(A*D))
      (hw : ‖realVec W‖ ≤ (1+4*I.format.unitRoundoff)*(A*D)) :
      |(V 0:ℝ)*(W 0:ℝ)|+|(V 1:ℝ)*(W 1:ℝ)|+|(V 2:ℝ)*(W 2:ℝ)| ≤ P := by
    have h := products_sum_le_norm (realVec V) (realVec W)
    have hm := mul_le_mul hv hw (norm_nonneg _) hU
    change |(V 0:ℝ)*(W 0:ℝ)|+|(V 1:ℝ)*(W 1:ℝ)|+|(V 2:ℝ)*(W 2:ℝ)| ≤ _ at h
    nlinarith only [h,hm,hbound]
  obtain ⟨a,ha,hea⟩ := DotWordBounds.dot3_finite_error_sum I hn hn hP (sum_bound N N hnD hnD)
    heta (by linarith) hlim
  obtain ⟨b,hb,heb⟩ := DotWordBounds.dot3_finite_error_sum I hn hk hP (sum_bound N K hnD hkD)
    heta (by linarith) hlim
  have hea' : |(a:ℝ)-‖realVec N‖^2| ≤
      3*I.format.unitRoundoff*(1+I.format.unitRoundoff)^2*‖realVec N‖^2+2*I.format.minSubnormal := by
    have heq : ‖realVec N‖^2 = (N 0:ℝ)*(N 0:ℝ)+(N 1:ℝ)*(N 1:ℝ)+(N 2:ℝ)*(N 2:ℝ) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [realVec,Fin.sum_univ_succ,pow_two,add_assoc]
    rw [← heq] at hea
    nlinarith only [hea]
  have heb' : |(b:ℝ)-inner ℝ (realVec N) (realVec K)| ≤
      3*I.format.unitRoundoff*(1+I.format.unitRoundoff)^2*‖realVec N‖*‖realVec K‖+2*I.format.minSubnormal := by
    have heq : inner ℝ (realVec N) (realVec K) =
        (N 0:ℝ)*(K 0:ℝ)+(N 1:ℝ)*(K 1:ℝ)+(N 2:ℝ)*(K 2:ℝ) := by
      simp [realVec,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_succ,mul_comm,add_assoc]
    rw [heq]
    exact heb
  exact reduced_geometry_bound I hone ha hb hA hD hd hc hv0 hv1 hrmax hlim1 hnD hkD he hstar hea' heb'

end DistanceAccuracy.PointProjection

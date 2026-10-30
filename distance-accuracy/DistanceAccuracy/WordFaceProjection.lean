import DistanceAccuracy.WordProjectionRounding
import DistanceAccuracy.FaceProjectionRounding

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge

/-- Concrete face reciprocal/product/FMA execution admits the effective
quadratic used in the relative and absolute face-gradient bounds. -/
theorem word_face_effective (I : Interchange) [I.Valid]
    {aw bw dw vw : I.Word} {a b d v c m q : ℚ} {x : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hd : value? I dw = some d) (hv : value? I vw = some v)
    (hap : 0 < a) (hv1 : (v : ℝ) ≤ 1)
    (hrmax : I.format.unitRoundoff < 1)
    (hnormal : I.format.minNormal ≤ 1 / (a : ℝ))
    (hlim : 1 / (a : ℝ) < I.format.overflowThreshold)
    (hc : value? I (IEEEAlgorithm.mul I bw (IEEEAlgorithm.div I (one I) aw)) = some c)
    (hm : value? I (IEEEAlgorithm.mul I (IEEEAlgorithm.neg I dw)
      (IEEEAlgorithm.div I (one I) aw)) = some m)
    (hq : value? I (IEEEAlgorithm.fma I (IEEEAlgorithm.neg I vw)
      (IEEEAlgorithm.mul I bw (IEEEAlgorithm.div I (one I) aw))
      (IEEEAlgorithm.mul I (IEEEAlgorithm.neg I dw) (IEEEAlgorithm.div I (one I) aw))) = some q)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 - (v : ℝ)) :
    ∃ di dc dm dq zc zm zq : ℝ,
      |di| ≤ I.format.unitRoundoff ∧ |dc| ≤ I.format.unitRoundoff ∧
      |dm| ≤ I.format.unitRoundoff ∧ |dq| ≤ I.format.unitRoundoff ∧
      |zc| ≤ I.format.minSubnormal / 2 ∧ |zm| ≤ I.format.minSubnormal / 2 ∧
      |zq| ≤ I.format.minSubnormal / 2 ∧
      let ae := (a : ℝ) / ((1 + di) * (1 + dq))
      let be := (d : ℝ) * (1 + dm) + (v : ℝ) * (b : ℝ) * (1 + dc) -
        ae * ((zm - (v : ℝ) * zc) * (1 + dq) + zq)
      0 ≤ (ae * max 0 (min (1 - (v : ℝ)) (q : ℝ)) + be) *
        (x - max 0 (min (1 - (v : ℝ)) (q : ℝ))) := by
  obtain ⟨ir, di, hir, hie, hdi⟩ := reciprocal_relative I hone ha hap hnormal hlim
  obtain ⟨dc, zc, hce, hdc, hzc⟩ := word_multiplication_decomposition I hb hir hc
  obtain ⟨dm, zm, hme, hdm, hzm⟩ := word_multiplication_decomposition I
    (Determinant.neg_value I hd) hir hm
  obtain ⟨dq, zq, hqe, hdq, hzq⟩ := word_fma_decomposition I
    (Determinant.neg_value I hv) hc hm hq
  refine ⟨di, dc, dm, dq, zc, zm, zq, hdi, hdc, hdm, hdq, hzc, hzm, hzq, ?_⟩
  have hdi0 := (abs_le.mp hdi).1
  have hdq0 := (abs_le.mp hdq).1
  apply face_effective_optimal (m := (m : ℝ)) (by exact_mod_cast hap)
    (by linarith) (by linarith) hie hce _ _ hv1 hx0 hx1
  · simpa only [Rat.cast_neg] using hme
  · simpa only [Rat.cast_neg] using hqe

end DistanceAccuracy.ProjectionRounding

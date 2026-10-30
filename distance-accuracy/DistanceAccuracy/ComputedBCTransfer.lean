import DistanceAccuracy.WordGeometryTransfer
import DistanceAccuracy.SegmentEvaluation

namespace DistanceAccuracy.WordGeometryTransfer
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds Determinant

lemma vadd_finite_norm_error (I : Interchange) [I.Valid]
    {A B : Vec3 I} {a b : Fin 3 → ℚ}
    (ha : ∀ i, value? I (A i) = some (a i)) (hb : ∀ i, value? I (B i) = some (b i))
    (hlim : ‖realVec a+realVec b‖ < I.format.overflowThreshold) :
    ∃ out : Fin 3 → ℚ, (∀ i, value? I (vadd I A B i) = some (out i)) ∧
      ‖realVec out-(realVec a+realVec b)‖ ≤ I.format.unitRoundoff*‖realVec a+realVec b‖+I.format.minSubnormal := by
  have hcoord (i : Fin 3) : |(a i : ℝ)+(b i : ℝ)| < I.format.overflowThreshold := by
    have hh := PiLp.norm_apply_le (realVec a+realVec b) i
    simp only [PiLp.add_apply, realVec, WithLp.ofLp_toLp, Real.norm_eq_abs] at hh
    exact hh.trans_lt hlim
  choose out hout herr using fun i => binary_exists_error I .add (ha i) (hb i)
    (no_overflow_of_lt I _ (by simpa only [Software.binaryExact, Rat.cast_add] using hcoord i))
  have hr := I.format.unitRoundoff_pos.le
  have he : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hv := vector_mixed_bound hr (le_refl (0:ℝ)) (show 0 ≤ I.format.minSubnormal/2 by positivity)
    (r := realVec out-(realVec a+realVec b)) (n := realVec a+realVec b) (p := (0:E3))
    (by intro i; simpa [realVec, Software.binaryExact, Rat.cast_add] using herr i)
  have hs : Real.sqrt (3:ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hm := mul_le_mul_of_nonneg_right hs he
  refine ⟨out, hout, ?_⟩
  simp only [zero_mul, add_zero] at hv
  nlinarith

/-- The difference of two independently rounded edges from the same anchor
    still has norm at most the common diameter3.5L. -/
theorem edge_difference (I : Interchange) [I.Valid]
    {a b c : Vec3 I} {A B C e f : Fin 3 → ℚ} {L : ℝ}
    (ha : ∀ k, value? I (a k) = some (A k)) (hb : ∀ k, value? I (b k) = some (B k))
    (hc : ∀ k, value? I (c k) = some (C k))
    (he : ∀ k, value? I (vsub I b a k) = some (e k))
    (hf : ∀ k, value? I (vsub I c a k) = some (f k))
    (hL : 0 ≤ L) (hA : ∀ k, |(A k : ℝ)| ≤ L) (hB : ∀ k, |(B k : ℝ)| ≤ L)
    (hC : ∀ k, |(C k : ℝ)| ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) : ‖realVec f-realVec e‖ ≤ (7/2)*L := by
  have heErr := difference_error I hb ha he hL hB hA hrho heta hlim
  have hfErr := difference_error I hc ha hf hL hC hA hrho heta hlim
  have hn := GeometryCoverage.coordinate_norm_bound (v := realVec C-realVec B)
    (show 0 ≤ 2*L by positivity) (fun k => Reconstruction.difference_abs (hC k) (hB k))
  have h1 := norm_sub_le (realVec f-(realVec C-realVec A)) (realVec e-(realVec B-realVec A))
  have h2 := norm_add_le
    ((realVec f-(realVec C-realVec A))-(realVec e-(realVec B-realVec A))) (realVec C-realVec B)
  have hid : ((realVec f-(realVec C-realVec A))-(realVec e-(realVec B-realVec A)))+(realVec C-realVec B) = realVec f-realVec e := by module
  rw [hid] at h2
  have hs : Real.sqrt (3:ℝ) ≤ 26/15 := by apply Real.sqrt_le_iff.mpr; norm_num
  have hm := mul_le_mul_of_nonneg_right hs hL
  have hρL := mul_le_mul_of_nonneg_right hrho hL
  nlinarith

/-- Actual point/triangle BC intermediates fl(F-E) and fl(R+E) transfer to
    the common rounded triangle with at most2.02ρD, D=3.5L. -/
theorem computed_bc_transfer (I : Interchange) [I.Valid]
    {E F R : Vec3 I} {e f r e2 bx : Fin 3 → ℚ} {L t : ℝ}
    (hE : ∀ k, value? I (E k) = some (e k))
    (hF : ∀ k, value? I (F k) = some (f k))
    (hR : ∀ k, value? I (R k) = some (r k))
    (he2 : ∀ k, value? I (vsub I F E k) = some (e2 k))
    (hbx : ∀ k, value? I (vadd I R E k) = some (bx k))
    (hFE : ‖realVec f-realVec e‖ ≤ (7/2)*L)
    (hRE : ‖realVec r+realVec e‖ ≤ (7/2)*L)
    (hL : 0 ≤ L) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ‖(realVec bx+t•realVec e2)-(realVec r+(1-t)•realVec e+t•realVec f)‖ ≤
      (101/50)*I.format.unitRoundoff*((7/2)*L) := by
  obtain ⟨v, hv, hve⟩ := ProjectionRounding.vsub_finite_norm_error I hF hE (by linarith)
  have hvv : v = e2 := funext (fun k => Option.some.inj ((hv k).symm.trans (he2 k)))
  subst v
  obtain ⟨w, hw, hwe⟩ := vadd_finite_norm_error I hR hE (by linarith)
  have hww : w = bx := funext (fun k => Option.some.inj ((hw k).symm.trans (hbx k)))
  subst w
  have hr := I.format.unitRoundoff_pos.le
  have hη : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hve' := mul_le_mul_of_nonneg_left hFE hr
  have hwe' := mul_le_mul_of_nonneg_left hRE hr
  have hweight := mul_le_mul_of_nonneg_left hve ht0
  have hh := norm_add_le (realVec bx-(realVec r+realVec e)) (t•(realVec e2-(realVec f-realVec e)))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hh
  have hid : (realVec bx-(realVec r+realVec e))+t•(realVec e2-(realVec f-realVec e)) =
      (realVec bx+t•realVec e2)-(realVec r+(1-t)•realVec e+t•realVec f) := by module
  rw [hid] at hh
  have hsmall := mul_le_mul_of_nonneg_right hrho (mul_nonneg hr hL)
  have hbase0 : 0 ≤ I.format.unitRoundoff*((7/2)*L)+I.format.minSubnormal := by positivity
  have hweight2 := mul_le_mul_of_nonneg_left (show ‖realVec e2-(realVec f-realVec e)‖ ≤ I.format.unitRoundoff*((7/2)*L)+I.format.minSubnormal by linarith) ht0
  have hweight3 := mul_le_mul_of_nonneg_right ht1 hbase0
  nlinarith

end DistanceAccuracy.WordGeometryTransfer

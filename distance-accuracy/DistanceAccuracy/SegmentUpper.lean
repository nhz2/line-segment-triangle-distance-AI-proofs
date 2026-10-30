import DistanceAccuracy.SegmentKernelUpper
import DistanceAccuracy.SegmentCoordinates
import DistanceAccuracy.EvaluateLower
import DistanceAccuracy.WordGeometryTransfer

namespace DistanceAccuracy.SegmentUpper
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds Geometry
open DistanceAccuracy.Determinant ProjectionRounding UpperSelection
set_option maxHeartbeats 1500000

/-- The sharp kernel envelope for actual endpoint subtractions, with only
input admissibility and a witness in their common rounded geometry. -/
theorem common_witness (fmt : DistanceAccuracy.Format)
    {x y : Segment fmt.interchange} {L s t d : ℝ}
    (hadm : Geometry.admissible fmt.interchange (.segment x) (.segment y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L)
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) (hd : 0 ≤ d)
    (hw : ‖decodeVec fmt.interchange (vsub fmt.interchange (y 0) (x 0))+
      t•decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0))-
      s•decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0))‖ ≤ d) :
    Upper fmt.interchange (fmt.rho*((7/2)*L)*F (d/(fmt.rho*((7/2)*L)))+
      3.55*fmt.rho*((7/2)*L)+6*fourthRoot fmt.leastSubnormal)
      (segmentSegment fmt.interchange x y).q := by
  let I := fmt.interchange
  let X0 := EvaluateLower.vertex_of_bounded hadm.2.2.1 0
  let X1 := EvaluateLower.vertex_of_bounded hadm.2.2.1 1
  let Y0 := EvaluateLower.vertex_of_bounded hadm.2.2.2 0
  let Y1 := EvaluateLower.vertex_of_bounded hadm.2.2.2 1
  have b := EvaluateLower.format_budget fmt hadm.1 hadm.2.1 hlarge
  obtain ⟨p,q,r,hp,hq,hr,hpC,hqC,hrC,hpD,hqD,hrD,hgeo⟩ :=
    SegmentCoordinates.segment_geometry I X0.decode X1.decode Y0.decode Y1.decode
      hadm.1 X0.bound X1.bound Y0.bound Y1.bound b.rho b.eta b.linear
  have conv {w : Vec3 I} {v : Fin 3 → ℚ} (hv : ∀ i, value? I (w i) = some (v i)) :
      realVec v = decodeVec I w := by
    ext i
    simp [realVec, decodeVec, real_decode I (hv i)]
  have hw' : ‖realVec r+t•realVec q-s•realVec p‖ ≤ d := by
    rw [conv hp,conv hq,conv hr]
    exact hw
  rw [SegmentCore.segmentSegment_eq]
  exact SegmentKernelUpper.kernel_upper fmt hp hq hr hadm.1 hadm.2.1 hlarge
    hpD hqD hrD hpC hqC hrC hgeo hs ht hd hw'

theorem original_witness_sharp (fmt : DistanceAccuracy.Format)
    {x y : Segment fmt.interchange} {L s t d : ℝ}
    (hadm : Geometry.admissible fmt.interchange (.segment x) (.segment y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L)
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) (hd : 0 ≤ d)
    (hw : ‖decodeVec fmt.interchange (y 0)-decodeVec fmt.interchange (x 0)+
      t•(decodeVec fmt.interchange (y 1)-decodeVec fmt.interchange (y 0))-
      s•(decodeVec fmt.interchange (x 1)-decodeVec fmt.interchange (x 0))‖ ≤ d) :
    Upper fmt.interchange (fmt.rho*((7/2)*L)*F ((d+3*fmt.rho*((7/2)*L))/(fmt.rho*((7/2)*L)))+
      3.55*fmt.rho*((7/2)*L)+6*fourthRoot fmt.leastSubnormal)
      (segmentSegment fmt.interchange x y).q := by
  let I := fmt.interchange
  let X0 := EvaluateLower.vertex_of_bounded hadm.2.2.1 0
  let X1 := EvaluateLower.vertex_of_bounded hadm.2.2.1 1
  let Y0 := EvaluateLower.vertex_of_bounded hadm.2.2.2 0
  let Y1 := EvaluateLower.vertex_of_bounded hadm.2.2.2 1
  have b := EvaluateLower.format_budget fmt hadm.1 hadm.2.1 hlarge
  have hrho : I.format.unitRoundoff = fmt.rho := by
    cases fmt with
    | binary32 => exact fp32_parameters.1
    | binary64 => exact fp64_parameters.1
  obtain ⟨p,q,r,hp,hq,hr,_,_,_,_,_,_,_⟩ :=
    SegmentCoordinates.segment_geometry I X0.decode X1.decode Y0.decode Y1.decode
      hadm.1 X0.bound X1.bound Y0.bound Y1.bound b.rho b.eta b.linear
  have conv {w : Vec3 I} {v : Fin 3 → ℚ} (hv : ∀ i, value? I (w i) = some (v i)) :
      realVec v = decodeVec I w := by
    ext i
    simp [realVec, decodeVec, real_decode I (hv i)]
  have heP := WordGeometryTransfer.difference_error I X1.decode X0.decode hp hadm.1 X1.bound X0.bound b.rho b.eta b.linear
  have heQ := WordGeometryTransfer.difference_error I Y1.decode Y0.decode hq hadm.1 Y1.bound Y0.bound b.rho b.eta b.linear
  have heR := WordGeometryTransfer.difference_error I Y0.decode X0.decode hr hadm.1 Y0.bound X0.bound b.rho b.eta b.linear
  simp only [conv hp,conv hq,conv hr,conv X0.decode,conv X1.decode,conv Y0.decode,conv Y1.decode,hrho] at heP heQ heR
  let P := decodeVec I (vsub I (x 1) (x 0))
  let Q := decodeVec I (vsub I (y 1) (y 0))
  let R := decodeVec I (vsub I (y 0) (x 0))
  let P0 := decodeVec I (x 1)-decodeVec I (x 0)
  let Q0 := decodeVec I (y 1)-decodeVec I (y 0)
  let R0 := decodeVec I (y 0)-decodeVec I (x 0)
  let S := fmt.rho*((7/2)*L)
  have hS0 : 0 ≤ S := by dsimp [S]; exact mul_nonneg fmt.rho_nonneg (by linarith [hadm.1])
  have hS : 0 < S := by
    have hL : 0 < L := by
      have hH : 0 < fourthRoot fmt.leastNormal := by
        unfold fourthRoot
        apply Real.sqrt_pos.mpr
        apply Real.sqrt_pos.mpr
        cases fmt <;> norm_num [Format.leastNormal]
      linarith
    dsimp [S]; rw [← hrho]; exact mul_pos I.format.unitRoundoff_pos (by positivity)
  have he : ‖(R+t•Q-s•P)-(R0+t•Q0-s•P0)‖ ≤ 3*S := by
    have hid : (R+t•Q-s•P)-(R0+t•Q0-s•P0) = (R-R0)+t•(Q-Q0)-s•(P-P0) := by module
    rw [hid]
    have h1 := norm_add_le (R-R0) (t•(Q-Q0))
    have h2 := norm_sub_le ((R-R0)+t•(Q-Q0)) (s•(P-P0))
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1] at h1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1] at h2
    have h3 := mul_le_mul ht.2 heQ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have h4 := mul_le_mul hs.2 heP (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    change t*‖Q-Q0‖ ≤ 1*S at h3
    change s*‖P-P0‖ ≤ 1*S at h4
    change ‖R-R0‖ ≤ S at heR
    nlinarith only [h1,h2,h3,h4,heR]
  have hn : ‖R+t•Q-s•P‖ ≤ d+3*S := by
    have hh := norm_le_norm_add_norm_sub (R0+t•Q0-s•P0) (R+t•Q-s•P)
    rw [norm_sub_rev (R+t•Q-s•P) (R0+t•Q0-s•P0)] at he
    exact hh.trans (add_le_add hw he)
  have hu := common_witness fmt hadm hlarge hs ht (by positivity : 0 ≤ d+3*S) hn
  simpa only [S, mul_assoc] using hu

theorem distance_upper_sharp (fmt : DistanceAccuracy.Format)
    {x y : Segment fmt.interchange} {L d : ℝ}
    (hadm : Geometry.admissible fmt.interchange (.segment x) (.segment y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L) (hd : 0 ≤ d)
    (hbound : Geometry.distance fmt.interchange (.segment x) (.segment y) ≤ d) :
    Upper fmt.interchange (fmt.rho*((7/2)*L)*F ((d+3*fmt.rho*((7/2)*L))/(fmt.rho*((7/2)*L)))+
      3.55*fmt.rho*((7/2)*L)+6*fourthRoot fmt.leastSubnormal)
      (segmentSegment fmt.interchange x y).q := by
  obtain ⟨s,t,hs,ht,heq⟩ := Geometry.closest_segments fmt.interchange x y
  exact original_witness_sharp fmt hadm hlarge hs ht hd (heq.ge.trans hbound)

theorem original_witness (fmt : DistanceAccuracy.Format)
    {x y : Segment fmt.interchange} {L s t d : ℝ}
    (hadm : Geometry.admissible fmt.interchange (.segment x) (.segment y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L)
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) (hd : 0 ≤ d)
    (hw : ‖decodeVec fmt.interchange (y 0)-decodeVec fmt.interchange (x 0)+
      t•(decodeVec fmt.interchange (y 1)-decodeVec fmt.interchange (y 0))-
      s•(decodeVec fmt.interchange (x 1)-decodeVec fmt.interchange (x 0))‖ ≤ d) :
    Upper fmt.interchange (d+19*fmt.rho*((7/2)*L)+6*fourthRoot fmt.leastSubnormal)
      (segmentSegment fmt.interchange x y).q := by
  let I := fmt.interchange
  let X0 := EvaluateLower.vertex_of_bounded hadm.2.2.1 0
  let X1 := EvaluateLower.vertex_of_bounded hadm.2.2.1 1
  let Y0 := EvaluateLower.vertex_of_bounded hadm.2.2.2 0
  let Y1 := EvaluateLower.vertex_of_bounded hadm.2.2.2 1
  have b := EvaluateLower.format_budget fmt hadm.1 hadm.2.1 hlarge
  have hrho : I.format.unitRoundoff = fmt.rho := by
    cases fmt with
    | binary32 => exact fp32_parameters.1
    | binary64 => exact fp64_parameters.1
  obtain ⟨p,q,r,hp,hq,hr,_,_,_,_,_,_,_⟩ :=
    SegmentCoordinates.segment_geometry I X0.decode X1.decode Y0.decode Y1.decode
      hadm.1 X0.bound X1.bound Y0.bound Y1.bound b.rho b.eta b.linear
  have conv {w : Vec3 I} {v : Fin 3 → ℚ} (hv : ∀ i, value? I (w i) = some (v i)) :
      realVec v = decodeVec I w := by
    ext i
    simp [realVec, decodeVec, real_decode I (hv i)]
  have heP := WordGeometryTransfer.difference_error I X1.decode X0.decode hp hadm.1 X1.bound X0.bound b.rho b.eta b.linear
  have heQ := WordGeometryTransfer.difference_error I Y1.decode Y0.decode hq hadm.1 Y1.bound Y0.bound b.rho b.eta b.linear
  have heR := WordGeometryTransfer.difference_error I Y0.decode X0.decode hr hadm.1 Y0.bound X0.bound b.rho b.eta b.linear
  simp only [conv hp,conv hq,conv hr,conv X0.decode,conv X1.decode,conv Y0.decode,conv Y1.decode,hrho] at heP heQ heR
  let P := decodeVec I (vsub I (x 1) (x 0))
  let Q := decodeVec I (vsub I (y 1) (y 0))
  let R := decodeVec I (vsub I (y 0) (x 0))
  let P0 := decodeVec I (x 1)-decodeVec I (x 0)
  let Q0 := decodeVec I (y 1)-decodeVec I (y 0)
  let R0 := decodeVec I (y 0)-decodeVec I (x 0)
  let S := fmt.rho*((7/2)*L)
  have hS0 : 0 ≤ S := by dsimp [S]; exact mul_nonneg fmt.rho_nonneg (by linarith [hadm.1])
  have hS : 0 < S := by
    have hL : 0 < L := by
      have hH : 0 < fourthRoot fmt.leastNormal := by
        unfold fourthRoot
        apply Real.sqrt_pos.mpr
        apply Real.sqrt_pos.mpr
        cases fmt <;> norm_num [Format.leastNormal]
      linarith
    dsimp [S]; rw [← hrho]; exact mul_pos I.format.unitRoundoff_pos (by positivity)
  have he : ‖(R+t•Q-s•P)-(R0+t•Q0-s•P0)‖ ≤ 3*S := by
    have hid : (R+t•Q-s•P)-(R0+t•Q0-s•P0) = (R-R0)+t•(Q-Q0)-s•(P-P0) := by module
    rw [hid]
    have h1 := norm_add_le (R-R0) (t•(Q-Q0))
    have h2 := norm_sub_le ((R-R0)+t•(Q-Q0)) (s•(P-P0))
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1] at h1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1] at h2
    have h3 := mul_le_mul ht.2 heQ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have h4 := mul_le_mul hs.2 heP (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    change t*‖Q-Q0‖ ≤ 1*S at h3
    change s*‖P-P0‖ ≤ 1*S at h4
    change ‖R-R0‖ ≤ S at heR
    nlinarith only [h1,h2,h3,h4,heR]
  have hn : ‖R+t•Q-s•P‖ ≤ d+3*S := by
    have hh := norm_le_norm_add_norm_sub (R0+t•Q0-s•P0) (R+t•Q-s•P)
    rw [norm_sub_rev (R+t•Q-s•P) (R0+t•Q0-s•P0)] at he
    exact hh.trans (add_le_add hw he)
  have hu := common_witness fmt hadm hlarge hs ht (by positivity : 0 ≤ d+3*S) hn
  obtain ⟨a,ha,hbound⟩ := hu
  refine ⟨a,ha,?_⟩
  have hF : F 3+3.55 ≤ (19:ℝ) := by
    have hj : J 3.17 3 ≤ (12.52:ℝ) := by
      have hh : hypot (3+3.17) 7.02 ≤ (9.35:ℝ) := hypot_le (by norm_num) (by norm_num)
      dsimp [J]; linarith
    have hf : F 3 ≤ (15.1:ℝ) := hypot_le_of_le (J_nonneg (by norm_num)) hj (by norm_num) (by norm_num)
    linarith
  have hh := F_add_le (z := (3:ℝ)) (t := d/S) (by norm_num) (div_nonneg hd hS0)
  have hid : (d+3*S)/S = 3+d/S := by field_simp; ring
  change Real.sqrt (a:ℝ) ≤ S*F ((d+3*S)/S)+3.55*fmt.rho*((7/2)*L)+6*fourthRoot fmt.leastSubnormal at hbound
  rw [hid] at hbound
  have hm := mul_le_mul_of_nonneg_left hh hS0
  have hm' := mul_le_mul_of_nonneg_left hF hS0
  have hc : S*(d/S)=d := mul_div_cancel₀ d (ne_of_gt hS)
  dsimp [S] at *
  nlinarith only [hbound,hm,hm',hc]

theorem large_upper (fmt : DistanceAccuracy.Format)
    {x y : Segment fmt.interchange} {L : ℝ}
    (hadm : Geometry.admissible fmt.interchange (.segment x) (.segment y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L) :
    Upper fmt.interchange (Geometry.distance fmt.interchange (.segment x) (.segment y)+
      19*fmt.rho*((7/2)*L)+6*fourthRoot fmt.leastSubnormal)
      (segmentSegment fmt.interchange x y).q := by
  obtain ⟨s,t,hs,ht,heq⟩ := Geometry.closest_segments fmt.interchange x y
  apply original_witness fmt hadm hlarge hs ht (Geometry.distance_nonneg _ _ _)
  exact heq.ge

/-- End-to-end claim 4 for two segments, including all degeneracies and scales. -/
theorem accuracy (fmt : DistanceAccuracy.Format)
    (x y : Segment fmt.interchange) (L : ℝ)
    (hadm : Geometry.admissible fmt.interchange (.segment x) (.segment y) L) :
    ∃ q : ℝ, fmt.interchange.decode? (evaluate fmt.interchange (.segment x) (.segment y)).q = some q ∧
      |Real.sqrt q-Geometry.distance fmt.interchange (.segment x) (.segment y)| ≤
        64*(2*fmt.interchange.format.unitRoundoff)*L+fourthRoot fmt.interchange.format.minNormal := by
  have hrho : fmt.interchange.format.unitRoundoff = fmt.rho := by
    cases fmt with
    | binary32 => exact fp32_parameters.1
    | binary64 => exact fp64_parameters.1
  have hn : fmt.interchange.format.minNormal = fmt.leastNormal := by
    cases fmt with
    | binary32 => exact fp32_parameters.2.1
    | binary64 => exact fp64_parameters.2.1
  by_cases hlarge : fourthRoot fmt.leastNormal/64 ≤ L
  · obtain ⟨q,hq,hb⟩ := large_upper fmt hadm hlarge
    obtain ⟨v,hv,_,hlo⟩ := EvaluateLower.large_lower fmt (.segment x) (.segment y) L hadm hlarge
    have hqr : fmt.interchange.decode? (evaluate fmt.interchange (.segment x) (.segment y)).q = some (q:ℝ) :=
      real_decode fmt.interchange hq
    have heq : v = (q:ℝ) := Option.some.inj (hv.symm.trans hqr)
    subst v
    refine ⟨q,hqr,abs_le.mpr ⟨?_,?_⟩⟩
    · have hm := mul_nonneg fmt.interchange.format.unitRoundoff_pos.le hadm.1
      have hh := fourthRoot_nonneg fmt.interchange.format.minNormal
      nlinarith only [hlo,hm,hh]
    · rw [hrho,hn]
      have hm := mul_nonneg fmt.rho_nonneg hadm.1
      have hh := fourthRoot_nonneg fmt.leastSubnormal
      have hbudget := fmt.underflow_budget
      nlinarith only [hb,hm,hh,hbudget]
  · obtain ⟨q,hq,_,hb⟩ := EvaluateLower.small_accuracy fmt (.segment x) (.segment y) L hadm (le_of_not_ge hlarge)
    refine ⟨q,hq,?_⟩
    rw [hn]
    have hm := mul_nonneg fmt.interchange.format.unitRoundoff_pos.le hadm.1
    nlinarith only [hb,hm]

end DistanceAccuracy.SegmentUpper

import DistanceAccuracy.SegmentCore
import DistanceAccuracy.CrossReducedAdmissible
import DistanceAccuracy.InteriorCandidateUpper
import DistanceAccuracy.LocalProjectionUpper
import DistanceAccuracy.GeometryCoverage

namespace DistanceAccuracy.SegmentKernelUpper
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds
open DistanceAccuracy.Determinant ProjectionRounding UpperSelection
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option exponentiation.threshold 2048

private lemma upper_mono (I : Interchange) {a b : ℝ} {w : I.Word}
    (h : Upper I a w) (hab : a ≤ b) : Upper I b w := by
  obtain ⟨q,hq,hb⟩ := h
  exact ⟨q,hq,hb.trans hab⟩

/-- Sharp nonlinear segment-kernel envelope for every feasible witness in the
common rounded geometry. It includes every degenerate first/second direction. -/
theorem kernel_upper (fmt : DistanceAccuracy.Format)
    {Pw Qw Rw : Vec3 fmt.interchange} {p q r : Fin 3 → ℚ} {L s₀ t₀ d : ℝ}
    (hP : ∀ i, value? fmt.interchange (Pw i) = some (p i))
    (hQ : ∀ i, value? fmt.interchange (Qw i) = some (q i))
    (hR : ∀ i, value? fmt.interchange (Rw i) = some (r i))
    (hL0 : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L)
    (hpD : ‖realVec p‖ ≤ (7/2)*L) (hqD : ‖realVec q‖ ≤ (7/2)*L) (hrD : ‖realVec r‖ ≤ (7/2)*L)
    (hpC : ∀ i, |(p i:ℝ)| ≤ ((7/2)*L)/Real.sqrt 3)
    (hqC : ∀ i, |(q i:ℝ)| ≤ ((7/2)*L)/Real.sqrt 3)
    (hrC : ∀ i, |(r i:ℝ)| ≤ ((7/2)*L)/Real.sqrt 3)
    (hgeo : ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      ‖realVec r+t•realVec q-s•realVec p‖ ≤ (7/2)*L)
    (hs₀ : s₀ ∈ Set.Icc (0:ℝ) 1) (ht₀ : t₀ ∈ Set.Icc (0:ℝ) 1) (hd : 0 ≤ d)
    (hwitness : ‖realVec r+t₀•realVec q-s₀•realVec p‖ ≤ d) :
    Upper fmt.interchange (fmt.rho*((7/2)*L)*F (d/(fmt.rho*((7/2)*L)))+
      3.55*fmt.rho*((7/2)*L)+6*fourthRoot fmt.leastSubnormal)
      (SegmentCore.core fmt.interchange Pw Qw Rw).q := by
  let I := fmt.interchange
  let D : ℝ := (7/2)*L
  let S := fmt.rho*D
  let h := fourthRoot fmt.leastSubnormal
  have hρeq : I.format.unitRoundoff = fmt.rho := by
    cases fmt with
    | binary32 => exact fp32_parameters.1
    | binary64 => exact fp64_parameters.1
  have hHpos : 0 < fourthRoot fmt.leastNormal := by
    unfold fourthRoot
    apply Real.sqrt_pos.mpr
    apply Real.sqrt_pos.mpr
    cases fmt <;> norm_num [DistanceAccuracy.Format.leastNormal]
  have hLpos : 0 < L := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hS : 0 < S := by dsimp [S]; rw [← hρeq]; exact mul_pos I.format.unitRoundoff_pos hD
  have hh : 0 ≤ h := fourthRoot_nonneg _
  have hDL : D ≤ 9*L := by dsimp [D]; linarith
  have hone : value? I (one I) = some 1 := by
    cases fmt with
    | binary32 => exact one_fp32
    | binary64 => exact one_fp64
  have hRQ : ‖realVec r+realVec q‖ ≤ D := by simpa using hgeo 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hRP : ‖realVec r-realVec p‖ ≤ D := by simpa using hgeo 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hRPQ : ‖(realVec r-realVec p)+realVec q‖ ≤ D := by
    convert hgeo 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1
    congr 1; module
  have h0 (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
      Upper I (hypot ‖realVec r+v•realVec q‖ (8.38*S)+2.54*S+2*h) (SegmentCore.endpoint0 I Pw Qw Rw).q := by
    simpa [show (419/50:ℝ) = 8.38 by norm_num, show (127/50:ℝ) = 2.54 by norm_num, SegmentCore.endpoint0, IEEEAlgorithm.make, S, h, I, mul_assoc] using
      direct_candidate_upper fmt hone hQ hR hL0 hadm hDL hqD hrD hRQ hqC hrC hv0 hv1
  have h1 (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
      Upper I (hypot ‖(realVec r-realVec p)+v•realVec q‖ (8.38*S)+3.54*S+2*h) (SegmentCore.endpoint1 I Pw Qw Rw).q := by
    simpa [show (419/50:ℝ) = 8.38 by norm_num, show (177/50:ℝ) = 3.54 by norm_num, SegmentCore.endpoint1, IEEEAlgorithm.make, S, h, I, mul_assoc] using
      endpoint_candidate_upper fmt hone hP hQ hR hL0 hadm hDL hpD hqD hrD hRP hRPQ hpC hqC hrC hv0 hv1
  have hi : UpperSelection.Finite I (SegmentCore.inside I Pw Qw Rw).q := by
    obtain ⟨t,ht,ht0,ht1⟩ := clamp01nan_bounded I hone
      (IEEEAlgorithm.div I (neg I (dot3 I (cross3 I Pw Qw) (cross3 I Pw Rw))) (dot3 I (cross3 I Pw Qw) (cross3 I Pw Qw)))
    exact interior_candidate_finite fmt hone hP hQ hR ht hD.le hadm hDL
      (fun s hs0 hs1 => hgeo s t hs0 hs1 (by exact_mod_cast ht0) (by exact_mod_cast ht1))
  have hscaled : hypot (S*J 3.17 (d/S)) (8.38*S) = S*F (d/S) := by
    have hh := hypot_scale (a := J 3.17 (d/S)) (b := (8.38:ℝ)) hS.le
    simpa only [F,mul_comm] using hh
  have hJd : d ≤ S*J 3.17 (d/S) := by
    have h := mul_le_mul_of_nonneg_left (le_hypot (d/S+3.17) (7.02:ℝ)) hS.le
    have heq : S*(d/S+3.17)=d+3.17*S := by field_simp <;> ring
    rw [heq] at h
    dsimp [J]
    nlinarith only [h,hS.le]
  apply SegmentCore.upper I ((h0 0 (by norm_num) (by norm_num)).finite I)
    ((h1 0 (by norm_num) (by norm_num)).finite I) hi
  by_cases hshort : ‖realVec p‖ ≤ h
  · left
    have hnorm : ‖realVec r+t₀•realVec q‖ ≤ d+h := by
      have hid : realVec r+t₀•realVec q = (realVec r+t₀•realVec q-s₀•realVec p)+s₀•realVec p := by module
      rw [hid]
      have hn := norm_add_le (realVec r+t₀•realVec q-s₀•realVec p) (s₀•realVec p)
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs₀.1] at hn
      have hp := mul_le_mul hs₀.2 hshort (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      nlinarith only [hn,hwitness,hp]
    apply upper_mono I (h0 t₀ ht₀.1 ht₀.2)
    have hmono := hypot_mono (norm_nonneg _) hnorm (b := 8.38*S)
    have hadd := hypot_add_le (b := 8.38*S) hd hh
    have hj := hypot_mono hd hJd (b := 8.38*S)
    rw [hscaled] at hj
    dsimp [S, D, h] at *
    nlinarith only [hmono,hadd,hj,hS.le,hh]
  · have hA : h < ‖realVec p‖ := lt_of_not_ge hshort
    have hw : ‖GeometryCoverage.residual (realVec r) (realVec p) (realVec q) (-s₀) t₀‖ ≤ d := by
      convert hwitness using 1
      congr 1; dsimp [GeometryCoverage.residual]; module
    obtain ⟨t,ht,ht0,ht1,htB⟩ := PointProjection.cross_reduced_admissible fmt false hP hQ hR hL0 hadm hlarge hA
      hpD hqD hrD hpC hqC hrC hd ht₀.1 ht₀.2 hw
    let u := -LineReduction.parameter (realVec p) (realVec r) (realVec q) (t:ℝ)
    let B := S*J 3.17 (d/S)+4*h+(3/1000000)*S
    have ht0r : (0:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht0
    have ht1r : (t:ℝ) ≤ 1 := by exact_mod_cast ht1
    have hline : ‖GeometryCoverage.residual (realVec r) (-realVec p) (realVec q) u (t:ℝ)‖ ≤ B := by
      convert htB using 1
      · congr 1; dsimp [GeometryCoverage.residual,u]; module
      · simp only [B, S, D, h, PointProjection.crossCoefficient, Bool.false_eq_true, ↓reduceIte]
        norm_num only
        ring
    have hB0 : 0 ≤ B := by dsimp [B]; exact add_nonneg (add_nonneg (mul_nonneg hS.le (J_nonneg (by norm_num))) (by positivity)) (by positivity)
    have hBd : d ≤ B := by dsimp [B]; nlinarith only [hJd,hh,hS.le]
    have hBF : hypot B (8.38*S) ≤ S*F (d/S)+4*h+(3/1000000)*S := by
      have h := hypot_add_le (a := S*J 3.17 (d/S)) (b := 8.38*S)
        (mul_nonneg hS.le (J_nonneg (by norm_num))) (show 0 ≤ 4*h+(3/1000000)*S by positivity)
      rw [hscaled] at h
      simpa only [B,add_assoc] using h
    by_cases hin : u ∈ Set.Icc (0:ℝ) 1
    · right; right
      have hiu := interior_candidate_upper fmt hone hP hQ hR ht ht0 ht1 hL0 hadm hA hDL hpD hqD hrD
        (fun s hs0 hs1 => hgeo s t hs0 hs1 ht0r ht1r) hpC hqC hrC hin.1 hin.2
      have hn : ‖realVec r+(t:ℝ)•realVec q-u•realVec p‖ ≤ B := by
        convert hline using 1
        congr 1; dsimp [GeometryCoverage.residual]; module
      rw [hρeq] at hiu
      norm_num only at hiu
      simp only [mul_assoc] at hiu
      apply upper_mono I hiu
      have hm := hypot_mono (norm_nonneg _) hn (b := 8.38*S)
      norm_num only at hm
      simp only [S, mul_assoc] at hm
      dsimp [S, D, h] at *
      nlinarith only [hm,hBF,hS.le,hh]
    · have hout : u ≤ 0 ∨ 1 ≤ u := by
        simp only [Set.mem_Icc,not_and_or,not_le] at hin
        exact hin.imp le_of_lt le_of_lt
      have hw' : ‖GeometryCoverage.residual (realVec r) (-realVec p) (realVec q) s₀ t₀‖ ≤ B := by
        have hn : GeometryCoverage.residual (realVec r) (-realVec p) (realVec q) s₀ t₀ =
            realVec r+t₀•realVec q-s₀•realVec p := by dsimp [GeometryCoverage.residual]; module
        rw [hn]; exact hwitness.trans hBd
      obtain ⟨s',t',hs',ht',hn⟩ := GeometryCoverage.segment_boundary_witness hs₀ ht₀ ⟨ht0r,ht1r⟩ hout hw' hline
      rcases hs' with rfl | rfl
      · left
        have hn' : ‖realVec r+t'•realVec q‖ ≤ B := by simpa [GeometryCoverage.residual] using hn
        apply upper_mono I (h0 t' ht'.1 ht'.2)
        have hm := hypot_mono (norm_nonneg _) hn' (b := 8.38*S)
        dsimp [S, D, h] at *
        nlinarith only [hm,hBF,hS.le,hh]
      · right; left
        have hn' : ‖(realVec r-realVec p)+t'•realVec q‖ ≤ B := by
          convert hn using 1
          congr 1; dsimp [GeometryCoverage.residual]; module
        apply upper_mono I (h1 t' ht'.1 ht'.2)
        have hm := hypot_mono (norm_nonneg _) hn' (b := 8.38*S)
        dsimp [S, D, h] at *
        nlinarith only [hm,hBF,hS.le,hh]

end DistanceAccuracy.SegmentKernelUpper

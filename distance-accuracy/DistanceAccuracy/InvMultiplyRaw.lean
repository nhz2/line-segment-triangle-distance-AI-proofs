import DistanceAccuracy.InvMultiplyAdmissible
import DistanceAccuracy.InvMultiplyEnvelope
import DistanceAccuracy.InvMultiplyCore
import DistanceAccuracy.CrossReducedAdmissible
import DistanceAccuracy.InteriorCandidateUpper
namespace DistanceAccuracy.InvMultiplyRaw
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds
open DistanceAccuracy.Determinant ProjectionRounding InvProjectionRounding
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

lemma parameter_change (P Q R : E3) {s t u v : ℝ} :
    ‖R+t•Q-s•P‖ ≤ ‖R+v•Q-u•P‖+|s-u| * ‖P‖+|t-v| * ‖Q‖ := by
  have he : R+t•Q-s•P = (R+v•Q-u•P)-(s-u)•P+(t-v)•Q := by module
  have h1 := norm_sub_le (R+v•Q-u•P) ((s-u)•P)
  have h2 := norm_add_le ((R+v•Q-u•P)-(s-u)•P) ((t-v)•Q)
  rw [norm_smul,Real.norm_eq_abs] at h1 h2
  rw [he]
  linarith
lemma interval_span {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |s-t| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [hs.2,ht.1]⟩

/-- Raw residual of the actual three word solves, before its two vector FMAs
and stored norm. Both short-direction cases are included. -/
theorem raw_upper (fmt : DistanceAccuracy.Format)
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
    ∃ s t : ℚ,
      value? fmt.interchange (InvMultiplyCore.second fmt.interchange Pw Qw Rw) = some s ∧
      value? fmt.interchange (InvMultiplyCore.third fmt.interchange Pw Qw Rw) = some t ∧
      0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧
      ‖realVec r+(t:ℝ)•realVec q-(s:ℝ)•realVec p‖ ≤
        (fmt.rho*((7/2)*L))*GI (d/(fmt.rho*((7/2)*L)))+4*fourthRoot fmt.leastSubnormal+
        40*Real.sqrt fmt.leastSubnormal*(1+(7/2)*L)+(3/1000000)*fmt.rho*((7/2)*L) := by
  let I := fmt.interchange
  let D : ℝ := (7/2)*L
  let S := fmt.rho*D
  let h := fourthRoot fmt.leastSubnormal
  let A := Real.sqrt fmt.leastSubnormal*(1+D)
  let K := (9.38:ℝ)*S
  have hρ : I.format.unitRoundoff = fmt.rho := by cases fmt <;> first | exact fp32_parameters.1 | exact fp64_parameters.1
  have hη : I.format.minSubnormal = fmt.leastSubnormal := by cases fmt <;> first | exact fp32_parameters.2.2 | exact fp64_parameters.2.2
  have hH : 0 < fourthRoot fmt.leastNormal := by
    unfold fourthRoot
    apply Real.sqrt_pos.mpr
    apply Real.sqrt_pos.mpr
    cases fmt <;> norm_num [Format.leastNormal]
  have hD : 0 < D := by dsimp [D]; linarith
  have hρp : 0 < fmt.rho := by rw [←hρ]; exact I.format.unitRoundoff_pos
  have hS : 0 < S := mul_pos hρp hD
  have hh : 0 ≤ h := fourthRoot_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hDL : D ≤ 9*L := by dsimp [D]; linarith
  have hone : value? I (one I) = some 1 := by cases fmt <;> first | exact one_fp32 | exact one_fp64
  obtain ⟨v,hv,hv0,hv1⟩ := clamp01nan_bounded I hone
    (div I (neg I (dot3 I (cross3 I Pw Qw) (cross3 I Pw Rw))) (dot3 I (cross3 I Pw Qw) (cross3 I Pw Qw)))
  change value? I (InvMultiplyCore.initial I Pw Qw Rw) = some v at hv
  obtain ⟨s,hs,hs0,hs1⟩ := clamp01nan_bounded I hone
    (InvProjectionRounding.rdiv I (fma I (InvMultiplyCore.initial I Pw Qw Rw) (dot3 I Pw Qw) (dot3 I Pw Rw)) (dot3 I Pw Pw))
  change value? I (InvMultiplyCore.second I Pw Qw Rw) = some s at hs
  obtain ⟨t,ht,ht0,ht1⟩ := clamp01nan_bounded I hone
    (InvProjectionRounding.rdiv I (fma I (InvMultiplyCore.second I Pw Qw Rw) (dot3 I Pw Qw) (neg I (dot3 I Qw Rw))) (dot3 I Qw Qw))
  change value? I (InvMultiplyCore.third I Pw Qw Rw) = some t at ht
  have hsr : (s:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by exact_mod_cast hs0,by exact_mod_cast hs1⟩
  have htr : (t:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by exact_mod_cast ht0,by exact_mod_cast ht1⟩
  have hvr : (v:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by exact_mod_cast hv0,by exact_mod_cast hv1⟩
  refine ⟨s,t,hs,ht,hs0,hs1,ht0,ht1,?_⟩
  suffices hout : ‖realVec r+(t:ℝ)•realVec q-(s:ℝ)•realVec p‖ ≤ S*GI (d/S)+4*h+40*A+(3/1000000)*fmt.rho*D by
    simpa only [S,D,h,A,mul_assoc] using hout
  have hscaled : hypot (S*F9 (d/S)) K = S*GI (d/S) := by
    simpa only [K,GI,mul_comm] using (hypot_scale (a := F9 (d/S)) (b := (9.38:ℝ)) hS.le)
  have hdF : d ≤ S*F9 (d/S) := by
    have h := mul_le_mul_of_nonneg_left (F9_ge_input (div_nonneg hd hS.le)) hS.le
    simpa only [mul_div_cancel₀ d hS.ne'] using h
  have hdG : hypot d K ≤ S*GI (d/S) := by
    rw [←hscaled]; exact hypot_mono hd hdF
  have changeP (s' : ℝ) (hs' : s' ∈ Set.Icc (0:ℝ) 1) (hp : ‖realVec p‖ ≤ h) :
      ‖realVec r+t₀•realVec q-s'•realVec p‖ ≤ d+h := by
    have hc := parameter_change (realVec p) (realVec q) (realVec r) (s:=s') (t:=t₀) (u:=s₀) (v:=t₀)
    have hm := mul_le_mul (interval_span hs' hs₀) hp (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    simp only [sub_self,abs_zero,zero_mul,add_zero] at hc
    linarith
  have third (hq : h < ‖realVec q‖) (w : ℝ) (hw : w ∈ Set.Icc (0:ℝ) 1) :
      ‖realVec r+(t:ℝ)•realVec q-(s:ℝ)•realVec p‖ ≤
        hypot ‖realVec r+w•realVec q-(s:ℝ)•realVec p‖ K+8*A := by
    have hk : ‖realVec r-(s:ℝ)•realVec p‖ ≤ D := by simpa using hgeo s 0 hsr.1 hsr.2 (by norm_num) (by norm_num)
    obtain ⟨t',ht',_,_,hloss⟩ := InvProjectionRounding.third_solve_admissible fmt hone hP hQ hR hs hs0 hs1 hL0 hadm hq hDL hpD hqD hrD hk hpC hqC hrC
    have htEq : t'=t := Option.some.inj (ht'.symm.trans ht)
    subst t'
    have hn := inv_projection_norm_budget I.format.unitRoundoff_pos.le
      (show 0 ≤ I.format.minSubnormal by unfold FP.IEEE.Format.minSubnormal; positivity)
      hD.le (norm_nonneg _) hqD (norm_nonneg _) (hloss w hw.1 hw.2)
    simpa only [hρ,hη,K,A,S,mul_assoc,show (469/50:ℝ)=9.38 by norm_num] using hn
  by_cases hqshort : ‖realVec q‖ ≤ h
  · by_cases hpshort : ‖realVec p‖ ≤ h
    · have hc := parameter_change (realVec p) (realVec q) (realVec r) (s:=(s:ℝ)) (t:=(t:ℝ)) (u:=s₀) (v:=t₀)
      have hmP := mul_le_mul (interval_span hsr hs₀) hpshort (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      have hmQ := mul_le_mul (interval_span htr ht₀) hqshort (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      have hbase := le_hypot d K
      dsimp [S] at *
      nlinarith only [hc,hmP,hmQ,hwitness,hbase,hdG,hh,hA,hS.le]
    · have hp : h < ‖realVec p‖ := lt_of_not_ge hpshort
      have hk : ‖realVec r+(v:ℝ)•realVec q‖ ≤ D := by simpa using hgeo 0 v (by norm_num) (by norm_num) hvr.1 hvr.2
      obtain ⟨s',hs',_,_,hloss⟩ := InvProjectionRounding.second_solve_admissible fmt hone hP hQ hR hv hv0 hv1 hL0 hadm hp hDL hpD hqD hrD hk hpC hqC hrC
      have hsEq : s'=s := Option.some.inj (hs'.symm.trans hs)
      subst s'
      have hn := inv_projection_norm_budget I.format.unitRoundoff_pos.le
        (show 0 ≤ I.format.minSubnormal by unfold FP.IEEE.Format.minSubnormal; positivity)
        hD.le (norm_nonneg _) hpD (norm_nonneg _) (hloss s₀ hs₀.1 hs₀.2)
      have hid (a : ℝ) : (realVec r+(v:ℝ)•realVec q)+a•(-realVec p) = realVec r+(v:ℝ)•realVec q-a•realVec p := by module
      simp only [hid,hρ,hη,show (469/50:ℝ)=9.38 by norm_num] at hn
      have hc := parameter_change (realVec p) (realVec q) (realVec r) (s:=s₀) (t:=(v:ℝ)) (u:=s₀) (v:=t₀)
      have hm := mul_le_mul (interval_span hvr ht₀) hqshort (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      simp only [sub_self,abs_zero,zero_mul,add_zero] at hc
      have hw : ‖realVec r+(v:ℝ)•realVec q-s₀•realVec p‖ ≤ d+h := by linarith
      have hmono := hypot_mono (norm_nonneg _) hw (b:=K)
      have hadd := hypot_add_le (b:=K) hd hh
      have hc' := parameter_change (realVec p) (realVec q) (realVec r) (s:=(s:ℝ)) (t:=(t:ℝ)) (u:=(s:ℝ)) (v:=(v:ℝ))
      have hm' := mul_le_mul (interval_span htr hvr) hqshort (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      simp only [sub_self,abs_zero,zero_mul,add_zero] at hc'
      simp only [K,A,S,D,mul_assoc] at *
      nlinarith only [hn,hmono,hadd,hc',hm',hdG,hh,hA,hS.le]
  · have hq : h < ‖realVec q‖ := lt_of_not_ge hqshort
    by_cases hpshort : ‖realVec p‖ ≤ h
    · have hn := third hq t₀ ht₀
      have hmono := hypot_mono (norm_nonneg _) (changeP s hsr hpshort) (b:=K)
      have hadd := hypot_add_le (b:=K) hd hh
      dsimp [S] at *
      nlinarith only [hn,hmono,hadd,hdG,hh,hA,hS.le]
    · have hp : h < ‖realVec p‖ := lt_of_not_ge hpshort
      have hw : ‖GeometryCoverage.residual (realVec r) (realVec p) (realVec q) (-s₀) t₀‖ ≤ d := by
        convert hwitness using 1; congr 1; dsimp [GeometryCoverage.residual]; module
      obtain ⟨v',hv',_,_,hline⟩ := PointProjection.cross_reduced_admissible fmt false hP hQ hR hL0 hadm hlarge hp hpD hqD hrD hpC hqC hrC hd ht₀.1 ht₀.2 hw
      have hvEq : v'=v := Option.some.inj (hv'.symm.trans hv)
      subst v'
      let B := S*J 3.17 (d/S)+4*h+(3/1000000)*S
      have hline' : ‖GeometryCoverage.residual (realVec r) (-realVec p) (realVec q)
          (LineReduction.parameter (-realVec p) (realVec r) (realVec q) (v:ℝ)) (v:ℝ)‖ ≤ B := by
        simpa [LineReduction.parameter,GeometryCoverage.residual,inner_neg_left,neg_div,neg_smul,
          B,S,D,h,PointProjection.crossCoefficient,mul_assoc] using hline
      have hBd : d ≤ B := by
        have h0 := mul_le_mul_of_nonneg_left (le_hypot (d/S+3.17) 7.02) hS.le
        have heq : S*(d/S)=d := mul_div_cancel₀ d hS.ne'
        dsimp [B,J]
        nlinarith only [h0,heq,hh,hS.le]
      have hB : 0 ≤ B := hd.trans hBd
      have hk : ‖realVec r+(v:ℝ)•realVec q‖ ≤ D := by simpa using hgeo 0 v (by norm_num) (by norm_num) hvr.1 hvr.2
      obtain ⟨s',hs',_,_,hdich⟩ := InvProjectionRounding.second_line_or_endpoint fmt hone hP hQ hR hv hv0 hv1 hL0 hadm hp hDL hpD hqD hrD hk hpC hqC hrC
      have hsEq : s'=s := Option.some.inj (hs'.symm.trans hs)
      subst s'
      have herr := third_absolute_gradient hp hpD
      have hc : ((s:ℝ)=0 ∧ LineReduction.parameter (-realVec p) (realVec r) (realVec q) (v:ℝ)≤0) ∨
          ((s:ℝ)=1 ∧ 1≤LineReduction.parameter (-realVec p) (realVec r) (realVec q) (v:ℝ)) ∨
          |(s:ℝ)-LineReduction.parameter (-realVec p) (realVec r) (realVec q) (v:ℝ)| * ‖-realVec p‖ ≤ K+32*A := by
        rcases hdich with he | he | he
        · exact Or.inl he
        · exact Or.inr (Or.inl he)
        · right; right
          have hρ' : fmt.interchange.format.unitRoundoff = fmt.rho := hρ
          have hη' : fmt.interchange.format.minSubnormal = fmt.leastSubnormal := hη
          simp only [hρ',hη',norm_neg] at he ⊢
          simp only [K,A,S,D,mul_assoc,show (469/50:ℝ)=9.38 by norm_num] at he herr ⊢
          linarith
      have hw' : ‖GeometryCoverage.residual (realVec r) (-realVec p) (realVec q) s₀ t₀‖ ≤ B := by
        have hid : GeometryCoverage.residual (realVec r) (-realVec p) (realVec q) s₀ t₀ = realVec r+t₀•realVec q-s₀•realVec p := by dsimp [GeometryCoverage.residual]; module
        rw [hid]; exact hwitness.trans hBd
      obtain ⟨w,hw,hwn⟩ := ThreeDivideGeometry.rounded_witness
        (neg_ne_zero.mpr (norm_pos_iff.mp ((fourthRoot_nonneg _).trans_lt hp))) hs₀ ht₀ hvr hB hK (show 0 ≤ 32*A by positivity) hw' hline' hc
      have hwn' : ‖realVec r+w•realVec q-(s:ℝ)•realVec p‖ ≤ hypot B K+32*A := by
        convert hwn using 1; congr 1; dsimp [GeometryCoverage.residual]; module
      have hn := third hq w hw
      have hmono := hypot_mono (norm_nonneg _) hwn' (b:=K)
      have hadd := hypot_add_le (a:=hypot B K) (b:=K) (hypot_nonneg _ _) (show 0 ≤ 32*A by positivity)
      have hBupper : hypot B K ≤ S*F9 (d/S)+4*h+(3/1000000)*S := by
        have hh0 : 0 ≤ S*J 3.17 (d/S) := mul_nonneg hS.le (J_nonneg (by norm_num))
        have h := hypot_add_le (a:=S*J 3.17 (d/S)) (b:=K) hh0 (show 0 ≤ 4*h+(3/1000000)*S by positivity)
        have he : hypot (S*J 3.17 (d/S)) K = S*F9 (d/S) := by
          simpa only [K,F9,mul_comm] using (hypot_scale (a:=J 3.17 (d/S)) (b:=(9.38:ℝ)) hS.le)
        simpa only [B,add_assoc,he] using h
      have hBmono := hypot_mono (hypot_nonneg B K) hBupper (b:=K)
      have hBadd := hypot_add_le (a:=S*F9 (d/S)) (b:=K)
        (mul_nonneg hS.le (F9_nonneg _)) (show 0 ≤ 4*h+(3/1000000)*S by positivity)
      rw [hscaled] at hBadd
      have hBadd' : hypot (S*F9 (d/S)+4*h+(3/1000000)*S) K ≤ S*GI (d/S)+4*h+(3/1000000)*S := by
        simpa only [add_assoc] using hBadd
      dsimp [S] at *
      nlinarith only [hn,hmono,hadd,hBmono,hBadd']
end DistanceAccuracy.InvMultiplyRaw

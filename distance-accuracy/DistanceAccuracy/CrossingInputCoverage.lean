import DistanceAccuracy.CrossingLocalCoverage
import DistanceAccuracy.CrossingCoordinates
import DistanceAccuracy.CrossingAdmissible
import DistanceAccuracy.EvaluateLower
import DistanceAccuracy.WordGeometryTransfer

namespace DistanceAccuracy.CrossingInputCoverage
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge
open Geometry Determinant UpperSelection
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2048

lemma decoded_eq (I : Interchange) [I.Valid] {w : Vec3 I} {v : Fin 3 → ℚ}
    (hv : ∀ i, value? I (w i)=some (v i)) : realVec v=decodeVec I w := by
  ext i
  simp [realVec,decodeVec,real_decode I (hv i)]

lemma cross_eq (a b : Geometry.E3) : GeometryCoverage.exactCross a b=Determinant.exactCross a b := by
  ext i
  fin_cases i <;> simp [GeometryCoverage.exactCross,Determinant.exactCross,crossProduct]

/-- All pre-crossing local geometry follows from the original bounded words. -/
theorem base_geometry (fmt : Format) {x : Segment fmt.interchange} {y : Triangle fmt.interchange} {L : ℝ}
    (hadm : admissible fmt.interchange (.segment x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64   ≤   L) :
    ∃ e f ap p : Fin 3 → ℚ,
      (∀ i, value? fmt.interchange (vsub fmt.interchange (y 1) (y 0) i)=some (e i)) ∧
      (∀ i, value? fmt.interchange (vsub fmt.interchange (y 2) (y 0) i)=some (f i)) ∧
      (∀ i, value? fmt.interchange (vsub fmt.interchange (y 0) (x 0) i)=some (ap i)) ∧
      (∀ i, value? fmt.interchange (vsub fmt.interchange (x 1) (x 0) i)=some (p i)) ∧
      (∀ i, |(e i:ℝ)|   ≤   ((7/2)*L)/Real.sqrt 3) ∧
      (∀ i, |(f i:ℝ)|   ≤   ((7/2)*L)/Real.sqrt 3) ∧
      (∀ i, |(ap i:ℝ)|   ≤   ((7/2)*L)/Real.sqrt 3) ∧
      (∀ i, |(p i:ℝ)|   ≤   ((7/2)*L)/Real.sqrt 3) ∧
      ‖realVec e‖   ≤   (7/2)*L ∧ ‖realVec f‖   ≤   (7/2)*L ∧
      ‖realVec ap‖   ≤   (7/2)*L ∧ ‖realVec p‖   ≤   (7/2)*L ∧
      (∀ s : ℝ, 0   ≤   s → s   ≤   1 → ‖realVec ap-s • realVec p‖   ≤   (7/2)*L) := by
  let I := fmt.interchange
  let X0 := EvaluateLower.vertex_of_bounded hadm.2.2.1 0
  let X1 := EvaluateLower.vertex_of_bounded hadm.2.2.1 1
  let Y0 := EvaluateLower.vertex_of_bounded hadm.2.2.2 0
  let Y1 := EvaluateLower.vertex_of_bounded hadm.2.2.2 1
  let Y2 := EvaluateLower.vertex_of_bounded hadm.2.2.2 2
  have b := EvaluateLower.format_budget fmt hadm.1 hadm.2.1 hlarge
  obtain ⟨e,f,ap,he,hf,hap,heC,hfC,hapC,heD,hfD,hapD,_,_⟩ :=
    FaceCoordinates.face_geometry I Y0.decode Y1.decode Y2.decode X0.decode hadm.1
      Y0.bound Y1.bound Y2.bound X0.bound b.rho b.eta b.linear
  obtain ⟨p,q,ap',hp,_,hap',hpC,_,_,hpD,_,_,hgeo⟩ :=
    SegmentCoordinates.segment_geometry (x := x) (y := ![y 0,y 0]) I X0.decode X1.decode
      Y0.decode Y0.decode hadm.1 X0.bound X1.bound Y0.bound Y0.bound b.rho b.eta b.linear
  have heq : ap'=ap := funext (fun i => Option.some.inj ((hap' i).symm.trans (hap i)))
  subst ap'
  refine ⟨e,f,ap,p,he,hf,hap,hp,heC,hfC,hapC,hpC,heD,hfD,hapD,hpD,?_⟩
  intro s hs0 hs1
  simpa only [zero_smul,add_zero] using hgeo s 0 hs0 hs1 (by norm_num) (by norm_num)

/-- Actual thick crossing at original bounded inputs, conditional only on
exact geometric witnesses in the common rounded input differences. -/
theorem thick_root (fmt : Format) {x : Segment fmt.interchange} {y : Triangle fmt.interchange}
    {L s₀ u₀ v₀ t : ℝ}
    (hadm : admissible fmt.interchange (.segment x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64   ≤   L)
    (hA : fourthRoot fmt.leastSubnormal < ‖decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0))‖)
    (hfloor : (fourthRoot fmt.leastSubnormal)^2    ≤    ‖GeometryCoverage.exactCross
      (decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0)))
      (decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0)))‖)
    (hthick : 16*fmt.rho*‖decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0))‖*((7/2)*L)    ≤   
      ‖GeometryCoverage.exactCross (decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0)))
        (decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0)))‖)
    (hs₀ : s₀ ∈ Set.Icc (0:ℝ) 1) (hu₀ : 0   ≤   u₀) (hv₀ : 0   ≤   v₀) (huv₀ : u₀+v₀   ≤   1)
    (ht0 : 0   ≤   t) (ht1 : t   ≤   1)
    (hroot : inner ℝ (GeometryCoverage.exactCross
      (decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0)))
      (decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0))))
      (decodeVec fmt.interchange (vsub fmt.interchange (y 0) (x 0))-
        t • decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0)))=0)
    (hwitness : ‖decodeVec fmt.interchange (vsub fmt.interchange (y 0) (x 0))-
      s₀ • decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0))+
      u₀ • decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0))+
      v₀ • decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0))‖   ≤   3*fmt.rho*((7/2)*L)) :
    Upper fmt.interchange (fmt.rho*((7/2)*L)*(V (42/5)+4.54)+6*fourthRoot fmt.leastSubnormal)
      (crossing fmt.interchange x (y 0) (vsub fmt.interchange (y 1) (y 0))
        (vsub fmt.interchange (y 2) (y 0))
        (cross3Accurate fmt.interchange (vsub fmt.interchange (y 1) (y 0))
          (vsub fmt.interchange (y 2) (y 0)))).q ∨
    ∃ s u v : ℝ, s ∈ Set.Icc (0:ℝ) 1 ∧ 0   ≤   u ∧ 0   ≤   v ∧ u+v   ≤   1 ∧
      (u=0 ∨ v=0 ∨ u+v=1) ∧
      ‖decodeVec fmt.interchange (vsub fmt.interchange (y 0) (x 0))-
        s • decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0))+
        u • decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0))+
        v • decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0))‖   ≤   
        fmt.rho*((7/2)*L)*(V (42/5)+1.01)+7*fourthRoot fmt.leastSubnormal := by
  let I := fmt.interchange
  let D : ℝ := (7/2)*L
  let S : ℝ := fmt.rho*D
  let h : ℝ := fourthRoot fmt.leastSubnormal
  have hr : I.format.unitRoundoff=fmt.rho := by cases fmt; exact fp32_parameters.1; exact fp64_parameters.1
  have hrfmt : fmt.interchange.format.unitRoundoff=fmt.rho := hr
  have heta : I.format.minSubnormal=fmt.leastSubnormal := by cases fmt; exact fp32_parameters.2.2; exact fp64_parameters.2.2
  have hone : value? I (one I)=some 1 := by cases fmt; exact OperationBounds.one_fp32; exact OperationBounds.one_fp64
  have hh : 0<h := (FaceRanges.root_bounds fmt).1.trans_le (FaceRanges.root_bounds fmt).2.1
  have hD : 0<D := (hh.trans hA).trans_le (by
    obtain ⟨e,f,ap,p,he,hf,hap,hp,heC,hfC,hapC,hpC,heD,rest⟩ := base_geometry fmt hadm hlarge
    rw [← decoded_eq I he]; exact heD)
  have hS : 0<S := mul_pos (by rw [← hr]; exact I.format.unitRoundoff_pos) hD
  have heta_h : fmt.leastSubnormal   ≤   h := by
    apply le_trans (b := FaceRanges.rootLower fmt) _ (FaceRanges.root_bounds fmt).2.1
    cases fmt <;> norm_num [Format.leastSubnormal,FaceRanges.rootLower]
  obtain ⟨e,f,ap,p,he,hf,hap,hp,heC,hfC,hapC,hpC,heD,hfD,hapD,hpD,hgeo⟩ := base_geometry fmt hadm hlarge
  rw [← decoded_eq I he] at hA hthick
  rw [← decoded_eq I he,← decoded_eq I hf] at hfloor
  rw [← decoded_eq I hf] at hthick
  rw [← decoded_eq I he,← decoded_eq I hf,← decoded_eq I hap,← decoded_eq I hp] at hroot
  rw [← decoded_eq I he,← decoded_eq I hf,← decoded_eq I hap,← decoded_eq I hp] at hwitness
  have hN : GeometryCoverage.exactCross (realVec e) (realVec f)≠0 := by
    apply norm_pos_iff.mp
    exact (sq_pos_of_pos hh).trans_le hfloor
  obtain ⟨s,ax,hs,hax,hs0,hs1,hheight⟩ := CrossingHeight.word_crossing_thick fmt hone he hf hap hp
    hadm.1 hadm.2.1 hD (show D   ≤   9*L by dsimp [D]; linarith [hadm.1])
    (hh.trans hA) heD hfD heC hfC hfloor (by simpa only [hrfmt,D,cross_eq] using hthick)
    hapD hpD hgeo hapC hpC ht0 ht1 hroot
  let X0 := EvaluateLower.vertex_of_bounded hadm.2.2.1 0
  let X1 := EvaluateLower.vertex_of_bounded hadm.2.2.1 1
  let Y0 := EvaluateLower.vertex_of_bounded hadm.2.2.2 0
  let Y1 := EvaluateLower.vertex_of_bounded hadm.2.2.2 1
  let Y2 := EvaluateLower.vertex_of_bounded hadm.2.2.2 2
  have b := EvaluateLower.format_budget fmt hadm.1 hadm.2.1 hlarge
  have hrmax : I.format.unitRoundoff   ≤   1/16777216 := by rw [hr]; have hh := fmt.rho_le; norm_num at hh; exact hh
  obtain ⟨e',f',ax',he',hf',hax',_,_,haxC,_,_,haxD,haxE,haxF,_⟩ :=
    CrossingCoordinates.crossing_face_geometry I Y0.decode Y1.decode Y2.decode X0.decode X1.decode hs hs0 hs1
      hadm.1 Y0.bound Y1.bound Y2.bound X0.bound X1.bound hrmax b.eta b.linear
  have eqe : e'=e := funext (fun i => Option.some.inj ((he' i).symm.trans (he i)))
  have eqf : f'=f := funext (fun i => Option.some.inj ((hf' i).symm.trans (hf i)))
  have eqax : ax'=ax := funext (fun i => Option.some.inj ((hax' i).symm.trans (hax i)))
  subst e'; subst f'; subst ax'
  have hs0r : (0:ℝ)   ≤   (s:ℝ) := by exact_mod_cast hs0
  have hs1r : (s:ℝ)   ≤   1 := by exact_mod_cast hs1
  have hshift := CrossingCoordinates.crossing_anchor_displacement I hap hp hs hax
    (hgeo s hs0r hs1r) (show D<I.format.overflowThreshold by dsimp [D]; linarith [b.linear,hadm.1])
  rw [norm_sub_rev (realVec ax) (realVec ap-(s:ℝ) • realVec p),hr,heta] at hshift
  have hw : ‖realVec ap+s₀ • (-realVec p)+u₀ • realVec e+v₀ • realVec f‖   ≤   
      ((42/5)*S+h)+(S+fmt.leastSubnormal) := by
    simp only [smul_neg,← sub_eq_add_neg]
    change _   ≤   ((42/5)*S+h)+(S+fmt.leastSubnormal)
    dsimp [S,D,h]
    nlinarith [fmt.subnormal_nonneg]
  have hshift' : ‖realVec ap+(s:ℝ) • (-realVec p)-realVec ax‖   ≤   S+fmt.leastSubnormal := by
    simpa only [smul_neg,← sub_eq_add_neg] using hshift
  have hhgt : |inner ℝ (GeometryCoverage.exactCross (realVec e) (realVec f)) (realVec ax)|/
      ‖GeometryCoverage.exactCross (realVec e) (realVec f)‖   ≤   (42/5)*S+h := by
    simpa only [hrfmt,S,h,cross_eq,mul_assoc] using hheight
  have hout := crossing_local_coverage (R₀ := realVec ap) (P₀ := -realVec p) fmt he hf hax
    hadm.1 hadm.2.1 hlarge hA heD hfD haxD haxE haxF heC hfC haxC
    (show 0   ≤   (42/5)*S+h by positivity) hs₀ ⟨hs0r,hs1r⟩ hu₀ hv₀ huv₀ hN hw hshift' hhgt
  have hV := FaceCoverage.scaled_V_plane hS hh.le (show 0   ≤   (42/5)*S+h by positivity)
    (le_refl ((42/5)*S+h))
  rcases hout with ⟨q,hq,hbound⟩ | ⟨ss,u,v,hss,hu,hv,huv,hbd,hbound⟩
  · left
    refine ⟨q,hq,?_⟩
    change _   ≤   S*(V (42/5)+4.54)+6*h
    change _   ≤   S*(V (((42/5)*S+h)/S)+4.532)+5*h at hbound
    nlinarith only [hbound,hV,hS]
  · right
    refine ⟨ss,u,v,hss,hu,hv,huv,hbd,?_⟩
    rw [← decoded_eq I hap,← decoded_eq I hp,← decoded_eq I he,← decoded_eq I hf]
    simp only [smul_neg,← sub_eq_add_neg] at hbound
    change _   ≤   max ((42/5)*S+h) (S*(V (((42/5)*S+h)/S)+0.002)+5*h)+(S+fmt.leastSubnormal) at hbound
    rw [FaceCoverage.crossing_edge_max hS hh.le] at hbound
    change _   ≤   S*(V (42/5)+1.01)+7*h
    nlinarith only [hbound,hV,hS,heta_h]

lemma endpoint_displacement (fmt : Format) {x : Segment fmt.interchange} {y : Triangle fmt.interchange}
    {L : ℝ} {ap p r : Fin 3 → ℚ} (k : Fin 2)
    (hadm : admissible fmt.interchange (.segment x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64   ≤   L)
    (hap : ∀ i, value? fmt.interchange (vsub fmt.interchange (y 0) (x 0) i)=some (ap i))
    (hp : ∀ i, value? fmt.interchange (vsub fmt.interchange (x 1) (x 0) i)=some (p i))
    (hr : ∀ i, value? fmt.interchange (vsub fmt.interchange (y 0) (x k) i)=some (r i)) :
    ‖realVec ap-(k.val:ℝ) • realVec p-realVec r‖   ≤   3*fmt.rho*((7/2)*L) := by
  let I := fmt.interchange
  have hrho : I.format.unitRoundoff=fmt.rho := by cases fmt; exact fp32_parameters.1; exact fp64_parameters.1
  have hS : 0   ≤   fmt.rho*((7/2)*L) := mul_nonneg fmt.rho_nonneg (by linarith [hadm.1])
  fin_cases k
  · have heq : ap=r := funext (fun i => Option.some.inj ((hap i).symm.trans (hr i)))
    simp only [Fin.val_zero,Nat.cast_zero,zero_smul,sub_zero,heq,sub_self,norm_zero]
    linarith
  · let X0 := EvaluateLower.vertex_of_bounded hadm.2.2.1 0
    let X1 := EvaluateLower.vertex_of_bounded hadm.2.2.1 1
    let Y0 := EvaluateLower.vertex_of_bounded hadm.2.2.2 0
    have b := EvaluateLower.format_budget fmt hadm.1 hadm.2.1 hlarge
    have ha := WordGeometryTransfer.difference_error I Y0.decode X0.decode hap hadm.1 Y0.bound X0.bound b.rho b.eta b.linear
    have hp' := WordGeometryTransfer.difference_error I X1.decode X0.decode hp hadm.1 X1.bound X0.bound b.rho b.eta b.linear
    have hr' := WordGeometryTransfer.difference_error I Y0.decode X1.decode hr hadm.1 Y0.bound X1.bound b.rho b.eta b.linear
    have hid : realVec ap-realVec p-realVec r =
        (realVec ap-(realVec Y0.values-realVec X0.values))-
        (realVec p-(realVec X1.values-realVec X0.values))-
        (realVec r-(realVec Y0.values-realVec X1.values)) := by module
    simp only [Fin.val_one,Nat.cast_one,one_smul]
    rw [hid]
    have h1 := norm_sub_le (realVec ap-(realVec Y0.values-realVec X0.values))
      (realVec p-(realVec X1.values-realVec X0.values))
    have h2 := norm_sub_le
      ((realVec ap-(realVec Y0.values-realVec X0.values))-(realVec p-(realVec X1.values-realVec X0.values)))
      (realVec r-(realVec Y0.values-realVec X1.values))
    rw [hrho] at ha hp' hr'
    linarith

theorem endpoint_cover (fmt : Format) {x : Segment fmt.interchange} {y : Triangle fmt.interchange}
    {L s₀ u₀ v₀ : ℝ} (k : Fin 2)
    (hadm : admissible fmt.interchange (.segment x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64   ≤   L)
    (hA : fourthRoot fmt.leastSubnormal < ‖decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0))‖)
    (hN : GeometryCoverage.exactCross
      (decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0)))
      (decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0)))≠0)
    (hs₀ : s₀ ∈ Set.Icc (0:ℝ) 1) (hu₀ : 0   ≤   u₀) (hv₀ : 0   ≤   v₀) (huv₀ : u₀+v₀   ≤   1)
    (hheight : |inner ℝ (GeometryCoverage.exactCross
      (decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0)))
      (decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0))))
      (decodeVec fmt.interchange (vsub fmt.interchange (y 0) (x 0))-
        (k.val:ℝ) • decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0)))|/
      ‖GeometryCoverage.exactCross
      (decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0)))
      (decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0)))‖   ≤   3*fmt.rho*((7/2)*L))
    (hwitness : ‖decodeVec fmt.interchange (vsub fmt.interchange (y 0) (x 0))-
      s₀ • decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0))+
      u₀ • decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0))+
      v₀ • decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0))‖   ≤   3*fmt.rho*((7/2)*L)) :
    Upper fmt.interchange (fmt.rho*((7/2)*L)*(V 6+4.54)+5*fourthRoot fmt.leastSubnormal)
      (face fmt.interchange (vsub fmt.interchange (y 0) (x k))
        (vsub fmt.interchange (y 1) (y 0)) (vsub fmt.interchange (y 2) (y 0))
        (cross3Accurate fmt.interchange (vsub fmt.interchange (y 1) (y 0))
          (vsub fmt.interchange (y 2) (y 0)))).q ∨
    ∃ ss u v : ℝ, ss ∈ Set.Icc (0:ℝ) 1 ∧ 0  ≤  u ∧ 0  ≤  v ∧ u+v  ≤  1 ∧
      (u=0 ∨ v=0 ∨ u+v=1) ∧
      ‖decodeVec fmt.interchange (vsub fmt.interchange (y 0) (x 0))-
        ss • decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0))+
        u • decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0))+
        v • decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0))‖  ≤  
        fmt.rho*((7/2)*L)*(V 6+3.002)+5*fourthRoot fmt.leastSubnormal := by
  let I := fmt.interchange
  let D : ℝ := (7/2)*L
  let S : ℝ := fmt.rho*D
  let h : ℝ := fourthRoot fmt.leastSubnormal
  obtain ⟨e,f,ap,p,he,hf,hap,hp,heC,hfC,hapC,hpC,heD,hfD,hapD,hpD,hgeo⟩ := base_geometry fmt hadm hlarge
  rw [← decoded_eq I he] at hA
  rw [← decoded_eq I he,← decoded_eq I hf] at hN
  rw [← decoded_eq I he,← decoded_eq I hf,← decoded_eq I hap,← decoded_eq I hp] at hheight hwitness
  have hD : 0<D := ((fourthRoot_nonneg _).trans_lt hA).trans_le heD
  have hS : 0<S := mul_pos (by cases fmt <;> norm_num [Format.rho]) hD
  have hh : 0  ≤  h := fourthRoot_nonneg _
  let Xk := EvaluateLower.vertex_of_bounded hadm.2.2.1 k.castSucc
  let Y0 := EvaluateLower.vertex_of_bounded hadm.2.2.2 0
  let Y1 := EvaluateLower.vertex_of_bounded hadm.2.2.2 1
  let Y2 := EvaluateLower.vertex_of_bounded hadm.2.2.2 2
  have hxk : ∀ i, value? I (x k i)=some (Xk.values i) := by
    fin_cases k <;> exact Xk.decode
  have b := EvaluateLower.format_budget fmt hadm.1 hadm.2.1 hlarge
  obtain ⟨e',f',r,he',hf',hr,_,_,hrC,_,_,hrD,hrE,hrF⟩ :=
    FaceCoordinates.face_geometry I Y0.decode Y1.decode Y2.decode hxk hadm.1
      Y0.bound Y1.bound Y2.bound Xk.bound b.rho b.eta b.linear
  have eqe : e'=e := funext (fun i => Option.some.inj ((he' i).symm.trans (he i)))
  have eqf : f'=f := funext (fun i => Option.some.inj ((hf' i).symm.trans (hf i)))
  subst e'; subst f'
  have hshift := endpoint_displacement fmt k hadm hlarge hap hp hr
  have hheight' := GeometryCoverage.plane_height_shift hN hheight hshift
  have hk : (k.val:ℝ) ∈ Set.Icc (0:ℝ) 1 := by fin_cases k <;> norm_num
  have hw : ‖realVec ap+s₀ • (-realVec p)+u₀ • realVec e+v₀ • realVec f‖  ≤  6*S+3*S := by
    simp only [smul_neg,← sub_eq_add_neg]
    dsimp [S,D]
    nlinarith only [hwitness,mul_nonneg fmt.rho_nonneg (show 0  ≤  L from hadm.1)]
  have hshift' : ‖realVec ap+(k.val:ℝ) • (-realVec p)-realVec r‖  ≤  3*S := by
    simpa only [smul_neg,← sub_eq_add_neg,S,mul_assoc] using hshift
  have hhgt : |inner ℝ (GeometryCoverage.exactCross (realVec e) (realVec f)) (realVec r)|/
      ‖GeometryCoverage.exactCross (realVec e) (realVec f)‖  ≤  6*S := by
    dsimp [S,D]; nlinarith only [hheight']
  have hout := crossing_local_coverage (R₀ := realVec ap) (P₀ := -realVec p) fmt he hf hr
    hadm.1 hadm.2.1 hlarge hA heD hfD hrD hrE hrF heC hfC hrC
    (show 0  ≤  6*S by positivity) hs₀ hk hu₀ hv₀ huv₀ hN hw hshift' hhgt
  have hratio : 6*S/S=6 := by field_simp
  rcases hout with ⟨q,hq,hbound⟩ | ⟨ss,u,v,hss,hu,hv,huv,hbd,hbound⟩
  · left
    refine ⟨q,hq,?_⟩
    change _  ≤  S*(V 6+4.54)+5*h
    change _  ≤  S*(V ((6*S)/S)+4.532)+5*h at hbound
    rw [hratio] at hbound
    nlinarith only [hbound,hS]
  · right
    refine ⟨ss,u,v,hss,hu,hv,huv,hbd,?_⟩
    rw [← decoded_eq I hap,← decoded_eq I hp,← decoded_eq I he,← decoded_eq I hf]
    simp only [smul_neg,← sub_eq_add_neg] at hbound
    change _  ≤  max (6*S) (S*(V ((6*S)/S)+0.002)+5*h)+3*S at hbound
    rw [FaceCoverage.crossing_edge_max hS hh,hratio] at hbound
    change _  ≤  S*(V 6+3.002)+5*h
    nlinarith only [hbound]

/-- An original exact intersection remains a small common rounded witness;
no rounded plane-intersection assumption is made. -/
theorem intersection_common (fmt : Format) {x : Segment fmt.interchange} {y : Triangle fmt.interchange}
    {L s u v : ℝ}
    (hadm : admissible fmt.interchange (.segment x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64  ≤  L)
    (hs : s∈Set.Icc (0:ℝ) 1) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v ≤ 1)
    (hzero : decodeVec fmt.interchange (y 0)+u • (decodeVec fmt.interchange (y 1)-decodeVec fmt.interchange (y 0))+
      v • (decodeVec fmt.interchange (y 2)-decodeVec fmt.interchange (y 0))-
      (decodeVec fmt.interchange (x 0)+s • (decodeVec fmt.interchange (x 1)-decodeVec fmt.interchange (x 0)))=0) :
    ‖decodeVec fmt.interchange (vsub fmt.interchange (y 0) (x 0))-
      s • decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0))+
      u • decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0))+
      v • decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0))‖ ≤ 3*fmt.rho*((7/2)*L) := by
  let I := fmt.interchange
  let X0 := EvaluateLower.vertex_of_bounded hadm.2.2.1 0
  let X1 := EvaluateLower.vertex_of_bounded hadm.2.2.1 1
  let Y0 := EvaluateLower.vertex_of_bounded hadm.2.2.2 0
  let Y1 := EvaluateLower.vertex_of_bounded hadm.2.2.2 1
  let Y2 := EvaluateLower.vertex_of_bounded hadm.2.2.2 2
  have b := EvaluateLower.format_budget fmt hadm.1 hadm.2.1 hlarge
  obtain ⟨e,f,ap,p,he,hf,hap,hp,rest⟩ := base_geometry fmt hadm hlarge
  have hh := WordGeometryTransfer.original_common I Y0.decode Y1.decode Y2.decode X0.decode X1.decode
    he hf hap hp hadm.1 Y0.bound Y1.bound Y2.bound X0.bound X1.bound hu hv huv hs.1 hs.2 b.rho b.eta b.linear
  rw [decoded_eq I he,decoded_eq I hf,decoded_eq I hap,decoded_eq I hp,
    decoded_eq I Y0.decode,decoded_eq I Y1.decode,decoded_eq I Y2.decode,
    decoded_eq I X0.decode,decoded_eq I X1.decode] at hh
  have hrho : I.format.unitRoundoff=fmt.rho := by cases fmt; exact fp32_parameters.1; exact fp64_parameters.1
  change ‖(_)-((decodeVec I (y 0)+u • (decodeVec I (y 1)-decodeVec I (y 0))+v • (decodeVec I (y 2)-decodeVec I (y 0)))-
    (decodeVec I (x 0)+s • (decodeVec I (x 1)-decodeVec I (x 0))))‖ ≤ _ at hh
  rw [hzero,sub_zero,hrho] at hh
  convert hh using 1
  congr 1
  module

end DistanceAccuracy.CrossingInputCoverage

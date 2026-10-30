import DistanceAccuracy.PointUpper
import DistanceAccuracy.PointProjection
import DistanceAccuracy.DotWordBounds

namespace DistanceAccuracy.PointUpper
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds
open GeometryCoverage
set_option exponentiation.threshold 2048

/-- Complete point-segment word trace and distance bounds against every
feasible exact parameter. Exceptional quotients need no preconditions. -/
theorem pointSegment_witness_bounds (f : DistanceAccuracy.Format)
    {x : Vec3 f.interchange} {y : Segment f.interchange}
    {X Y0 Y1 : Fin 3 → ℚ} {L : ℝ}
    (hx : ∀ i, value? f.interchange (x i) = some (X i))
    (hy0 : ∀ i, value? f.interchange (y 0 i) = some (Y0 i))
    (hy1 : ∀ i, value? f.interchange (y 1 i) = some (Y1 i))
    (hX : ∀ i, |(X i:ℝ)| ≤ L) (hY0 : ∀ i, |(Y0 i:ℝ)| ≤ L)
    (hY1 : ∀ i, |(Y1 i:ℝ)| ≤ L)
    (hL : L < fourthRoot f.interchange.format.maxFinite/4) :
    ∃ q t : ℚ, value? f.interchange (pointSegment f.interchange x y).q = some q ∧
      0 ≤ q ∧ 0 ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1 ∧
      (∀ v : ℝ, 0 ≤ v → v ≤ 1 →
        Real.sqrt (q:ℝ) ≤ ‖realVec Y0-realVec X+v • (realVec Y1-realVec Y0)‖+
          100*f.rho*L+12*Real.sqrt f.leastSubnormal) ∧
      ‖realVec Y0-realVec X+(t:ℝ) • (realVec Y1-realVec Y0)‖ ≤
        Real.sqrt (q:ℝ)+46*f.rho*L+7*Real.sqrt f.leastSubnormal := by
  let I := f.interchange
  let rho := I.format.unitRoundoff
  let eta := I.format.minSubnormal
  have hr : 0 ≤ rho := I.format.unitRoundoff_pos.le
  have he : 0 < eta := by dsimp [eta]; unfold FP.IEEE.Format.minSubnormal; positivity
  have hreq : rho = f.rho := by cases f with
    | binary32 => exact fp32_parameters.1
    | binary64 => exact fp64_parameters.1
  have heeq : eta = f.leastSubnormal := by cases f with
    | binary32 => exact fp32_parameters.2.2
    | binary64 => exact fp64_parameters.2.2
  have hrmax : rho ≤ 1/16777216 := by rw [hreq]; exact f.rho_le.trans (by norm_num)
  have hr1024 : rho ≤ 1/1024 := hrmax.trans (by norm_num)
  have he1 : eta ≤ 1 := by rw [heeq]; cases f <;> norm_num [DistanceAccuracy.Format.leastSubnormal]
  have hesmall : 2*Real.sqrt eta ≤ rho := by
    have hs : Real.sqrt eta ≤ rho/2 := by
      rw [Real.sqrt_le_iff,hreq,heeq]
      cases f <;> norm_num [DistanceAccuracy.Format.leastSubnormal,DistanceAccuracy.Format.rho]
    linarith only [hs]
  have hone : value? I (one I) = some 1 := by
    cases f with
    | binary32 => exact one_fp32
    | binary64 => exact one_fp64
  have hL0 : 0 ≤ L := (abs_nonneg (X 0:ℝ)).trans (hX 0)
  have hc := f.admissible_coordinate_ceiling hL
  have range (m c : ℝ) (hm : 0 ≤ m) (hmc : m ≤ 32) (hc0 : 0 ≤ c) (hc1 : c ≤ 32) :
      m*L+c < I.format.overflowThreshold := by
    have hb : m*L+c ≤ 32*f.coordinateCeiling+32 := by nlinarith only [hc,hL0,hmc,hc1,hm]
    have hh : 32*f.coordinateCeiling+32 < I.format.overflowThreshold := by
      cases f <;> norm_num [I,DistanceAccuracy.Format.interchange,DistanceAccuracy.Format.coordinateCeiling,
        fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.overflowThreshold]
    exact hb.trans_lt hh
  have hlim : 2*L < I.format.overflowThreshold := by have := range 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num); linarith
  have hflim : 2*(3*L+eta) < I.format.overflowThreshold := by
    have := range 6 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    linarith only [this,he1]
  obtain ⟨R,P,V,t,hR,hP,ht,ht0q,ht1q,hV,her,hep,hev⟩ :=
    pointSegment_residual_data I hone hx hy0 hy1 hX hY0 hY1 hr1024 hlim hflim
  have ht0 : (0:ℝ) ≤ t := by exact_mod_cast ht0q
  have ht1 : (t:ℝ) ≤ 1 := by exact_mod_cast ht1q
  let n := realVec R
  let p := realVec P
  let w := realVec V
  let n0 := realVec Y1-realVec Y0
  let p0 := realVec Y0-realVec X
  let D := 6*L+2*eta
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hs3 : Real.sqrt (3:ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have err : I.format.unitRoundoff*(2*Real.sqrt 3*L)+Real.sqrt 3*eta/2 ≤ 4*rho*L+eta := by
    have h1 := mul_le_mul_of_nonneg_right hs3 (show 0 ≤ 2*rho*L by positivity)
    have h2 := mul_le_mul_of_nonneg_right hs3 he.le
    nlinarith only [h1,h2]
  have herr : ‖n-n0‖ ≤ 4*rho*L+eta := her.trans err
  have hepr : ‖p-p0‖ ≤ 4*rho*L+eta := hep.trans err
  have diffnorm (A B : Fin 3 → ℚ) (hA : ∀ i, |(A i:ℝ)| ≤ L) (hB : ∀ i, |(B i:ℝ)| ≤ L) :
      ‖realVec A-realVec B‖ ≤ 4*L := by
    have hh := coordinate_norm_bound (show 0 ≤ 2*L by positivity)
      (v := realVec A-realVec B) (fun i => coordinate_difference (hA i) (hB i))
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hs3 hL0])
  have hn0 := diffnorm Y1 Y0 hY1 hY0
  have hp0 := diffnorm Y0 X hY0 hX
  have hnD : ‖n‖ ≤ D := by
    have hh := norm_le_norm_add_norm_sub n0 n
    rw [norm_sub_rev n0 n] at hh
    dsimp [D]
    nlinarith only [hh,herr,hn0,hL0,mul_nonneg hL0 (sub_nonneg.mpr hrmax),he.le]
  have hpD : ‖p‖ ≤ D := by
    have hh := norm_le_norm_add_norm_sub p0 p
    rw [norm_sub_rev p0 p] at hh
    dsimp [D]
    nlinarith only [hh,hepr,hp0,hL0,mul_nonneg hL0 (sub_nonneg.mpr hrmax),he.le]
  have heval : ‖w-(p+(t:ℝ) • n)‖ ≤ 12*rho*L+(4*rho+1)*eta := by
    have hm := mul_le_mul_of_nonneg_right hs3
      (show 0 ≤ 2*rho*(3*L+eta)+eta/2 by positivity)
    have hv : ‖w-(p+(t:ℝ) • n)‖ ≤ Real.sqrt 3*(2*rho*(3*L+eta)+eta/2) := by
      simpa only [add_comm] using hev
    nlinarith only [hv,hm]
  have hpn : ‖p+(t:ℝ) • n‖ ≤ 2*D := by
    have hh := norm_add_le p ((t:ℝ) • n)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0] at hh
    nlinarith only [hh,hpD,hnD,ht1,norm_nonneg n]
  have hwbound : ‖w‖ ≤ 13*L+6*eta := by
    have hh := norm_le_norm_add_norm_sub (p+(t:ℝ) • n) w
    rw [norm_sub_rev (p+(t:ℝ) • n) w] at hh
    dsimp [D] at hpn
    nlinarith only [hh,heval,hpn,hL0,he.le,mul_nonneg hL0 (sub_nonneg.mpr hrmax),
      mul_nonneg he.le (sub_nonneg.mpr hrmax)]
  have coord_norm (z : E3) (i : Fin 3) : |z i| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
  have prod_bound (A B : Fin 3 → ℚ) (hA : ‖realVec A‖ ≤ D) (hB : ‖realVec B‖ ≤ D) :
      ∀ i, |(A i:ℝ)*(B i:ℝ)| ≤ D^2+eta := by
    intro i
    have ha := (coord_norm (realVec A) i).trans hA
    have hb := (coord_norm (realVec B) i).trans hB
    have hm := mul_le_mul ha hb (abs_nonneg _) hD
    change |(A i:ℝ)| * |(B i:ℝ)| ≤ D*D at hm
    rw [abs_mul]
    nlinarith only [hm,he.le]
  have hprodlim : 6*(D^2+eta) < I.format.overflowThreshold := by
    have hdb : D ≤ 6*f.coordinateCeiling+2 := by dsimp [D]; linarith only [hc,he1]
    have hd2 := mul_self_le_mul_self hD hdb
    have hcap : 6*((6*f.coordinateCeiling+2)^2+1) < I.format.overflowThreshold := by
      cases f <;> norm_num [I,DistanceAccuracy.Format.interchange,DistanceAccuracy.Format.coordinateCeiling,
        fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.overflowThreshold]
    nlinarith only [hd2,hcap,he1]
  obtain ⟨a,ha,hea⟩ := DotWordBounds.dot3_finite_error I hR hR (by positivity : 0 < D^2+eta)
    (prod_bound R R hnD hnD) (by nlinarith only [sq_nonneg D]) (hrmax.trans (by norm_num)) hprodlim
  obtain ⟨b,hb,heb⟩ := DotWordBounds.dot3_finite_error I hP hR (by positivity : 0 < D^2+eta)
    (prod_bound P R hpD hnD) (by nlinarith only [sq_nonneg D]) (hrmax.trans (by norm_num)) hprodlim
  have hea' : |(a:ℝ)-‖n‖^2| ≤ 3*rho*(1+rho)^2*‖n‖^2+2*eta := by
    have hn : ‖n‖^2 = (R 0:ℝ)*(R 0:ℝ)+(R 1:ℝ)*(R 1:ℝ)+(R 2:ℝ)*(R 2:ℝ) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [n,realVec,Fin.sum_univ_succ,pow_two,add_assoc]
    change |(a:ℝ)-((R 0:ℝ)*(R 0:ℝ)+(R 1:ℝ)*(R 1:ℝ)+(R 2:ℝ)*(R 2:ℝ))| ≤
      3*rho*(1+rho)^2*‖n‖*‖n‖+2*eta at hea
    rw [← hn] at hea
    nlinarith only [hea]
  have heb' : |(b:ℝ)-inner ℝ n p| ≤ 3*rho*(1+rho)^2*‖n‖*‖p‖+2*eta := by
    have hn : inner ℝ n p = (P 0:ℝ)*(R 0:ℝ)+(P 1:ℝ)*(R 1:ℝ)+(P 2:ℝ)*(R 2:ℝ) := by
      simp [n,p,realVec,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_succ,mul_comm,add_assoc]
    rw [hn]
    simpa only [n,p,realVec,Determinant.realVec,mul_assoc,mul_left_comm,mul_comm] using heb
  have hquotrange : 16*D+4 < I.format.overflowThreshold*Real.sqrt eta := by
    have hh := f.quotient_range hL
    dsimp [D]
    nlinarith only [hh,hL0,he1]
  have hsolve (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
      ‖p+(t:ℝ) • n‖ ≤ ‖p+v • n‖+9*rho*D+4*Real.sqrt eta :=
    PointProjection.word_projection_norm_bound I hone ha hb ht ht0 ht1 hv0 hv1 hD hnD hpD
      hrmax he1 hesmall hquotrange hea' heb'
  have hpert (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
      ‖(p+v • n)-(p0+v • n0)‖ ≤ 8*rho*L+2*eta :=
    ReducedProjection.residual_perturbation hv0 hv1 (by linarith only [herr,hepr])
  have heval' : ‖w-(p+(t:ℝ) • n)‖ ≤ 12*rho*L+2*eta := by
    have hm := mul_le_mul_of_nonneg_right hrmax he.le
    nlinarith only [heval,hm,he.le]
  have hrecon : ‖w-(p0+(t:ℝ) • n0)‖ ≤ 20*rho*L+4*eta := by
    have hh := norm_add_le (w-(p+(t:ℝ) • n)) ((p+(t:ℝ) • n)-(p0+(t:ℝ) • n0))
    have hid : (w-(p+(t:ℝ) • n))+((p+(t:ℝ) • n)-(p0+(t:ℝ) • n0)) = w-(p0+(t:ℝ) • n0) := by module
    rw [hid] at hh
    linarith only [hh,heval',hpert (t:ℝ) ht0 ht1]
  have hwcoord (i : Fin 3) : |(V i:ℝ)| ≤ 13*L+6*eta :=
    (coord_norm w i).trans hwbound
  have hqlim : 8*(13*L+6*eta)*(13*L+6*eta)+4 < I.format.overflowThreshold := by
    have hh : 13*L+6*eta ≤ 13*f.coordinateCeiling+6 := by linarith only [hc,he1]
    have hs := mul_self_le_mul_self (show 0 ≤ 13*L+6*eta by positivity) hh
    have hcap : 8*(13*f.coordinateCeiling+6)^2+4 < I.format.overflowThreshold := by
      cases f <;> norm_num [I,DistanceAccuracy.Format.interchange,DistanceAccuracy.Format.coordinateCeiling,
        fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.overflowThreshold]
    nlinarith only [hs,hcap]
  obtain ⟨q,hq,hq0,hqe⟩ := ReconstructionIEEE.dot3_self_finite_error I hV
    (show 0 ≤ 13*L+6*eta by positivity) hwcoord hr1024 he1 hqlim
  have hw_sq : ‖w‖^2 = (V 0:ℝ)*(V 0:ℝ)+(V 1:ℝ)*(V 1:ℝ)+(V 2:ℝ)*(V 2:ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [w,realVec,Fin.sum_univ_succ,pow_two,add_assoc]
  have hroot := LowerBound.norm_evaluation hr hr1024 he.le (norm_nonneg w)
    (show 0 ≤ (q:ℝ) by exact_mod_cast hq0) (by rw [hw_sq]; exact hqe)
  have hsη := Real.sq_sqrt he.le
  have hsη0 := Real.sqrt_nonneg eta
  have hηroot : eta ≤ Real.sqrt eta := by nlinarith only [hsη,hsη0,he1]
  have hroot' : |Real.sqrt (q:ℝ)-‖w‖| ≤ 26*rho*L+3*Real.sqrt eta := by
    have hm := mul_le_mul_of_nonneg_left hwbound (show 0 ≤ 2*rho by positivity)
    have hmη := mul_le_mul_of_nonneg_right hrmax he.le
    nlinarith only [hroot,hm,hmη,hηroot,he.le]
  refine ⟨q,t,hq,hq0,ht0,ht1,?_,?_⟩
  · intro v hv0 hv1
    have hs := hsolve v hv0 hv1
    have hpv := norm_le_norm_add_norm_sub (p0+v • n0) (p+v • n)
    rw [norm_sub_rev (p0+v • n0) (p+v • n)] at hpv
    have hw := norm_le_norm_add_norm_sub (p+(t:ℝ) • n) w
    rw [norm_sub_rev (p+(t:ℝ) • n) w] at hw
    have hsq := (abs_le.mp hroot').2
    have hmη := mul_le_mul_of_nonneg_right hrmax he.le
    dsimp [D] at hs
    rw [← hreq,← heeq]
    change Real.sqrt (q:ℝ) ≤ ‖p0+v • n0‖+100*rho*L+12*Real.sqrt eta
    nlinarith only [hs,hpv,hw,hsq,hpert v hv0 hv1,heval',hmη,hηroot,hsη0]
  · have hw := norm_le_norm_add_norm_sub w (p0+(t:ℝ) • n0)
    have hlo := (abs_le.mp hroot').1
    rw [← hreq,← heeq]
    change ‖p0+(t:ℝ) • n0‖ ≤ Real.sqrt (q:ℝ)+46*rho*L+7*Real.sqrt eta
    nlinarith only [hw,hlo,hrecon,hηroot]

/-- Full claim 4 for the concrete point-segment kernel, including zero-length
segments and exceptional intermediate quotients. -/
theorem pointSegment_accuracyStatement (f : DistanceAccuracy.Format)
    (x : Vec3 f.interchange) (y : Segment f.interchange) (L : ℝ)
    (hadm : Geometry.admissible f.interchange (.point x) (.segment y) L) :
    ∃ q : ℝ, f.interchange.decode? (evaluate f.interchange (.point x) (.segment y)).q = some q ∧
      |Real.sqrt q-Geometry.distance f.interchange (.point x) (.segment y)| ≤
        64*(2*f.interchange.format.unitRoundoff)*L+fourthRoot f.interchange.format.minNormal := by
  have getInput (w : Vec3 f.interchange)
      (hw : ∀ i, ∃ v : ℝ, f.interchange.decode? (w i) = some v ∧ |v| ≤ L) :
      ∃ W : Fin 3 → ℚ, (∀ i, value? f.interchange (w i) = some (W i)) ∧
        (∀ i, |(W i:ℝ)| ≤ L) := by
    choose V hV hVL using hw
    have hq (i : Fin 3) := rat_of_real f.interchange (hV i)
    choose W hW hWV using hq
    exact ⟨W,hW,fun i => by rw [hWV i]; exact hVL i⟩
  obtain ⟨X,hX,hXL⟩ := getInput x (hadm.2.2.1 0)
  obtain ⟨Y0,hY0,hY0L⟩ := getInput (y 0) (hadm.2.2.2 0)
  obtain ⟨Y1,hY1,hY1L⟩ := getInput (y 1) (hadm.2.2.2 1)
  obtain ⟨q,t,hq,_,ht0,ht1,hupper,hlower⟩ :=
    pointSegment_witness_bounds f hX hY0 hY1 hXL hY0L hY1L hadm.2.1
  refine ⟨(q:ℝ),real_decode f.interchange hq,?_⟩
  have hxv := realVec_eq_decodeVec f.interchange hX
  have hy0v := realVec_eq_decodeVec f.interchange hY0
  have hy1v := realVec_eq_decodeVec f.interchange hY1
  rw [hxv,hy0v,hy1v] at hupper hlower
  obtain ⟨v,hv0,hv1,hv⟩ := Geometry.closest_point_segment f.interchange x y
  have hhi := hupper v hv0 hv1
  rw [← hv] at hhi
  have hmem : Geometry.decodeVec f.interchange (y 0)+(t:ℝ) •
      (Geometry.decodeVec f.interchange (y 1)-Geometry.decodeVec f.interchange (y 0)) ∈
      Geometry.carrier f.interchange (.segment y) := by
    rw [Geometry.segment_carrier]
    exact ⟨(t:ℝ),⟨ht0,ht1⟩,rfl⟩
  have hdist := Geometry.distance_le f.interchange (Geometry.vertex_mem f.interchange (.point x) 0) hmem
  have heq : Geometry.decodeVec f.interchange (y 0)+(t:ℝ) •
      (Geometry.decodeVec f.interchange (y 1)-Geometry.decodeVec f.interchange (y 0))-
      Geometry.decodeVec f.interchange x =
      Geometry.decodeVec f.interchange (y 0)-Geometry.decodeVec f.interchange x+(t:ℝ) •
      (Geometry.decodeVec f.interchange (y 1)-Geometry.decodeVec f.interchange (y 0)) := by module
  change Geometry.distance f.interchange (.point x) (.segment y) ≤ ‖_‖ at hdist
  dsimp only [Geometry.vertices] at hdist
  rw [heq] at hdist
  have hreq : f.interchange.format.unitRoundoff = f.rho := by
    cases f with
    | binary32 => exact fp32_parameters.1
    | binary64 => exact fp64_parameters.1
  have hneq : f.interchange.format.minNormal = f.leastNormal := by
    cases f with
    | binary32 => exact fp32_parameters.2.1
    | binary64 => exact fp64_parameters.2.1
  have hs : Real.sqrt f.leastSubnormal ≤ f.rootLower/12 := by
    rw [Real.sqrt_le_iff]
    cases f <;> norm_num [DistanceAccuracy.Format.leastSubnormal,DistanceAccuracy.Format.rootLower]
  have hroot := f.rootLower_le
  have hm := mul_nonneg f.rho_nonneg hadm.1
  have hs0 := Real.sqrt_nonneg f.leastSubnormal
  rw [hreq,hneq,abs_le]
  constructor <;> linarith only [hhi,hlower,hdist,hs,hroot,hm,hs0]

/-- Reversing the pair preserves the returned squared distance. -/
theorem segmentPoint_accuracyStatement (f : DistanceAccuracy.Format)
    (x : Segment f.interchange) (y : Vec3 f.interchange) (L : ℝ)
    (hadm : Geometry.admissible f.interchange (.segment x) (.point y) L) :
    ∃ q : ℝ, f.interchange.decode? (evaluate f.interchange (.segment x) (.point y)).q = some q ∧
      |Real.sqrt q-Geometry.distance f.interchange (.segment x) (.point y)| ≤
        64*(2*f.interchange.format.unitRoundoff)*L+fourthRoot f.interchange.format.minNormal := by
  obtain ⟨q,hq,he⟩ := pointSegment_accuracyStatement f y x L
    ⟨hadm.1,hadm.2.1,hadm.2.2.2,hadm.2.2.1⟩
  exact ⟨q,hq,by rw [Geometry.distance_symm]; exact he⟩

end DistanceAccuracy.PointUpper

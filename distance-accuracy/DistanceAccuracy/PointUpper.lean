import DistanceAccuracy.OperationBounds
import DistanceAccuracy.GeometryTransfer
import DistanceAccuracy.ReconstructionIEEE
import DistanceAccuracy.FormatRange
import DistanceAccuracy.GeometrySubsimplex

/-! Concrete word-level residual estimates for point kernels. -/
namespace DistanceAccuracy.PointUpper
open FP.IEEE FP.IEEE.Interchange
open IEEEAlgorithm IEEEBridge OperationBounds
open GeometryCoverage

variable (I : Interchange) [I.Valid]

noncomputable def realVec (v : Fin 3 → ℚ) : E3 := WithLp.toLp 2 (fun i => (v i : ℝ))

/-- Finite input coordinates and the subtraction range imply finite rounded
coordinate differences, with the local IEEE error at every coordinate. -/
theorem vsub_exists_error {x y : Vec3 I} {X Y : Fin 3 → ℚ} {L : ℝ}
    (hx : ∀ i, value? I (x i) = some (X i))
    (hy : ∀ i, value? I (y i) = some (Y i))
    (hX : ∀ i, |(X i : ℝ)| ≤ L) (hY : ∀ i, |(Y i : ℝ)| ≤ L)
    (hlim : 2*L < I.format.overflowThreshold) :
    ∃ R : Fin 3 → ℚ, (∀ i, value? I (vsub I y x i) = some (R i)) ∧
      ∀ i, |(R i : ℝ)-((Y i : ℝ)-(X i : ℝ))| ≤
        I.format.unitRoundoff * |(Y i : ℝ)-(X i : ℝ)|+I.format.minSubnormal/2 := by
  have he (i : Fin 3) := binary_exists_error I .sub (hy i) (hx i)
    (no_overflow_of_lt I (Y i-X i) (by
      simp only [Rat.cast_sub]
      exact (coordinate_difference (hY i) (hX i)).trans_lt hlim))
  choose R hR heR using he
  exact ⟨R, hR, by simpa only [Software.binaryExact, Rat.cast_sub] using heR⟩

/-- Point-point residual norm differs from the exact point distance by at most
one subtraction error. This theorem starts from actual IEEE input words. -/
theorem pointPoint_norm_error {x y : Vec3 I} {X Y : Fin 3 → ℚ} {L : ℝ}
    (hx : ∀ i, value? I (x i) = some (X i))
    (hy : ∀ i, value? I (y i) = some (Y i))
    (hX : ∀ i, |(X i : ℝ)| ≤ L) (hY : ∀ i, |(Y i : ℝ)| ≤ L)
    (hlim : 2*L < I.format.overflowThreshold) :
    ∃ R : Fin 3 → ℚ, (∀ i, value? I ((pointPoint I x y).r i) = some (R i)) ∧
      |‖realVec R‖-‖realVec Y-realVec X‖| ≤
        I.format.unitRoundoff*(2*Real.sqrt 3*L)+Real.sqrt 3*I.format.minSubnormal/2 := by
  obtain ⟨R,hR,he⟩ := vsub_exists_error I hx hy hX hY hlim
  refine ⟨R,hR,?_⟩
  have hn := difference_error_norm (A := realVec Y) (B := realVec X)
    (e := realVec R-(realVec Y-realVec X)) hY hX I.format.unitRoundoff_pos.le
    (show 0 ≤ I.format.minSubnormal by unfold FP.IEEE.Format.minSubnormal; positivity)
    (by simpa [realVec] using he)
  exact (abs_norm_sub_norm_le _ _).trans hn

/-- Clamping makes the point-segment parameter finite in [0,1], regardless of
zero denominators, overflowed quotients, or NaN quotients. -/
theorem pointSegment_parameter_bounded (hone : value? I (one I) = some 1)
    (x : Vec3 I) (y : Segment I) :
    ∃ t : ℚ, value? I ((pointSegment I x y).right 0) = some t ∧ 0 ≤ t ∧ t ≤ 1 := by
  simpa only [pointSegment, make, weights, Matrix.cons_val_zero] using
    clamp01nan_bounded I hone (div I (neg I (dot3 I (vsub I (y 0) x) (vsub I (y 1) (y 0))))
      (dot3 I (vsub I (y 1) (y 0)) (vsub I (y 1) (y 0))))

/-- A bounded finite parameter and bounded finite vectors imply finite FMA
residuals with an explicit norm error. -/
theorem fma3_exists_error {tw : I.Word} {r p : Vec3 I} {t : ℚ}
    {R P : Fin 3 → ℚ} {K : ℝ}
    (ht : value? I tw = some t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : ∀ i, value? I (r i) = some (R i))
    (hp : ∀ i, value? I (p i) = some (P i))
    (hR : ∀ i, |(R i : ℝ)| ≤ K) (hP : ∀ i, |(P i : ℝ)| ≤ K)
    (hlim : 2*K < I.format.overflowThreshold) :
    ∃ V : Fin 3 → ℚ, (∀ i, value? I (fma3 I tw r p i) = some (V i)) ∧
      ‖realVec V-((t:ℝ) • realVec R+realVec P)‖ ≤
        Real.sqrt 3*(2*I.format.unitRoundoff*K+I.format.minSubnormal/2) := by
  have ht0r : (0:ℝ) ≤ t := by exact_mod_cast ht0
  have ht1r : (t:ℝ) ≤ 1 := by exact_mod_cast ht1
  have hK : 0 ≤ K := (abs_nonneg (R 0 : ℝ)).trans (hR 0)
  have hbound (i : Fin 3) : |((t*R i+P i:ℚ):ℝ)| ≤ 2*K := by
    simp only [Rat.cast_add, Rat.cast_mul]
    calc
      |(t:ℝ)*(R i:ℝ)+(P i:ℝ)| ≤ |(t:ℝ)*(R i:ℝ)|+|(P i:ℝ)| := abs_add_le _ _
      _ ≤ 2*K := by
        rw [abs_mul, abs_of_nonneg ht0r]
        nlinarith [mul_le_mul_of_nonneg_left (hR i) ht0r, hP i]
  have he (i : Fin 3) := fma_exists_error I ht (hr i) (hp i)
    (no_overflow_of_lt I (t*R i+P i) ((hbound i).trans_lt hlim))
  choose V hV heV using he
  refine ⟨V,hV,coordinate_norm_bound (by
    have := I.format.unitRoundoff_pos; unfold FP.IEEE.Format.minSubnormal; positivity) ?_⟩
  intro i
  have he := (heV i).trans (add_le_add
    (mul_le_mul_of_nonneg_left (hbound i) I.format.unitRoundoff_pos.le) (le_refl _))
  simpa [realVec, mul_assoc, mul_left_comm, mul_comm] using he

/-- Complete concrete point-point distance estimate, including its returned
multiply/FMA/FMA squared distance and gradual underflow. Range assumptions are
on input magnitudes and the IEEE format, not on intermediate output words. -/
theorem pointPoint_distance_error {x y : Vec3 I} {X Y : Fin 3 → ℚ} {L : ℝ}
    (hx : ∀ i, value? I (x i) = some (X i))
    (hy : ∀ i, value? I (y i) = some (Y i))
    (hX : ∀ i, |(X i : ℝ)| ≤ L) (hY : ∀ i, |(Y i : ℝ)| ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ 1)
    (hlim : 2*L < I.format.overflowThreshold)
    (hqlim : 8*(3*L+I.format.minSubnormal)^2+4 < I.format.overflowThreshold) :
    ∃ q : ℚ, value? I (pointPoint I x y).q = some q ∧ 0 ≤ q ∧
      |Real.sqrt (q:ℝ)-‖realVec Y-realVec X‖| ≤
        16*I.format.unitRoundoff*L+4*Real.sqrt I.format.minSubnormal := by
  let rho := I.format.unitRoundoff
  let eta := I.format.minSubnormal
  have hr : 0 ≤ rho := I.format.unitRoundoff_pos.le
  have he : 0 ≤ eta := by dsimp [eta]; unfold FP.IEEE.Format.minSubnormal; positivity
  have hL : 0 ≤ L := (abs_nonneg (X 0:ℝ)).trans (hX 0)
  obtain ⟨R,hR,heR⟩ := vsub_exists_error I hx hy hX hY hlim
  have hRb (i : Fin 3) : |(R i:ℝ)| ≤ 3*L+eta := by
    have hd := coordinate_difference (hY i) (hX i)
    have hh := abs_sub (R i:ℝ) ((R i:ℝ)-((Y i:ℝ)-(X i:ℝ)))
    have hround := heR i
    have hmul := mul_le_mul_of_nonneg_left hd hr
    dsimp [rho,eta] at *
    have ht : |(R i:ℝ)| ≤ |(R i:ℝ)-((Y i:ℝ)-(X i:ℝ))|+|(Y i:ℝ)-(X i:ℝ)| := by
      convert abs_add_le ((R i:ℝ)-((Y i:ℝ)-(X i:ℝ))) ((Y i:ℝ)-(X i:ℝ)) using 1 <;> congr 1 <;> ring
    nlinarith [mul_nonneg hL (sub_nonneg.mpr hrho)]
  obtain ⟨q,hq,hq0,hqe⟩ := ReconstructionIEEE.dot3_self_finite_error I hR
    (show 0 ≤ 3*L+eta by positivity) hRb hrho heta (by nlinarith only [hqlim])
  refine ⟨q,hq,hq0,?_⟩
  have hn : ‖realVec R‖^2 = (R 0:ℝ)*(R 0:ℝ)+(R 1:ℝ)*(R 1:ℝ)+(R 2:ℝ)*(R 2:ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [realVec, Fin.sum_univ_succ, pow_two, add_assoc]
  have hroot := LowerBound.norm_evaluation hr hrho he (norm_nonneg (realVec R))
    (show 0 ≤ (q:ℝ) by exact_mod_cast hq0) (by rw [hn]; exact hqe)
  have herr := difference_error_norm (A := realVec Y) (B := realVec X)
    (e := realVec R-(realVec Y-realVec X)) hY hX hr he (by simpa [realVec] using heR)
  have hnerr := (abs_norm_sub_norm_le (realVec R) (realVec Y-realVec X)).trans herr
  have hnorm := coordinate_norm_bound (show 0 ≤ 3*L+eta by positivity) (v := realVec R) hRb
  have hs : Real.sqrt (3:ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hesq := Real.sq_sqrt he
  have hesqrt := Real.sqrt_nonneg eta
  have hecompare : eta ≤ Real.sqrt eta := by nlinarith
  have hnorm' : ‖realVec R‖ ≤ 2*(3*L+eta) := hnorm.trans
    (mul_le_mul_of_nonneg_right hs (by positivity))
  have herr' : |‖realVec R‖-‖realVec Y-realVec X‖| ≤ 4*rho*L+eta := by
    have h1 := mul_le_mul_of_nonneg_right hs (show 0 ≤ 2*rho*L by positivity)
    have h2 := mul_le_mul_of_nonneg_right hs he
    nlinarith only [hnerr,h1,h2]
  have htriangle : |Real.sqrt (q:ℝ)-‖realVec Y-realVec X‖| ≤
      |Real.sqrt (q:ℝ)-‖realVec R‖|+|‖realVec R‖-‖realVec Y-realVec X‖| := by
    convert abs_add_le (Real.sqrt (q:ℝ)-‖realVec R‖) (‖realVec R‖-‖realVec Y-realVec X‖) using 1 <;> congr 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hnorm' (show 0 ≤ 2*rho by positivity)
  have hecoef : 4*rho*eta ≤ eta := by nlinarith [mul_nonneg he (sub_nonneg.mpr hrho)]
  nlinarith only [htriangle,hroot,herr',hmul,hecoef,hecompare]

set_option exponentiation.threshold 2048 in
/-- Claim 4 for the complete concrete point-point kernel in binary32/binary64.
Epsilon is 2 rho, so 128 rho L is the requested 64 epsilon L. -/
theorem pointPoint_claim4 (f : DistanceAccuracy.Format) [f.interchange.Valid]
    {x y : Vec3 f.interchange} {X Y : Fin 3 → ℚ} {L : ℝ}
    (hx : ∀ i, value? f.interchange (x i) = some (X i))
    (hy : ∀ i, value? f.interchange (y i) = some (Y i))
    (hX : ∀ i, |(X i : ℝ)| ≤ L) (hY : ∀ i, |(Y i : ℝ)| ≤ L)
    (hL : L < fourthRoot f.interchange.format.maxFinite/4) :
    ∃ q : ℚ, value? f.interchange (pointPoint f.interchange x y).q = some q ∧ 0 ≤ q ∧
      |Real.sqrt (q:ℝ)-‖realVec Y-realVec X‖| ≤
        64*(2*f.rho)*L+fourthRoot f.leastNormal := by
  have hL0 : 0 ≤ L := (abs_nonneg (X 0:ℝ)).trans (hX 0)
  have hreq : f.interchange.format.unitRoundoff = f.rho := by
    cases f with
    | binary32 => exact fp32_parameters.1
    | binary64 => exact fp64_parameters.1
  have heeq : f.interchange.format.minSubnormal = f.leastSubnormal := by
    cases f with
    | binary32 => exact fp32_parameters.2.2
    | binary64 => exact fp64_parameters.2.2
  have hrmax : f.interchange.format.unitRoundoff ≤ 1/1024 := by
    rw [hreq]; exact f.rho_le.trans (by norm_num)
  have hemax : f.interchange.format.minSubnormal ≤ 1 := by
    rw [heeq]; cases f <;> norm_num [DistanceAccuracy.Format.leastSubnormal]
  have he0 := f.subnormal_nonneg
  have hlim : 2*L < f.interchange.format.overflowThreshold := by
    have := f.linear_range hL0 hL
    linarith
  have hq : 8*(3*L+f.interchange.format.minSubnormal)^2+4 <
      f.interchange.format.overflowThreshold := by
    have hc := f.admissible_coordinate_ceiling hL
    have hsum : 3*L+f.interchange.format.minSubnormal ≤ 3*f.coordinateCeiling+1 := by linarith
    have hs := mul_self_le_mul_self (show 0 ≤ 3*L+f.interchange.format.minSubnormal by rw [heeq]; positivity) hsum
    have hcap : 8*(3*f.coordinateCeiling+1)^2+4 < f.interchange.format.overflowThreshold := by
      cases f <;> norm_num [DistanceAccuracy.Format.coordinateCeiling, DistanceAccuracy.Format.interchange,
        fp32,fp64,FP.IEEE.binary32,FP.IEEE.binary64,FP.IEEE.Format.overflowThreshold]
    nlinarith only [hs,hcap]
  obtain ⟨q,hqv,hq0,he⟩ := pointPoint_distance_error f.interchange hx hy hX hY hrmax hemax hlim hq
  refine ⟨q,hqv,hq0,?_⟩
  have hs : Real.sqrt f.leastSubnormal ≤ f.rootLower/4 := by
    rw [Real.sqrt_le_iff]
    cases f <;> norm_num [DistanceAccuracy.Format.leastSubnormal, DistanceAccuracy.Format.rootLower]
  rw [hreq,heeq] at he
  have hroot := f.rootLower_le
  have hm := mul_nonneg f.rho_nonneg hL0
  linarith

/-- Complete concrete residual data for point-segment. No finiteness or range
assumption is made about either dot product or the quotient. The clamp alone
makes the returned residual finite once coordinate arithmetic fits. -/
theorem pointSegment_residual_data {x : Vec3 I} {y : Segment I}
    {X Y0 Y1 : Fin 3 → ℚ} {L : ℝ}
    (hone : value? I (one I) = some 1)
    (hx : ∀ i, value? I (x i) = some (X i))
    (hy0 : ∀ i, value? I (y 0 i) = some (Y0 i))
    (hy1 : ∀ i, value? I (y 1 i) = some (Y1 i))
    (hX : ∀ i, |(X i:ℝ)| ≤ L) (hY0 : ∀ i, |(Y0 i:ℝ)| ≤ L)
    (hY1 : ∀ i, |(Y1 i:ℝ)| ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (hlim : 2*L < I.format.overflowThreshold)
    (hflim : 2*(3*L+I.format.minSubnormal) < I.format.overflowThreshold) :
    ∃ (R P V : Fin 3 → ℚ) (t : ℚ),
      (∀ i, value? I (vsub I (y 1) (y 0) i) = some (R i)) ∧
      (∀ i, value? I (vsub I (y 0) x i) = some (P i)) ∧
      value? I ((pointSegment I x y).right 0) = some t ∧
      0 ≤ t ∧ t ≤ 1 ∧
      (∀ i, value? I ((pointSegment I x y).r i) = some (V i)) ∧
      ‖realVec R-(realVec Y1-realVec Y0)‖ ≤
        I.format.unitRoundoff*(2*Real.sqrt 3*L)+Real.sqrt 3*I.format.minSubnormal/2 ∧
      ‖realVec P-(realVec Y0-realVec X)‖ ≤
        I.format.unitRoundoff*(2*Real.sqrt 3*L)+Real.sqrt 3*I.format.minSubnormal/2 ∧
      ‖realVec V-((t:ℝ) • realVec R+realVec P)‖ ≤
        Real.sqrt 3*(2*I.format.unitRoundoff*(3*L+I.format.minSubnormal)+I.format.minSubnormal/2) := by
  obtain ⟨R,hR,heR⟩ := vsub_exists_error I hy0 hy1 hY0 hY1 hlim
  obtain ⟨P,hP,heP⟩ := vsub_exists_error I hx hy0 hX hY0 hlim
  obtain ⟨t,ht,ht0,ht1⟩ := pointSegment_parameter_bounded I hone x y
  let tw := clamp01nan I (div I (neg I (dot3 I (vsub I (y 0) x) (vsub I (y 1) (y 0))))
    (dot3 I (vsub I (y 1) (y 0)) (vsub I (y 1) (y 0))))
  have htw : value? I tw = some t := ht
  have hr := I.format.unitRoundoff_pos.le
  have he : 0 ≤ I.format.minSubnormal := by unfold FP.IEEE.Format.minSubnormal; positivity
  have hL0 : 0 ≤ L := (abs_nonneg (X 0:ℝ)).trans (hX 0)
  have bound (Z A B : Fin 3 → ℚ) (hA : ∀ i, |(A i:ℝ)| ≤ L)
      (hB : ∀ i, |(B i:ℝ)| ≤ L)
      (herr : ∀ i, |(Z i:ℝ)-((A i:ℝ)-(B i:ℝ))| ≤
        I.format.unitRoundoff*|(A i:ℝ)-(B i:ℝ)|+I.format.minSubnormal/2) :
      ∀ i, |(Z i:ℝ)| ≤ 3*L+I.format.minSubnormal := by
    intro i
    have hd := coordinate_difference (hA i) (hB i)
    have ht := abs_add_le ((Z i:ℝ)-((A i:ℝ)-(B i:ℝ))) ((A i:ℝ)-(B i:ℝ))
    have hid : (Z i:ℝ)-((A i:ℝ)-(B i:ℝ))+((A i:ℝ)-(B i:ℝ)) = (Z i:ℝ) := by ring
    rw [hid] at ht
    have hm := mul_le_mul_of_nonneg_left hd hr
    nlinarith [herr i,mul_nonneg hL0 (sub_nonneg.mpr hrho)]
  obtain ⟨V,hV,heV⟩ := fma3_exists_error I htw ht0 ht1 hR hP
    (bound R Y1 Y0 hY1 hY0 heR) (bound P Y0 X hY0 hX heP) hflim
  refine ⟨R,P,V,t,hR,hP,ht,ht0,ht1,hV,?_,?_,heV⟩
  · exact difference_error_norm (A := realVec Y1) (B := realVec Y0)
      hY1 hY0 hr he (by simpa [realVec] using heR)
  · exact difference_error_norm (A := realVec Y0) (B := realVec X)
      hY0 hX hr he (by simpa [realVec] using heP)

lemma realVec_eq_decodeVec {x : Vec3 I} {X : Fin 3 → ℚ}
    (hx : ∀ i, value? I (x i) = some (X i)) : realVec X = Geometry.decodeVec I x := by
  ext i
  simp [realVec,Geometry.decodeVec,real_decode I (hx i)]

/-- The point-point case of Geometry.accuracyStatement, with the exact distance
of the convex hulls and the actual evaluate dispatcher. -/
theorem pointPoint_accuracyStatement (f : DistanceAccuracy.Format)
    (x y : Vec3 f.interchange) (L : ℝ)
    (hadm : Geometry.admissible f.interchange (.point x) (.point y) L) :
    ∃ q : ℝ, f.interchange.decode? (evaluate f.interchange (.point x) (.point y)).q = some q ∧
      |Real.sqrt q-Geometry.distance f.interchange (.point x) (.point y)| ≤
        64*(2*f.interchange.format.unitRoundoff)*L+fourthRoot f.interchange.format.minNormal := by
  have getInput (w : Vec3 f.interchange)
      (hw : Geometry.boundedInput f.interchange (.point w) L) :
      ∃ W : Fin 3 → ℚ, (∀ i, value? f.interchange (w i) = some (W i)) ∧
        (∀ i, |(W i:ℝ)| ≤ L) := by
    have hv (i : Fin 3) : ∃ v : ℝ, f.interchange.decode? (w i) = some v ∧ |v| ≤ L := hw 0 i
    choose V hV hVL using hv
    have hq (i : Fin 3) := rat_of_real f.interchange (hV i)
    choose W hW hWV using hq
    exact ⟨W,hW,fun i => by rw [hWV i]; exact hVL i⟩
  obtain ⟨X,hX,hXL⟩ := getInput x hadm.2.2.1
  obtain ⟨Y,hY,hYL⟩ := getInput y hadm.2.2.2
  obtain ⟨q,hq,_,he⟩ := pointPoint_claim4 f hX hY hXL hYL hadm.2.1
  refine ⟨(q:ℝ),real_decode f.interchange hq,?_⟩
  rw [realVec_eq_decodeVec f.interchange hX,realVec_eq_decodeVec f.interchange hY,
    ← Geometry.distance_point_point f.interchange x y] at he
  have hreq : f.interchange.format.unitRoundoff = f.rho := by
    cases f with
    | binary32 => exact fp32_parameters.1
    | binary64 => exact fp64_parameters.1
  have hneq : f.interchange.format.minNormal = f.leastNormal := by
    cases f with
    | binary32 => exact fp32_parameters.2.1
    | binary64 => exact fp64_parameters.2.1
  simpa only [hreq,hneq] using he

end DistanceAccuracy.PointUpper

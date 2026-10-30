import DistanceAccuracy.SwappedDirectUpper
import DistanceAccuracy.FaceBudget
import DistanceAccuracy.BCUpperGeometry
import DistanceAccuracy.EvaluateLower
import DistanceAccuracy.FaceFinite
import DistanceAccuracy.ComputedBCTransfer
import DistanceAccuracy.TriangleCarrier
import DistanceAccuracy.PointUpper

namespace DistanceAccuracy.PointTriangleUpper
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant
open ProjectionRounding GeometryCoverage UpperSelection OperationBounds
set_option exponentiation.threshold 2048

lemma face_shape_bound {z : ℝ} (hz : 0 ≤ z) :
    hypot (J (317/100) z) (361/50) ≤ z+14 := by
  have hj := J_add_le (c := (317/100:ℝ)) (z := 0) (t := z) (by norm_num) (by norm_num) hz
  simp only [zero_add] at hj
  have hj0 : J (317/100) 0 ≤ 11 := by
    have hh : hypot (317/100:ℝ) 7.02 ≤ 783/100 := by
      apply hypot_le (by norm_num); norm_num
    dsimp [J]; norm_num at hh ⊢; linarith only [hh]
  have hm := hypot_mono (b := (361/50:ℝ)) (J_nonneg (c := (317/100:ℝ)) (z := z) (by norm_num)) hj
  have ha := hypot_add_le (a := J (317/100) 0) (b := (361/50:ℝ))
    (J_nonneg (by norm_num)) hz
  have hm0 := hypot_mono (J_nonneg (c := (317/100:ℝ)) (z := 0) (by norm_num)) hj0 (b := (361/50:ℝ))
  have h14 : hypot (11:ℝ) (361/50) ≤ 14 := by apply hypot_le (by norm_num); norm_num
  linarith only [hm,ha,hm0,h14]

lemma hypot_linear {a b : ℝ} (ha : 0≤a) (hb : 0≤b) : hypot a b ≤ a+b := by
  apply hypot_le (by positivity)
  nlinarith only [mul_nonneg ha hb]

lemma upper_mono {I : Interchange} {w : I.Word} {a b : ℝ}
    (h : Upper I a w) (hab : a≤b) : Upper I b w := by
  obtain ⟨q,hq,h⟩ := h
  exact ⟨q,hq,h.trans hab⟩

/-- The local face/edge dichotomy has a simple additive envelope. -/
theorem local_face_or_edge (fmt : Format)
    {E F R : Vec3 fmt.interchange} {e f r : Fin 3 → ℚ} {u v d L : ℝ}
    (hE : ∀ i, value? fmt.interchange (E i)= some (e i))
    (hF : ∀ i, value? fmt.interchange (F i)= some (f i))
    (hR : ∀ i, value? fmt.interchange (R i)= some (r i))
    (hL : 0≤L) (hadm : L<fourthRoot fmt.interchange.format.maxFinite/4)
    (hlarge : fourthRoot fmt.leastNormal/64≤L)
    (heD : ‖realVec e‖≤(7/2)*L) (hfD : ‖realVec f‖≤(7/2)*L) (hrD : ‖realVec r‖≤(7/2)*L)
    (hRE : ‖realVec r+realVec e‖≤(7/2)*L) (hRF : ‖realVec r+realVec f‖≤(7/2)*L)
    (heC : ∀ i, |(e i:ℝ)|≤((7/2)*L)/Real.sqrt 3)
    (hfC : ∀ i, |(f i:ℝ)|≤((7/2)*L)/Real.sqrt 3)
    (hrC : ∀ i, |(r i:ℝ)|≤((7/2)*L)/Real.sqrt 3)
    (hd : 0≤d) (hu : 0≤u) (hv : 0≤v) (huv : u+v≤1)
    (hw : ‖residual (realVec r) (realVec e) (realVec f) u v‖≤d) :
    Upper fmt.interchange (d+19*fmt.rho*((7/2)*L)+5*fourthRoot fmt.leastSubnormal)
      (face fmt.interchange R E F (cross3 fmt.interchange E F)).q ∨
    ∃ u' v' : ℝ, 0≤u' ∧ 0≤v' ∧ u'+v'≤1 ∧ (u'=0 ∨ u'+v'=1) ∧
      ‖residual (realVec r) (realVec e) (realVec f) u' v'‖≤
        d+(1401/100)*fmt.rho*((7/2)*L)+5*fourthRoot fmt.leastSubnormal := by
  have hrho : 0 < fmt.rho := by cases fmt <;> norm_num [Format.rho]
  have hk0 : 0≤fmt.rho*((7/2)*L) := mul_nonneg hrho.le (by positivity)
  by_cases hA : fourthRoot fmt.leastSubnormal < ‖realVec e‖
  · have hk : 0<fmt.rho*((7/2)*L) := mul_pos hrho
      ((fourthRoot_nonneg _).trans_lt hA |>.trans_le heD)
    have hb := face_shape_bound (div_nonneg hd hk.le)
    have hm := mul_le_mul_of_nonneg_left hb hk.le
    have heq : fmt.rho*((7/2)*L)*(d/(fmt.rho*((7/2)*L)))=d := mul_div_cancel₀ _ (ne_of_gt hk)
    rw [mul_add,heq] at hm
    have hh := FaceCoverage.face_admissible_clean fmt false hE hF hR hL hadm hlarge hA
      heD hfD hrD hRE hRF heC hfC hrC hd hu hv huv hw
    simp only [Bool.false_eq_true, ↓reduceIte, PointProjection.crossCoefficient] at hh
    rcases hh with hface | ⟨u',v',hu',hv',huv',hbd,hbound⟩
    · exact Or.inl (upper_mono hface (by nlinarith only [hm,hk0]))
    · exact Or.inr ⟨u',v',hu',hv',huv',hbd,by nlinarith only [hbound,hm,hk0]⟩
  · obtain ⟨u',v',hu',hv',huv',hbd,hclose⟩ := short_base_edge_witness (R := realVec r) (E := realVec e) (F := realVec f) hu hv huv
    have ht := norm_add_le (residual (realVec r) (realVec e) (realVec f) u v)
      (residual (realVec r) (realVec e) (realVec f) u' v' - residual (realVec r) (realVec e) (realVec f) u v)
    simp only [← add_sub_assoc, add_sub_cancel_left] at ht
    rw [norm_sub_rev] at hclose
    exact Or.inr ⟨u',v',hu',hv',huv',hbd,by nlinarith only [ht,hclose,hw,le_of_not_gt hA,hk0,fourthRoot_nonneg fmt.leastSubnormal]⟩

lemma boundary_upper {I : Interchange} {ac bc : I.Word} {R E F BX E2 : Determinant.E3}
    {rho D h d u v : ℝ} (hk : 0≤rho*D) (hh : 0≤h)
    (hu : 0≤u) (hv : 0≤v) (huv : u+v≤1) (hbd : u=0 ∨ u+v=1)
    (hw : ‖residual R E F u v‖≤d+(1401/100)*rho*D+5*h)
    (htransfer : ∀ t : ℝ, 0≤t → t≤1 →
      ‖BX+t•E2-(R+(1-t)•E+t•F)‖≤4*rho*D)
    (hac : ∀ t : ℝ, 0≤t → t≤1 → Upper I
      (hypot ‖R+t•F‖ ((419/50)*rho*D)+(127/50)*rho*D+2*h) ac)
    (hbc : ∀ t : ℝ, 0≤t → t≤1 → Upper I
      (hypot ‖BX+t•E2‖ ((419/50)*rho*D)+(127/50)*rho*D+2*h) bc) :
    Upper I (d+29*rho*D+7*h) ac ∨ Upper I (d+29*rho*D+7*h) bc := by
  have hv1 : v≤1 := by linarith only [hu,huv]
  have hs : 0≤(419/50)*rho*D := by nlinarith only [hk]
  rcases hbd with rfl | hbd
  · left
    have hw' : ‖R+v•F‖≤d+(1401/100)*rho*D+5*h := by
      simpa [GeometryCoverage.residual] using hw
    exact upper_mono (hac v hv hv1) (by
      have hp := hypot_linear (norm_nonneg (R+v•F)) hs
      nlinarith only [hw',hp,hk])
  · right
    have hu' : u=1-v := by linarith only [hbd]
    have hn := norm_add_le (BX+v•E2-(R+(1-v)•E+v•F)) (R+(1-v)•E+v•F)
    rw [sub_add_cancel] at hn
    have he := htransfer v hv hv1
    rw [hu'] at hw
    change ‖R+(1-v)•E+v•F‖≤_ at hw
    exact upper_mono (hbc v hv hv1) (by
      have hp := hypot_linear (norm_nonneg (BX+v•E2)) hs
      nlinarith only [hn,he,hw,hp,hk])

lemma common_witness {R E F A B C X : Determinant.E3} {u v k d : ℝ}
    (hk : 0≤k) (hu : 0≤u) (hv : 0≤v) (huv : u+v≤1)
    (hR : ‖R-(A-X)‖≤k) (hE : ‖E-(B-A)‖≤k) (hF : ‖F-(C-A)‖≤k)
    (hw : ‖A-X+u•(B-A)+v•(C-A)‖≤d) :
    ‖residual R E F u v‖≤d+3*k := by
  have hu1 : u≤1 := by linarith only [hv,huv]
  have hv1 : v≤1 := by linarith only [hu,huv]
  have he := norm_add_le (R-(A-X)) (u•(E-(B-A)))
  have hf := norm_add_le ((R-(A-X))+u•(E-(B-A))) (v•(F-(C-A)))
  have ht := norm_add_le (A-X+u•(B-A)+v•(C-A))
    ((R-(A-X))+u•(E-(B-A))+v•(F-(C-A)))
  have hid : (A-X+u•(B-A)+v•(C-A))+((R-(A-X))+u•(E-(B-A))+v•(F-(C-A))) = residual R E F u v := by
    dsimp [GeometryCoverage.residual]; module
  rw [hid] at ht
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hu] at he
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hv] at hf
  have heu := mul_le_mul hE hu1 hu hk
  have hfv := mul_le_mul hF hv1 hv hk
  nlinarith only [he,hf,ht,hw,hR,heu,hfv]

/-- Actual point-triangle selection bounded against any exact feasible witness.
All local rounding and overflow obligations follow from the original inputs. -/
theorem witness_upper (fmt : Format)
    {x : Vec3 fmt.interchange} {y : Triangle fmt.interchange}
    {X A B C : Fin 3 → ℚ} {L u v d : ℝ}
    (hx : ∀ i, value? fmt.interchange (x i)=some (X i))
    (ha : ∀ i, value? fmt.interchange (y 0 i)=some (A i))
    (hb : ∀ i, value? fmt.interchange (y 1 i)=some (B i))
    (hc : ∀ i, value? fmt.interchange (y 2 i)=some (C i))
    (hX : ∀ i, |(X i:ℝ)|≤L) (hA : ∀ i, |(A i:ℝ)|≤L)
    (hB : ∀ i, |(B i:ℝ)|≤L) (hC : ∀ i, |(C i:ℝ)|≤L)
    (hL : 0≤L) (hadm : L<fourthRoot fmt.interchange.format.maxFinite/4)
    (hlarge : fourthRoot fmt.leastNormal/64≤L)
    (hd : 0≤d) (hu : 0≤u) (hv : 0≤v) (huv : u+v≤1)
    (hw : ‖realVec A-realVec X+u•(realVec B-realVec A)+v•(realVec C-realVec A)‖≤d) :
    Upper fmt.interchange (d+112*fmt.rho*L+7*fourthRoot fmt.leastSubnormal)
      (pointTriangle fmt.interchange x y).q := by
  let I := fmt.interchange
  let D : ℝ := (7/2)*L
  let k : ℝ := fmt.rho*D
  let budget := EvaluateLower.format_budget fmt hL hadm hlarge
  have hρ := (format_parameters fmt).1
  have hk : 0≤k := by dsimp [k,D]; rw [←hρ]; exact mul_nonneg I.format.unitRoundoff_pos.le (by positivity)
  have hh := fourthRoot_nonneg fmt.leastSubnormal
  obtain ⟨e,f,r,he,hf,hr,heC,hfC,hrC,heD,hfD,hrD,hRE,hRF⟩ :=
    FaceCoordinates.face_geometry I ha hb hc hx hL hA hB hC hX budget.rho budget.eta budget.linear
  obtain ⟨e2,bx,he2,hbx,he2C,hbxC,he2D,hbxD,hBXE2,_,_⟩ :=
    BCUpperGeometry.bc_geometry I ha hb hc hx hL hA hB hC hX budget.rho budget.eta budget.linear
  have hFE := WordGeometryTransfer.edge_difference I ha hb hc he hf hL hA hB hC budget.rho budget.eta budget.linear
  have hcycle (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
      ‖realVec bx+t•realVec e2-(realVec r+(1-t)•realVec e+t•realVec f)‖≤4*fmt.rho*D := by
    have hc := WordGeometryTransfer.computed_bc_transfer I he hf hr he2 hbx hFE hRE hL ht0 ht1 budget.rho budget.eta budget.linear
    rw [hρ] at hc
    dsimp [k,D] at *
    nlinarith only [hc,hk]
  have er := WordGeometryTransfer.difference_error I ha hx hr hL hA hX budget.rho budget.eta budget.linear
  have ee := WordGeometryTransfer.difference_error I hb ha he hL hB hA budget.rho budget.eta budget.linear
  have ef := WordGeometryTransfer.difference_error I hc ha hf hL hC hA budget.rho budget.eta budget.linear
  rw [hρ] at er ee ef
  have hw' := common_witness hk hu hv huv er ee ef hw
  have hd' : 0≤d+3*k := by positivity
  have hdlim : D≤9*L := by dsimp [D]; linarith only [hL]
  let acw := clamp01nan I (div I (neg I (dot3 I (vsub I (y 2) (y 0)) (vsub I (y 0) x)))
    (dot3 I (vsub I (y 2) (y 0)) (vsub I (y 2) (y 0))))
  let bcw := clamp01nan I (div I (neg I (dot3 I (vadd I (vsub I (y 0) x) (vsub I (y 1) (y 0)))
    (vsub I (vsub I (y 2) (y 0)) (vsub I (y 1) (y 0)))))
    (dot3 I (vsub I (vsub I (y 2) (y 0)) (vsub I (y 1) (y 0))) (vsub I (vsub I (y 2) (y 0)) (vsub I (y 1) (y 0)))))
  let ac := make I (fma3 I acw (vsub I (y 2) (y 0)) (vsub I (y 0) x)) (emptyWeights I) (weights I (zero I) acw)
  let bc := make I (fma3 I bcw (vsub I (vsub I (y 2) (y 0)) (vsub I (y 1) (y 0)))
    (vadd I (vsub I (y 0) x) (vsub I (y 1) (y 0)))) (emptyWeights I) (weights I (sub I (one I) bcw) bcw)
  let fc := face I (vsub I (y 0) x) (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
    (cross3 I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))
  have hac (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) : Upper I
      (hypot ‖realVec r+t•realVec f‖ ((419/50)*fmt.rho*D)+(127/50)*fmt.rho*D+2*fourthRoot fmt.leastSubnormal) ac.q :=
    direct_candidate_upper fmt budget.one hf hr hL hadm hdlim hfD hrD hRF hfC hrC ht0 ht1
  have hbc (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) : Upper I
      (hypot ‖realVec bx+t•realVec e2‖ ((419/50)*fmt.rho*D)+(127/50)*fmt.rho*D+2*fourthRoot fmt.leastSubnormal) bc.q :=
    direct_candidate_upper_swapped fmt budget.one he2 hbx hL hadm hdlim he2D hbxD hBXE2 he2C hbxC ht0 ht1
  have hfin := face_finite_admissible (n := cross3 I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))
    fmt ha hb hc hx hL hadm hA hB hC hX
  change Upper I _ (choose I (choose I ac bc) fc).q
  apply choose_three_upper I ((hac 0 le_rfl zero_le_one).finite) ((hbc 0 le_rfl zero_le_one).finite) hfin
  rcases local_face_or_edge fmt he hf hr hL hadm hlarge heD hfD hrD hRE hRF heC hfC hrC hd' hu hv huv hw' with hfup | ⟨u',v',hu',hv',huv',hbd,hbound⟩
  · right; right
    exact upper_mono hfup (by dsimp [k,D] at *; nlinarith only [hk,hh])
  · have h := boundary_upper hk hh hu' hv' huv' hbd hbound hcycle hac hbc
    rcases h with h | h
    · exact Or.inl (upper_mono h (by dsimp [k,D]; ring_nf; rfl))
    · exact Or.inr (Or.inl (upper_mono h (by dsimp [k,D]; ring_nf; rfl)))

lemma subnormal_remainder (fmt : Format) :
    7*fourthRoot fmt.leastSubnormal ≤ fourthRoot fmt.leastNormal := by
  apply (pow_le_pow_iff_left₀ (mul_nonneg (by norm_num) (fourthRoot_nonneg _))
    (fourthRoot_nonneg _) (show (4:ℕ)≠0 by decide)).mp
  rw [mul_pow, fourthRoot_pow_four fmt.subnormal_nonneg,
    fourthRoot_pow_four (show 0≤fmt.leastNormal by cases fmt <;> norm_num [Format.leastNormal])]
  cases fmt <;> norm_num [Format.leastNormal,Format.leastSubnormal]

lemma bounded_vertex (fmt : Format) {s : Simplex fmt.interchange} {L : ℝ}
    (hs : Geometry.boundedInput fmt.interchange s L) (j : Fin 3) :
    ∃ X : Fin 3 → ℚ, (∀ i, value? fmt.interchange (Geometry.vertices fmt.interchange s j i)=some (X i)) ∧
      (∀ i, |(X i:ℝ)|≤L) := by
  choose V hV hVL using hs j
  choose X hX hXV using fun i => rat_of_real fmt.interchange (hV i)
  exact ⟨X,hX,fun i => by rw [hXV i]; exact hVL i⟩

/-- End-to-end upper accuracy in the large-coordinate regime. -/
theorem large_upper (fmt : Format) (x : Vec3 fmt.interchange) (y : Triangle fmt.interchange) (L : ℝ)
    (hadm : Geometry.admissible fmt.interchange (.point x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64≤L) :
    Upper fmt.interchange (Geometry.distance fmt.interchange (.point x) (.triangle y)+
      112*fmt.rho*L+7*fourthRoot fmt.leastSubnormal) (pointTriangle fmt.interchange x y).q := by
  obtain ⟨X,hx,hX⟩ := bounded_vertex fmt hadm.2.2.1 0
  obtain ⟨A,ha,hA⟩ := bounded_vertex fmt hadm.2.2.2 0
  obtain ⟨B,hb,hB⟩ := bounded_vertex fmt hadm.2.2.2 1
  obtain ⟨C,hc,hC⟩ := bounded_vertex fmt hadm.2.2.2 2
  obtain ⟨u,v,hu,hv,huv,hw⟩ := Geometry.closest_point_triangle fmt.interchange x y
  have hw' : ‖realVec A-realVec X+u•(realVec B-realVec A)+v•(realVec C-realVec A)‖≤
      Geometry.distance fmt.interchange (.point x) (.triangle y) := by
    change ‖PointUpper.realVec A-PointUpper.realVec X+u•(PointUpper.realVec B-PointUpper.realVec A)+v•(PointUpper.realVec C-PointUpper.realVec A)‖≤_
    rw [PointUpper.realVec_eq_decodeVec fmt.interchange ha,PointUpper.realVec_eq_decodeVec fmt.interchange hb,
      PointUpper.realVec_eq_decodeVec fmt.interchange hc,PointUpper.realVec_eq_decodeVec fmt.interchange hx]
    exact hw.symm.le
  exact witness_upper fmt hx ha hb hc hX hA hB hC hadm.1 hadm.2.1 hlarge
    (Geometry.distance_nonneg _ _ _) hu hv huv hw'

/-- Claim4 for the complete IEEE point-triangle method, with coefficient64. -/
theorem pointTriangle_accuracyStatement (fmt : Format)
    (x : Vec3 fmt.interchange) (y : Triangle fmt.interchange) (L : ℝ)
    (hadm : Geometry.admissible fmt.interchange (.point x) (.triangle y) L) :
    ∃ q : ℝ, fmt.interchange.decode? (evaluate fmt.interchange (.point x) (.triangle y)).q=some q ∧
      |Real.sqrt q-Geometry.distance fmt.interchange (.point x) (.triangle y)|≤
        64*(2*fmt.interchange.format.unitRoundoff)*L+fourthRoot fmt.interchange.format.minNormal := by
  have hρ := (format_parameters fmt).1
  have hnormal : fmt.interchange.format.minNormal=fmt.leastNormal := by
    cases fmt with
    | binary32 => exact fp32_parameters.2.1
    | binary64 => exact fp64_parameters.2.1
  have hk : 0≤fmt.rho*L := by rw [←hρ]; exact mul_nonneg fmt.interchange.format.unitRoundoff_pos.le hadm.1
  by_cases hlarge : fourthRoot fmt.leastNormal/64≤L
  · obtain ⟨q,hq,hupper⟩ := large_upper fmt x y L hadm hlarge
    obtain ⟨q',hq',_,hlower⟩ := EvaluateLower.large_lower fmt (.point x) (.triangle y) L hadm hlarge
    have heq : (q:ℝ)=q' := Option.some.inj ((real_decode fmt.interchange hq).symm.trans hq')
    subst q'
    refine ⟨(q:ℝ),real_decode fmt.interchange hq,?_⟩
    rw [hρ,hnormal] at *
    have hf := subnormal_remainder fmt
    exact abs_le.mpr ⟨by nlinarith only [hlower,hk,fourthRoot_nonneg fmt.leastNormal],
      by nlinarith only [hupper,hf,hk]⟩
  · obtain ⟨q,hq,_,hb⟩ := EvaluateLower.small_accuracy fmt (.point x) (.triangle y) L hadm (le_of_not_ge hlarge)
    refine ⟨q,hq,?_⟩
    rw [hρ,hnormal]
    nlinarith only [hb,hk]

/-- Reversing the inputs preserves the selected squared distance. -/
theorem trianglePoint_accuracyStatement (fmt : Format)
    (x : Triangle fmt.interchange) (y : Vec3 fmt.interchange) (L : ℝ)
    (hadm : Geometry.admissible fmt.interchange (.triangle x) (.point y) L) :
    ∃ q : ℝ, fmt.interchange.decode? (evaluate fmt.interchange (.triangle x) (.point y)).q=some q ∧
      |Real.sqrt q-Geometry.distance fmt.interchange (.triangle x) (.point y)|≤
        64*(2*fmt.interchange.format.unitRoundoff)*L+fourthRoot fmt.interchange.format.minNormal := by
  obtain ⟨q,hq,hb⟩ := pointTriangle_accuracyStatement fmt y x L
    ⟨hadm.1,hadm.2.1,hadm.2.2.2,hadm.2.2.1⟩
  exact ⟨q,hq,by rw [Geometry.distance_symm]; exact hb⟩

end DistanceAccuracy.PointTriangleUpper

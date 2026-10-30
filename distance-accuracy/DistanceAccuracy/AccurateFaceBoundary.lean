import DistanceAccuracy.PointTriangleUpper

namespace DistanceAccuracy.PointTriangleUpper
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge Determinant
open ProjectionRounding GeometryCoverage UpperSelection OperationBounds
set_option exponentiation.threshold 2048

lemma face_shape_bound_accurate {z : ℝ} (hz : 0 ≤ z) :
    hypot (J (18/5) z) (361/50) ≤ z+14 := by
  have hj := J_add_le (c := (18/5:ℝ)) (z := 0) (t := z) (by norm_num) (by norm_num) hz
  simp only [zero_add] at hj
  have hj0 : J (18/5) 0 ≤ 59/5 := by
    have hh : hypot (18/5:ℝ) 7.02 ≤ 41/5 := by
      apply hypot_le (by norm_num); norm_num
    dsimp [J]; norm_num at hh ⊢; linarith only [hh]
  have hm := hypot_mono (b := (361/50:ℝ)) (J_nonneg (c := (18/5:ℝ)) (z := z) (by norm_num)) hj
  have ha := hypot_add_le (a := J (18/5) 0) (b := (361/50:ℝ))
    (J_nonneg (by norm_num)) hz
  have hm0 := hypot_mono (J_nonneg (c := (18/5:ℝ)) (z := 0) (by norm_num)) hj0 (b := (361/50:ℝ))
  have h14 : hypot (59/5:ℝ) (361/50) ≤ 14 := by apply hypot_le (by norm_num); norm_num
  linarith only [hm,ha,hm0,h14]

/-- The local face/edge dichotomy has a simple additive envelope. -/
theorem local_accurate_face_or_edge (fmt : Format)
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
      (face fmt.interchange R E F (cross3Accurate fmt.interchange E F)).q ∨
    ∃ u' v' : ℝ, 0≤u' ∧ 0≤v' ∧ u'+v'≤1 ∧ (u'=0 ∨ u'+v'=1) ∧
      ‖residual (realVec r) (realVec e) (realVec f) u' v'‖≤
        d+(1401/100)*fmt.rho*((7/2)*L)+5*fourthRoot fmt.leastSubnormal := by
  have hrho : 0 < fmt.rho := by cases fmt <;> norm_num [Format.rho]
  have hk0 : 0≤fmt.rho*((7/2)*L) := mul_nonneg hrho.le (by positivity)
  by_cases hA : fourthRoot fmt.leastSubnormal < ‖realVec e‖
  · have hk : 0<fmt.rho*((7/2)*L) := mul_pos hrho
      ((fourthRoot_nonneg _).trans_lt hA |>.trans_le heD)
    have hb := face_shape_bound_accurate (div_nonneg hd hk.le)
    have hm := mul_le_mul_of_nonneg_left hb hk.le
    have heq : fmt.rho*((7/2)*L)*(d/(fmt.rho*((7/2)*L)))=d := mul_div_cancel₀ _ (ne_of_gt hk)
    rw [mul_add,heq] at hm
    have hh := FaceCoverage.face_admissible_clean fmt true hE hF hR hL hadm hlarge hA
      heD hfD hrD hRE hRF heC hfC hrC hd hu hv huv hw
    simp only [↓reduceIte, PointProjection.crossCoefficient] at hh
    rcases hh with hface | ⟨u',v',hu',hv',huv',hbd,hbound⟩
    · exact Or.inl (upper_mono hface (by nlinarith only [hm,hk0]))
    · exact Or.inr ⟨u',v',hu',hv',huv',hbd,by nlinarith only [hbound,hm,hk0]⟩
  · obtain ⟨u',v',hu',hv',huv',hbd,hclose⟩ := short_base_edge_witness (R := realVec r) (E := realVec e) (F := realVec f) hu hv huv
    have ht := norm_add_le (residual (realVec r) (realVec e) (realVec f) u v)
      (residual (realVec r) (realVec e) (realVec f) u' v' - residual (realVec r) (realVec e) (realVec f) u v)
    simp only [← add_sub_assoc, add_sub_cancel_left] at ht
    rw [norm_sub_rev] at hclose
    exact Or.inr ⟨u',v',hu',hv',huv',hbd,by nlinarith only [ht,hclose,hw,le_of_not_gt hA,hk0,fourthRoot_nonneg fmt.leastSubnormal]⟩


lemma common_witness_two {R E F A B C X : Determinant.E3} {u v k d : ℝ}
    (hk : 0≤k) (hu : 0≤u) (hv : 0≤v) (huv : u+v≤1)
    (hR : ‖R-(A-X)‖≤k) (hE : ‖E-(B-A)‖≤k) (hF : ‖F-(C-A)‖≤k)
    (hw : ‖A-X+u•(B-A)+v•(C-A)‖≤d) :
    ‖residual R E F u v‖≤d+2*k := by
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
  have heu := mul_le_mul_of_nonneg_left hE hu
  have hfv := mul_le_mul_of_nonneg_left hF hv
  have huv' := mul_le_mul_of_nonneg_right huv hk
  nlinarith only [he,hf,ht,hw,hR,heu,hfv,huv']

lemma common_witness_reverse {R E F A B C X : Determinant.E3} {u v k d : ℝ}
    (hk : 0≤k) (hu : 0≤u) (hv : 0≤v) (huv : u+v≤1)
    (hR : ‖R-(A-X)‖≤k) (hE : ‖E-(B-A)‖≤k) (hF : ‖F-(C-A)‖≤k)
    (hw : ‖residual R E F u v‖≤d) :
    ‖A-X+u•(B-A)+v•(C-A)‖≤d+2*k := by
  have hu1 : u≤1 := by linarith only [hv,huv]
  have hv1 : v≤1 := by linarith only [hu,huv]
  have he := norm_add_le (R-(A-X)) (u•(E-(B-A)))
  have hf := norm_add_le ((R-(A-X))+u•(E-(B-A))) (v•(F-(C-A)))
  have ht := norm_sub_le (residual R E F u v)
    ((R-(A-X))+u•(E-(B-A))+v•(F-(C-A)))
  have hid : residual R E F u v-((R-(A-X))+u•(E-(B-A))+v•(F-(C-A))) = A-X+u•(B-A)+v•(C-A) := by
    dsimp [GeometryCoverage.residual]; module
  rw [hid] at ht
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hu] at he
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hv] at hf
  have heu := mul_le_mul_of_nonneg_left hE hu
  have hfv := mul_le_mul_of_nonneg_left hF hv
  have huv' := mul_le_mul_of_nonneg_right huv hk
  nlinarith only [he,hf,ht,hw,hR,heu,hfv,huv']

theorem accurate_face_or_boundary (fmt : Format)
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
    Upper fmt.interchange (d+21*fmt.rho*((7/2)*L)+5*fourthRoot fmt.leastSubnormal)
      (face fmt.interchange (vsub fmt.interchange (y 0) x) (vsub fmt.interchange (y 1) (y 0))
        (vsub fmt.interchange (y 2) (y 0))
        (cross3Accurate fmt.interchange (vsub fmt.interchange (y 1) (y 0)) (vsub fmt.interchange (y 2) (y 0)))).q ∨
    ∃ e f r : Fin 3 → ℚ,
      (∀ i, value? fmt.interchange (vsub fmt.interchange (y 1) (y 0) i)=some (e i)) ∧
      (∀ i, value? fmt.interchange (vsub fmt.interchange (y 2) (y 0) i)=some (f i)) ∧
      (∀ i, value? fmt.interchange (vsub fmt.interchange (y 0) x i)=some (r i)) ∧
      ∃ u' v' : ℝ, 0≤u' ∧ 0≤v' ∧ u'+v'≤1 ∧ (u'=0 ∨ u'+v'=1) ∧
        ‖residual (realVec r) (realVec e) (realVec f) u' v'‖≤
          d+(1601/100)*fmt.rho*((7/2)*L)+5*fourthRoot fmt.leastSubnormal := by
  let I := fmt.interchange
  let D : ℝ := (7/2)*L
  let k : ℝ := fmt.rho*D
  let budget := EvaluateLower.format_budget fmt hL hadm hlarge
  have hρ := (format_parameters fmt).1
  have hk : 0≤k := by dsimp [k,D]; rw [←hρ]; exact mul_nonneg I.format.unitRoundoff_pos.le (by positivity)
  obtain ⟨e,f,r,he,hf,hr,heC,hfC,hrC,heD,hfD,hrD,hRE,hRF⟩ :=
    FaceCoordinates.face_geometry I ha hb hc hx hL hA hB hC hX budget.rho budget.eta budget.linear
  have er := WordGeometryTransfer.difference_error I ha hx hr hL hA hX budget.rho budget.eta budget.linear
  have ee := WordGeometryTransfer.difference_error I hb ha he hL hB hA budget.rho budget.eta budget.linear
  have ef := WordGeometryTransfer.difference_error I hc ha hf hL hC hA budget.rho budget.eta budget.linear
  rw [hρ] at er ee ef
  have hw' := common_witness_two hk hu hv huv er ee ef hw
  have hd' : 0≤d+2*k := by positivity
  rcases local_accurate_face_or_edge fmt he hf hr hL hadm hlarge heD hfD hrD hRE hRF heC hfC hrC hd' hu hv huv hw' with hfup | ⟨u',v',hu',hv',huv',hbd,hbound⟩
  · exact Or.inl (upper_mono hfup (by dsimp [k,D]; ring_nf; rfl))
  · exact Or.inr ⟨e,f,r,he,hf,hr,u',v',hu',hv',huv',hbd,by dsimp [k,D] at hbound ⊢; nlinarith only [hbound]⟩

theorem accurate_face_or_original_boundary (fmt : Format)
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
    Upper fmt.interchange (d+21*fmt.rho*((7/2)*L)+5*fourthRoot fmt.leastSubnormal)
      (face fmt.interchange (vsub fmt.interchange (y 0) x) (vsub fmt.interchange (y 1) (y 0))
        (vsub fmt.interchange (y 2) (y 0))
        (cross3Accurate fmt.interchange (vsub fmt.interchange (y 1) (y 0)) (vsub fmt.interchange (y 2) (y 0)))).q ∨
    ∃ u' v' : ℝ, 0≤u' ∧ 0≤v' ∧ u'+v'≤1 ∧ (u'=0 ∨ u'+v'=1) ∧
      ‖realVec A-realVec X+u'•(realVec B-realVec A)+v'•(realVec C-realVec A)‖≤
        d+(1801/100)*fmt.rho*((7/2)*L)+5*fourthRoot fmt.leastSubnormal := by
  rcases accurate_face_or_boundary fmt hx ha hb hc hX hA hB hC hL hadm hlarge hd hu hv huv hw with hf | ⟨e,f,r,he,hf,hr,u',v',hu',hv',huv',hbd,hbound⟩
  · exact Or.inl hf
  · let budget := EvaluateLower.format_budget fmt hL hadm hlarge
    have hρ := (format_parameters fmt).1
    have hk : 0≤fmt.rho*((7/2)*L) := by rw [←hρ]; exact mul_nonneg fmt.interchange.format.unitRoundoff_pos.le (by positivity)
    have er := WordGeometryTransfer.difference_error fmt.interchange ha hx hr hL hA hX budget.rho budget.eta budget.linear
    have ee := WordGeometryTransfer.difference_error fmt.interchange hb ha he hL hB hA budget.rho budget.eta budget.linear
    have ef := WordGeometryTransfer.difference_error fmt.interchange hc ha hf hL hC hA budget.rho budget.eta budget.linear
    rw [hρ] at er ee ef
    have h := common_witness_reverse hk hu' hv' huv' er ee ef hbound
    exact Or.inr ⟨u',v',hu',hv',huv',hbd,by nlinarith only [h]⟩

end DistanceAccuracy.PointTriangleUpper

import DistanceAccuracy.CrossingInputCoverage
import DistanceAccuracy.EnvelopeBudget
import DistanceAccuracy.TriangleCarrier

namespace DistanceAccuracy.CrossingUpper
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge DistanceAccuracy.Geometry UpperSelection
open CrossingInputCoverage
set_option maxHeartbeats 1500000

def crossCandidate (I : Interchange) [I.Valid] (x : Segment I) (y : Triangle I) : Candidate I :=
  crossing I x (y 0) (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
    (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))
def faceCandidate (I : Interchange) [I.Valid] (x : Segment I) (y : Triangle I) (k : Fin 2) : Candidate I :=
  face I (vsub I (y 0) (x k)) (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0))
    (cross3Accurate I (vsub I (y 1) (y 0)) (vsub I (y 2) (y 0)))
noncomputable def commonResidual (I : Interchange) [I.Valid] (x : Segment I) (y : Triangle I) (s u v : ℝ) : Geometry.E3 :=
  decodeVec I (vsub I (y 0) (x 0))-s • decodeVec I (vsub I (x 1) (x 0))+
  u • decodeVec I (vsub I (y 1) (y 0))+v • decodeVec I (vsub I (y 2) (y 0))
def CommonBoundary (I : Interchange) [I.Valid] (x : Segment I) (y : Triangle I) (B : ℝ) : Prop :=
  ∃ s u v : ℝ, s∈Set.Icc (0:ℝ) 1 ∧ 0 ≤ u ∧ 0 ≤ v ∧ u+v ≤ 1 ∧
    (u=0 ∨ v=0 ∨ u+v=1) ∧ ‖commonResidual I x y s u v‖ ≤ B

lemma large_scale_pos (fmt : Format) {L : ℝ} (hl : fourthRoot fmt.leastNormal/64 ≤ L) :
    0<fmt.rho*((7/2)*L) := by
  have hh : 0<fourthRoot fmt.leastNormal := by
    unfold fourthRoot
    apply Real.sqrt_pos.mpr
    apply Real.sqrt_pos.mpr
    cases fmt <;> norm_num [Format.leastNormal]
  have hL : 0<L := (div_pos hh (by norm_num)).trans_le hl
  have hr : 0<fmt.rho := by cases fmt <;> norm_num [Format.rho]
  positivity

lemma upper_mono (I : Interchange) {a b : ℝ} {w : I.Word} (h : Upper I a w) (hab : a ≤ b) : Upper I b w := by
  obtain ⟨q,hq,hb⟩ := h
  exact ⟨q,hq,hb.trans hab⟩

theorem common_cover (fmt : Format) {x : Segment fmt.interchange} {y : Triangle fmt.interchange}
    {L s₀ u₀ v₀ : ℝ}
    (hadm : admissible fmt.interchange (.segment x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L)
    (hs₀ : s₀∈Set.Icc (0:ℝ) 1) (hu₀ : 0 ≤ u₀) (hv₀ : 0 ≤ v₀) (huv₀ : u₀+v₀ ≤ 1)
    (hw : ‖commonResidual fmt.interchange x y s₀ u₀ v₀‖ ≤ 3*fmt.rho*((7/2)*L)) :
    Upper fmt.interchange (24*fmt.rho*((7/2)*L)+7*fourthRoot fmt.leastSubnormal) (crossCandidate fmt.interchange x y).q ∨
    (∃ k, Upper fmt.interchange (24*fmt.rho*((7/2)*L)+7*fourthRoot fmt.leastSubnormal) (faceCandidate fmt.interchange x y k).q) ∨
    CommonBoundary fmt.interchange x y (20.2*fmt.rho*((7/2)*L)+7*fourthRoot fmt.leastSubnormal) := by
  let I := fmt.interchange
  let E := decodeVec I (vsub I (y 1) (y 0))
  let Fv := decodeVec I (vsub I (y 2) (y 0))
  let R := decodeVec I (vsub I (y 0) (x 0))
  let P := decodeVec I (vsub I (x 1) (x 0))
  let N := GeometryCoverage.exactCross E Fv
  let S : ℝ := fmt.rho*((7/2)*L)
  let h := fourthRoot fmt.leastSubnormal
  have hS : 0<S := large_scale_pos fmt hlarge
  have hh : 0 ≤ h := fourthRoot_nonneg _
  have hw' : ‖R-s₀ • P+u₀ • E+v₀ • Fv‖ ≤ 3*S := by
    change ‖R-s₀ • P+u₀ • E+v₀ • Fv‖ ≤ 3*fmt.rho*((7/2)*L) at hw
    dsimp [S]; nlinarith only [hw]
  by_cases hthin : ‖E‖ ≤ h ∨ ‖N‖ ≤ 16*fmt.rho*‖E‖*((7/2)*L) ∨ ‖N‖ ≤ h^2
  · obtain ⟨u,v,hu,hv,huv,hbd,hd⟩ := GeometryCoverage.combined_thin_edge_witness
      (R := R-s₀ • P) hu₀ hv₀ huv₀ fmt.rho_nonneg (show 0 ≤ (7/2:ℝ)*L by linarith [hadm.1]) hh hthin
    right; right
    refine ⟨s₀,u,v,hs₀,hu,hv,huv,?_ ,?_⟩
    · rcases hbd with hbd | hbd
      · exact Or.inl hbd
      · exact Or.inr (Or.inr hbd)
    · have ht := norm_add_le (R-s₀ • P+u₀ • E+v₀ • Fv)
        ((R-s₀ • P+u • E+v • Fv)-(R-s₀ • P+u₀ • E+v₀ • Fv))
      have hid : (R-s₀ • P+u₀ • E+v₀ • Fv)+((R-s₀ • P+u • E+v • Fv)-(R-s₀ • P+u₀ • E+v₀ • Fv)) =
          R-s₀ • P+u • E+v • Fv := by module
      rw [hid,norm_sub_rev (R-s₀ • P+u • E+v • Fv) (R-s₀ • P+u₀ • E+v₀ • Fv)] at ht
      dsimp [GeometryCoverage.residual] at hd
      change ‖R-s₀ • P+u • E+v • Fv‖ ≤ 20.2*fmt.rho*((7/2)*L)+7*h
      dsimp [S] at hw' hS
      nlinarith only [hw',hd,ht,hS,hh]
  · push_neg at hthin
    have hA : h<‖E‖ := hthin.1
    have hfloor : h^2 ≤ ‖N‖ := hthin.2.2.le
    have hthick : 16*fmt.rho*‖E‖*((7/2)*L) ≤ ‖N‖ := hthin.2.1.le
    have hN : N≠0 := norm_pos_iff.mp ((sq_nonneg h).trans_lt hthin.2.2)
    have endpoint (k : Fin 2) (hk : |inner ℝ N (R-(k.val:ℝ) • P)|/‖N‖ ≤ 3*fmt.rho*((7/2)*L)) :
        (∃ k, Upper I (24*fmt.rho*((7/2)*L)+7*h) (faceCandidate I x y k).q) ∨
        CommonBoundary I x y (20.2*fmt.rho*((7/2)*L)+7*h) := by
      have hout := endpoint_cover fmt k hadm hlarge hA hN hs₀ hu₀ hv₀ huv₀ hk hw
      rcases hout with hf | ⟨s,u,v,hs,hu,hv,huv,hbd,hbound⟩
      · left; refine ⟨k,upper_mono I hf ?_⟩
        have hm := mul_le_mul_of_nonneg_left endpoint_face_coefficient.le hS.le
        dsimp [S] at hm
        change _ ≤ 24*fmt.rho*((7/2)*L)+7*h
        nlinarith only [hm,hh]
      · right; refine ⟨s,u,v,hs,hu,hv,huv,hbd,?_⟩
        have hm := mul_le_mul_of_nonneg_left endpoint_boundary_coefficient.le hS.le
        dsimp [S] at hm
        change ‖commonResidual I x y s u v‖ ≤ 20.2*fmt.rho*((7/2)*L)+7*h
        dsimp [commonResidual,I,h] at *
        nlinarith only [hm,hbound,hh]
    rcases GeometryCoverage.witness_root_or_endpoint hN hs₀.1 hs₀.2 (show 0 ≤ 3*S by positivity) hw' with
      ⟨t,ht,hroot⟩ | hend | hend
    · have hout := thick_root fmt hadm hlarge hA hfloor hthick hs₀ hu₀ hv₀ huv₀ ht.1 ht.2 hroot hw
      rcases hout with hc | ⟨s,u,v,hs,hu,hv,huv,hbd,hbound⟩
      · left
        apply upper_mono I hc
        have hm := mul_le_mul_of_nonneg_left crossing_face_coefficient.le hS.le
        change S*(V (42/5)+4.54)+6*h ≤ 24*fmt.rho*((7/2)*L)+7*h
        dsimp [S] at hm
        rw [show (42/5:ℝ)=8.4 by norm_num]
        dsimp [S]
        nlinarith only [hm,hh]
      · right; right
        refine ⟨s,u,v,hs,hu,hv,huv,hbd,?_⟩
        have hm := mul_le_mul_of_nonneg_left crossing_boundary_coefficient.le hS.le
        change ‖commonResidual I x y s u v‖ ≤ 20.2*fmt.rho*((7/2)*L)+7*h
        norm_num only [show (42/5:ℝ)=8.4 by norm_num] at hbound
        dsimp [S] at hm
        dsimp [commonResidual,I,h] at *
        nlinarith only [hm,hbound]
    · exact Or.inr (endpoint 0 (by simpa only [Fin.val_zero,Nat.cast_zero,zero_smul,sub_zero,S,mul_assoc] using hend))
    · exact Or.inr (endpoint 1 (by simpa only [Fin.val_one,Nat.cast_one,one_smul,S,mul_assoc] using hend))

/-- Every original intersection is covered by the executable crossing/face
candidates or a common segment/edge witness, including degenerate triangles. -/
theorem large_cover (fmt : Format) {x : Segment fmt.interchange} {y : Triangle fmt.interchange} {L : ℝ}
    (hadm : admissible fmt.interchange (.segment x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L)
    (hd : distance fmt.interchange (.segment x) (.triangle y)=0) :
    Upper fmt.interchange (24*fmt.rho*((7/2)*L)+7*fourthRoot fmt.leastSubnormal) (crossCandidate fmt.interchange x y).q ∨
    (∃ k, Upper fmt.interchange (24*fmt.rho*((7/2)*L)+7*fourthRoot fmt.leastSubnormal) (faceCandidate fmt.interchange x y k).q) ∨
    CommonBoundary fmt.interchange x y (20.2*fmt.rho*((7/2)*L)+7*fourthRoot fmt.leastSubnormal) := by
  let I := fmt.interchange
  obtain ⟨a,ha,b,hb,he⟩ := closest_pair I (.segment x) (.triangle y)
  obtain ⟨s,hs,rfl⟩ := (show a∈(fun s : ℝ => decodeVec I (x 0)+s • (decodeVec I (x 1)-decodeVec I (x 0))) '' Set.Icc 0 1 by
    simpa only [segment_carrier] using ha)
  obtain ⟨u,v,hu,hv,huv,rfl⟩ := (triangle_carrier I y b).mp hb
  have hz := norm_eq_zero.mp (he.symm.trans hd)
  have hw := intersection_common fmt hadm hlarge hs hu hv huv hz
  exact common_cover fmt hadm hlarge hs hu hv huv hw

end DistanceAccuracy.CrossingUpper

import DistanceAccuracy.BoundaryEdgeUpper
import DistanceAccuracy.EnvelopeBudget
import DistanceAccuracy.CrossingUpper
import DistanceAccuracy.SharpGlobalUpperAssembly
namespace DistanceAccuracy.CrossingFinal
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge
open DistanceAccuracy.Geometry UpperSelection

lemma scale_positive (fmt : Format) {L : ℝ}
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L) : 0 < fmt.rho*((7/2)*L) := by
  have hH : 0 < fourthRoot fmt.leastNormal := by
    unfold fourthRoot
    apply Real.sqrt_pos.mpr
    apply Real.sqrt_pos.mpr
    cases fmt <;> norm_num [Format.leastNormal]
  have hρ : 0 < fmt.rho := by cases fmt <;> norm_num [Format.rho]
  have hL : 0 < L := by linarith
  positivity

lemma boundary_envelope (fmt : Format) {L : ℝ}
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L) :
    fmt.rho*((7/2)*L)*F (((20.2*fmt.rho*((7/2)*L)+7*fourthRoot fmt.leastSubnormal)+
      4*fmt.rho*((7/2)*L))/(fmt.rho*((7/2)*L)))+
        3.55*fmt.rho*((7/2)*L)+6*fourthRoot fmt.leastSubnormal ≤
      36.4*fmt.rho*((7/2)*L)+13*fourthRoot fmt.leastSubnormal := by
  have hS := scale_positive fmt hlarge
  have hh : 0 ≤ fourthRoot fmt.leastSubnormal := Real.sqrt_nonneg _
  have hm := scaled_F_bound (S:=fmt.rho*((7/2)*L))
    (d:=20.2*fmt.rho*((7/2)*L)+7*fourthRoot fmt.leastSubnormal+4*fmt.rho*((7/2)*L))
    (b:=(24.2:ℝ)) (e:=7*fourthRoot fmt.leastSubnormal) hS
    (by nlinarith) (by norm_num) (by positivity) (by nlinarith)
  have hc := mul_le_mul_of_nonneg_right crossing_edge_coefficient.le hS.le
  nlinarith

/-- Any boundary output of the crossing geometry bounds an actual segment/edge
candidate in both orientations. -/
theorem boundary (fmt : Format)
    {x : Segment fmt.interchange} {y : Triangle fmt.interchange} {L s u v : ℝ}
    (hadm : admissible fmt.interchange (.segment x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L)
    (hs : s ∈ Set.Icc (0:ℝ) 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v ≤ 1)
    (hb : u=0 ∨ v=0 ∨ u+v=1)
    (hw : ‖decodeVec fmt.interchange (vsub fmt.interchange (y 0) (x 0))-
      s•decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0))+
      u•decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0))+
      v•decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0))‖ ≤
        20.2*fmt.rho*((7/2)*L)+7*fourthRoot fmt.leastSubnormal) :
    ∃ e ∈ edges,
      Upper fmt.interchange (36.4*fmt.rho*((7/2)*L)+13*fourthRoot fmt.leastSubnormal)
        (segmentSegment fmt.interchange x (edge fmt.interchange y e)).q ∧
      Upper fmt.interchange (36.4*fmt.rho*((7/2)*L)+13*fourthRoot fmt.leastSubnormal)
        (segmentSegment fmt.interchange (edge fmt.interchange y e) x).q := by
  have hw' : ‖decodeVec fmt.interchange (vsub fmt.interchange (y 0) (x 0))+
      u•decodeVec fmt.interchange (vsub fmt.interchange (y 1) (y 0))+
      v•decodeVec fmt.interchange (vsub fmt.interchange (y 2) (y 0))-
      s•decodeVec fmt.interchange (vsub fmt.interchange (x 1) (x 0))‖ ≤
      20.2*fmt.rho*((7/2)*L)+7*fourthRoot fmt.leastSubnormal := by
    convert hw using 1
    congr 1
    module
  obtain ⟨e,he,hf,hr⟩ := BoundaryEdgeUpper.boundary_upper fmt hadm hlarge hs hu hv huv hb hw'
  obtain ⟨qf,hqf,hf⟩ := hf
  obtain ⟨qr,hqr,hr⟩ := hr
  exact ⟨e,he,⟨qf,hqf,hf.trans (boundary_envelope fmt hlarge)⟩,
    ⟨qr,hqr,hr.trans (boundary_envelope fmt hlarge)⟩⟩

/-- End-to-end crossing coverage, including both orientations of every edge
candidate, from finite admissible input coordinates and actual intersection. -/
theorem large_cover (fmt : Format) (x : Segment fmt.interchange)
    (y : Triangle fmt.interchange) (L : ℝ)
    (hadm : admissible fmt.interchange (.segment x) (.triangle y) L)
    (hlarge : fourthRoot fmt.leastNormal/64 ≤ L)
    (hzero : distance fmt.interchange (.segment x) (.triangle y)=0) :
    Upper fmt.interchange (36.4*fmt.rho*((7/2)*L)+13*fourthRoot fmt.leastSubnormal)
      (SharpGlobalUpperAssembly.segCross fmt.interchange x y).q ∨
    (∃ k, Upper fmt.interchange (36.4*fmt.rho*((7/2)*L)+13*fourthRoot fmt.leastSubnormal)
      (SharpGlobalUpperAssembly.segFace fmt.interchange x y k).q) ∨
    (∃ e ∈ edges,
      Upper fmt.interchange (36.4*fmt.rho*((7/2)*L)+13*fourthRoot fmt.leastSubnormal)
        (segmentSegment fmt.interchange x (edge fmt.interchange y e)).q ∧
      Upper fmt.interchange (36.4*fmt.rho*((7/2)*L)+13*fourthRoot fmt.leastSubnormal)
        (segmentSegment fmt.interchange (edge fmt.interchange y e) x).q) := by
  have hS := (scale_positive fmt hlarge).le
  have hh : 0 ≤ fourthRoot fmt.leastSubnormal := Real.sqrt_nonneg _
  have hm : 24*fmt.rho*((7/2)*L)+7*fourthRoot fmt.leastSubnormal ≤
      36.4*fmt.rho*((7/2)*L)+13*fourthRoot fmt.leastSubnormal := by nlinarith
  rcases CrossingUpper.large_cover fmt hadm hlarge hzero with hc | hf | hb
  · exact Or.inl (SharpGlobalUpperAssembly.upper_mono fmt.interchange hc hm)
  · obtain ⟨k,hk⟩ := hf
    exact Or.inr (Or.inl ⟨k,SharpGlobalUpperAssembly.upper_mono fmt.interchange hk hm⟩)
  · obtain ⟨s,u,v,hs,hu,hv,huv,hbd,hw⟩ := hb
    exact Or.inr (Or.inr (boundary fmt hadm hlarge hs hu hv huv hbd hw))
end DistanceAccuracy.CrossingFinal

import DistanceAccuracy.PlaneProjection
import DistanceAccuracy.GeometryCrossing

namespace DistanceAccuracy.GeometryCoverage
open Matrix WithLp

/-- A bounded normal height at a clamped segment point yields either a
feasible face witness at that point or a segment/edge witness. This exact
geometric step includes intersections at vertices and degenerate segments. -/
theorem crossing_plane_or_edge {R P E F : E3} {s₀ s₁ u₀ v₀ B : ℝ}
    (hN : exactCross E F ≠ 0)
    (hs₀ : s₀ ∈ Set.Icc (0:ℝ) 1) (hs₁ : s₁ ∈ Set.Icc (0:ℝ) 1)
    (hu₀ : 0≤u₀) (hv₀ : 0≤v₀) (huv₀ : u₀+v₀≤1)
    (hwitness : ‖R+s₀ • P+u₀ • E+v₀ • F‖≤B)
    (hheight : |inner ℝ (exactCross E F) (R+s₁ • P)|/‖exactCross E F‖≤B) :
    (∃ u v : ℝ, 0≤u ∧ 0≤v ∧ u+v≤1 ∧ ‖R+s₁ • P+u • E+v • F‖≤B) ∨
    ∃ s u v : ℝ, s ∈ Set.Icc (0:ℝ) 1 ∧ 0≤u ∧ 0≤v ∧ u+v≤1 ∧
      (u=0 ∨ v=0 ∨ u+v=1) ∧ ‖R+s • P+u • E+v • F‖≤B := by
  obtain ⟨u,v,hproj⟩ := plane_projection_exists (R+s₁ • P) E F hN
  have hp := hproj.le.trans hheight
  by_cases hu : 0≤u
  · by_cases hv : 0≤v
    · by_cases huv : u+v≤1
      · exact Or.inl ⟨u,v,hu,hv,huv,hp⟩
      · exact Or.inr (crossing_boundary_witness hs₀ hs₁ hu₀ hv₀ huv₀
          (Or.inr (Or.inr (le_of_not_ge huv))) hwitness hp)
    · exact Or.inr (crossing_boundary_witness hs₀ hs₁ hu₀ hv₀ huv₀
        (Or.inr (Or.inl (le_of_not_ge hv))) hwitness hp)
  · exact Or.inr (crossing_boundary_witness hs₀ hs₁ hu₀ hv₀ huv₀
      (Or.inl (le_of_not_ge hu)) hwitness hp)

/-- The same dichotomy when the algorithm uses a rounded affine origin Q.
The rounding discrepancy is paid once when transferring an outside projection
back to the common segment geometry. -/
theorem crossing_rounded_plane_or_edge {R P E F Q : E3} {s₀ s₁ u₀ v₀ B delta : ℝ}
    (hN : exactCross E F ≠ 0)
    (hs₀ : s₀ ∈ Set.Icc (0:ℝ) 1) (hs₁ : s₁ ∈ Set.Icc (0:ℝ) 1)
    (hu₀ : 0≤u₀) (hv₀ : 0≤v₀) (huv₀ : u₀+v₀≤1)
    (hwitness : ‖R+s₀ • P+u₀ • E+v₀ • F‖≤B+delta)
    (hshift : ‖R+s₁ • P-Q‖≤delta)
    (hheight : |inner ℝ (exactCross E F) Q|/‖exactCross E F‖≤B) :
    (∃ u v : ℝ, 0≤u ∧ 0≤v ∧ u+v≤1 ∧ ‖Q+u • E+v • F‖≤B) ∨
    ∃ s u v : ℝ, s ∈ Set.Icc (0:ℝ) 1 ∧ 0≤u ∧ 0≤v ∧ u+v≤1 ∧
      (u=0 ∨ v=0 ∨ u+v=1) ∧ ‖R+s • P+u • E+v • F‖≤B+delta := by
  obtain ⟨u,v,hproj⟩ := plane_projection_exists Q E F hN
  have hp := hproj.le.trans hheight
  have ht : ‖R+s₁ • P+u • E+v • F‖≤B+delta := by
    calc
      _ = ‖(Q+u • E+v • F)+(R+s₁ • P-Q)‖ := by congr 1; module
      _ ≤ ‖Q+u • E+v • F‖+‖R+s₁ • P-Q‖ := norm_add_le _ _
      _ ≤ B+delta := add_le_add hp hshift
  by_cases hu : 0≤u
  · by_cases hv : 0≤v
    · by_cases huv : u+v≤1
      · exact Or.inl ⟨u,v,hu,hv,huv,hp⟩
      · exact Or.inr (crossing_boundary_witness hs₀ hs₁ hu₀ hv₀ huv₀
          (Or.inr (Or.inr (le_of_not_ge huv))) hwitness ht)
    · exact Or.inr (crossing_boundary_witness hs₀ hs₁ hu₀ hv₀ huv₀
        (Or.inr (Or.inl (le_of_not_ge hv))) hwitness ht)
  · exact Or.inr (crossing_boundary_witness hs₀ hs₁ hu₀ hv₀ huv₀
      (Or.inl (le_of_not_ge hu)) hwitness ht)

/-- Compose rounded plane projection with a local face candidate-or-edge
result. The local numerical theorem supplies hit; the geometric composition
preserves its nonlinear bound C and adds only the affine-origin discrepancy. -/
theorem crossing_face_or_edge {R P E F Q : E3} {s₀ s₁ u₀ v₀ B C delta : ℝ} {hit : Prop}
    (hN : exactCross E F ≠ 0)
    (hs₀ : s₀ ∈ Set.Icc (0:ℝ) 1) (hs₁ : s₁ ∈ Set.Icc (0:ℝ) 1)
    (hu₀ : 0≤u₀) (hv₀ : 0≤v₀) (huv₀ : u₀+v₀≤1)
    (hwitness : ‖R+s₀ • P+u₀ • E+v₀ • F‖≤B+delta)
    (hshift : ‖R+s₁ • P-Q‖≤delta)
    (hheight : |inner ℝ (exactCross E F) Q|/‖exactCross E F‖≤B)
    (hface : ∀ u v : ℝ, 0≤u → 0≤v → u+v≤1 → ‖Q+u • E+v • F‖≤B →
      hit ∨ ∃ u' v' : ℝ, 0≤u' ∧ 0≤v' ∧ u'+v'≤1 ∧ (u'=0 ∨ u'+v'=1) ∧
        ‖Q+u' • E+v' • F‖≤C) :
    hit ∨ ∃ s u v : ℝ, s ∈ Set.Icc (0:ℝ) 1 ∧ 0≤u ∧ 0≤v ∧ u+v≤1 ∧
      (u=0 ∨ v=0 ∨ u+v=1) ∧ ‖R+s • P+u • E+v • F‖≤ max B C+delta := by
  rcases crossing_rounded_plane_or_edge hN hs₀ hs₁ hu₀ hv₀ huv₀ hwitness hshift hheight with
    ⟨u,v,hu,hv,huv,hb⟩ | ⟨s,u,v,hs,hu,hv,huv,hbd,hb⟩
  · rcases hface u v hu hv huv hb with hhit | ⟨u',v',hu',hv',huv',hbd',hb'⟩
    · exact Or.inl hhit
    · right
      refine ⟨s₁,u',v',hs₁,hu',hv',huv',?_,?_⟩
      · rcases hbd' with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · calc
          _ = ‖(Q+u' • E+v' • F)+(R+s₁ • P-Q)‖ := by congr 1; module
          _ ≤ ‖Q+u' • E+v' • F‖+‖R+s₁ • P-Q‖ := norm_add_le _ _
          _ ≤ C+delta := add_le_add hb' hshift
          _ ≤ max B C+delta := add_le_add (le_max_right B C) (le_refl delta)
  · exact Or.inr ⟨s,u,v,hs,hu,hv,huv,hbd,hb.trans (add_le_add (le_max_left B C) (le_refl delta))⟩

/-- A nearby segment-plane witness either guarantees a plane root on the
segment or supplies an endpoint with at least as small a plane residual.
This avoids assuming rounded geometry preserves an original intersection. -/
lemma affine_root_or_endpoint {a b t B : ℝ} (ht0 : 0≤t) (ht1 : t≤1)
    (hB : 0≤B) (hw : |a-t*b|≤B) :
    (∃ s ∈ Set.Icc (0:ℝ) 1, a-s*b=0) ∨ |a|≤B ∨ |a-b|≤B := by
  by_cases ha : |a|≤B
  · exact Or.inr (Or.inl ha)
  by_cases hb : |a-b|≤B
  · exact Or.inr (Or.inr hb)
  left
  have hcont : Continuous (fun s : ℝ => a-s*b) := by fun_prop
  have hw' := abs_le.mp hw
  rcases lt_or_gt_of_ne (show a≠0 by intro hz; rw [hz,abs_zero] at ha; exact ha hB) with han | hap
  · have haB : a < -B := by rw [abs_of_neg han] at ha; linarith
    have hend : 0≤a-b := by
      by_contra hn
      have hbn : a-b<0 := lt_of_not_ge hn
      rw [abs_of_neg hbn] at hb
      have hbB : a-b < -B := by linarith
      have hc := mul_nonneg ht0 (show 0≤ -B-(a-b) by linarith)
      have hd := mul_nonneg (show 0≤1-t by linarith) (show 0≤ -B-a by linarith)
      have ht : t<1 := by
        by_contra h
        have ht : t=1 := by linarith
        rw [ht] at hw'
        simp only [one_mul] at hw'
        linarith
      have hp := mul_pos (show 0< -B-a by linarith) (show 0<1-t by linarith)
      nlinarith
    obtain ⟨s,hs,hzero⟩ := intermediate_value_Icc (show (0:ℝ)≤1 by norm_num)
      hcont.continuousOn (show 0∈Set.Icc (a-0*b) (a-1*b) by simpa using And.intro han.le hend)
    exact ⟨s,hs,hzero⟩
  · have haB : B<a := by rw [abs_of_pos hap] at ha; linarith
    have hend : a-b≤0 := by
      by_contra hn
      have hbp : 0<a-b := lt_of_not_ge hn
      rw [abs_of_pos hbp] at hb
      have hbB : B<a-b := by linarith
      have hc := mul_nonneg ht0 (show 0≤a-b-B by linarith)
      have hd := mul_nonneg (show 0≤1-t by linarith) (show 0≤a-B by linarith)
      have ht : t<1 := by
        by_contra h
        have ht : t=1 := by linarith
        rw [ht] at hw'
        simp only [one_mul] at hw'
        linarith
      have hp := mul_pos (show 0<a-B by linarith) (show 0<1-t by linarith)
      nlinarith
    obtain ⟨s,hs,hzero⟩ := intermediate_value_Icc' (show (0:ℝ)≤1 by norm_num)
      hcont.continuousOn (show 0∈Set.Icc (a-1*b) (a-0*b) by simpa using And.intro hend hap.le)
    exact ⟨s,hs,hzero⟩

lemma plane_root_or_endpoint {N R P : E3} {t B : ℝ}
    (hN : N≠0) (ht0 : 0≤t) (ht1 : t≤1) (hB : 0≤B)
    (hw : |inner ℝ N (R-t • P)|/‖N‖≤B) :
    (∃ s ∈ Set.Icc (0:ℝ) 1, inner ℝ N (R-s • P)=0) ∨
      |inner ℝ N R|/‖N‖≤B ∨ |inner ℝ N (R-P)|/‖N‖≤B := by
  have hn : 0<‖N‖ := norm_pos_iff.mpr hN
  have hw' := (div_le_iff₀ hn).mp hw
  simp only [inner_sub_right,inner_smul_right] at hw'
  rcases affine_root_or_endpoint ht0 ht1 (mul_nonneg hB hn.le) hw' with
    ⟨s,hs,hzero⟩ | hzero | hone
  · exact Or.inl ⟨s,hs,by simpa only [inner_sub_right,inner_smul_right] using hzero⟩
  · exact Or.inr (Or.inl ((div_le_iff₀ hn).mpr hzero))
  · exact Or.inr (Or.inr ((div_le_iff₀ hn).mpr (by simpa only [inner_sub_right] using hone)))

lemma cross_normal_orthogonal (E F : E3) :
    inner ℝ (exactCross E F) E=0 ∧ inner ℝ (exactCross E F) F=0 := by
  constructor <;>
    simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_succ,exactCross,crossProduct] <;> ring

lemma plane_height_le_residual (R E F : E3) (u v : ℝ) (hN : exactCross E F≠0) :
    |inner ℝ (exactCross E F) R|/‖exactCross E F‖ ≤ ‖R+u • E+v • F‖ := by
  have hn : 0<‖exactCross E F‖ := norm_pos_iff.mpr hN
  obtain ⟨he,hf⟩ := cross_normal_orthogonal E F
  have hi : inner ℝ (exactCross E F) (R+u • E+v • F) = inner ℝ (exactCross E F) R := by
    simp only [inner_add_right,inner_smul_right,he,hf,mul_zero,add_zero]
  have hh := abs_real_inner_le_norm (exactCross E F) (R+u • E+v • F)
  rw [hi] at hh
  apply (div_le_iff₀ hn).mpr
  simpa only [mul_comm] using hh

/-- A common rounded segment/triangle witness supplies the plane-root or
endpoint alternative even when the original exact intersection was lost. -/
lemma witness_root_or_endpoint {R P E F : E3} {t u v B : ℝ}
    (hN : exactCross E F≠0) (ht0 : 0≤t) (ht1 : t≤1) (hB : 0≤B)
    (hw : ‖R-t • P+u • E+v • F‖≤B) :
    (∃ s ∈ Set.Icc (0:ℝ) 1, inner ℝ (exactCross E F) (R-s • P)=0) ∨
      |inner ℝ (exactCross E F) R|/‖exactCross E F‖≤B ∨
      |inner ℝ (exactCross E F) (R-P)|/‖exactCross E F‖≤B := by
  exact plane_root_or_endpoint hN ht0 ht1 hB ((plane_height_le_residual (R-t • P) E F u v hN).trans hw)

lemma plane_height_shift {N R Q : E3} {B delta : ℝ} (hN : N≠0)
    (hheight : |inner ℝ N R|/‖N‖≤B) (hshift : ‖R-Q‖≤delta) :
    |inner ℝ N Q|/‖N‖≤B+delta := by
  have hn : 0<‖N‖ := norm_pos_iff.mpr hN
  have h0 := (div_le_iff₀ hn).mp hheight
  have hi := abs_add_le (inner ℝ N R) (inner ℝ N (Q-R))
  have hid : inner ℝ N R+inner ℝ N (Q-R)=inner ℝ N Q := by
    rw [inner_sub_right]; ring
  rw [hid] at hi
  have hc := abs_real_inner_le_norm N (Q-R)
  rw [norm_sub_rev Q R] at hc
  have hm := mul_le_mul_of_nonneg_left hshift hn.le
  apply (div_le_iff₀ hn).mpr
  nlinarith only [h0,hi,hc,hm]

end DistanceAccuracy.GeometryCoverage

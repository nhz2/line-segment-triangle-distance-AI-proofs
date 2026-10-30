import DistanceAccuracy.GeometryCoverage

namespace DistanceAccuracy.GeometryCoverage

/-- Three nonnegative slacks with a vanishing minimum put a point on one of
all three triangle edges. -/
lemma min_three_zero {a b c : ℝ} (h : min a (min b c)=0) :
    0≤a ∧ 0≤b ∧ 0≤c ∧ (a=0 ∨ b=0 ∨ c=0) := by
  have hnon : 0 ≤ min a (min b c) := le_of_eq h.symm
  have hslack : 0≤a ∧ 0≤b ∧ 0≤c := by simpa only [le_min_iff] using hnon
  refine ⟨hslack.1,hslack.2.1,hslack.2.2,?_⟩
  by_cases ha : a≤ min b c
  · exact Or.inl (by simpa only [min_eq_left ha] using h)
  · rw [min_eq_right (le_of_not_ge ha)] at h
    by_cases hb : b≤c
    · exact Or.inr (Or.inl (by simpa only [min_eq_left hb] using h))
    · exact Or.inr (Or.inr (by simpa only [min_eq_right (le_of_not_ge hb)] using h))

/-- Interpolate a segment/triangle witness to an outside plane projection.
The first boundary point supplies a segment/edge witness with no increase in
residual norm. The outside barycentric coordinates need not be bounded. -/
theorem crossing_boundary_witness {R P E F : E3} {s₀ s₁ u₀ v₀ u₁ v₁ B : ℝ}
    (hs₀ : s₀ ∈ Set.Icc (0:ℝ) 1) (hs₁ : s₁ ∈ Set.Icc (0:ℝ) 1)
    (hu₀ : 0≤u₀) (hv₀ : 0≤v₀) (huv₀ : u₀+v₀≤1)
    (hout : u₁≤0 ∨ v₁≤0 ∨ 1≤u₁+v₁)
    (h₀ : ‖R+s₀ • P+u₀ • E+v₀ • F‖≤B)
    (h₁ : ‖R+s₁ • P+u₁ • E+v₁ • F‖≤B) :
    ∃ s u v : ℝ, s ∈ Set.Icc (0:ℝ) 1 ∧ 0≤u ∧ 0≤v ∧ u+v≤1 ∧
      (u=0 ∨ v=0 ∨ u+v=1) ∧ ‖R+s • P+u • E+v • F‖≤B := by
  let g (t : ℝ) := min (mix u₀ u₁ t)
    (min (mix v₀ v₁ t) (1-mix u₀ u₁ t-mix v₀ v₁ t))
  have hg : Continuous g := by dsimp [g,mix]; fun_prop
  have hg0 : 0≤g 0 := by
    dsimp [g,mix]
    simp only [sub_zero,one_mul,zero_mul,add_zero]
    exact le_min hu₀ (le_min hv₀ (by linarith only [huv₀]))
  have hg1 : g 1≤0 := by
    dsimp [g,mix]
    simp only [sub_self,zero_mul,one_mul,zero_add]
    rcases hout with h | h | h
    · exact (min_le_left _ _).trans h
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans h
    · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (by linarith only [h])
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc' (show (0:ℝ)≤1 by norm_num)
    hg.continuousOn (show (0:ℝ)∈Set.Icc (g 1) (g 0) from ⟨hg1,hg0⟩)
  obtain ⟨hu,hv,hrest,hboundary⟩ := min_three_zero he
  refine ⟨mix s₀ s₁ t,mix u₀ u₁ t,mix v₀ v₁ t,
    ⟨mix_nonneg hs₀.1 hs₁.1 ht.1 ht.2,mix_le_one hs₀.2 hs₁.2 ht.1 ht.2⟩,
    hu,hv,by linarith only [hrest],?_,?_⟩
  · rcases hboundary with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by linarith only [h]))
  · have hid : R+mix s₀ s₁ t • P+mix u₀ u₁ t • E+mix v₀ v₁ t • F =
        (1-t) • (R+s₀ • P+u₀ • E+v₀ • F)+t • (R+s₁ • P+u₁ • E+v₁ • F) := by
      dsimp [mix]
      module
    rw [hid]
    exact norm_mix_le h₀ h₁ ht.1 ht.2

end DistanceAccuracy.GeometryCoverage

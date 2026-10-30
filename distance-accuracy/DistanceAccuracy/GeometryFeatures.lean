import DistanceAccuracy.GeometrySubsimplex

/-! Sparse representations for global nearest-feature coverage. The additional
coordinate records which simplex a vertex came from. -/
namespace DistanceAccuracy.GeometryFeatures
open DistanceAccuracy.Geometry
open scoped Pointwise

abbrev LiftSpace := ℝ × E3

lemma lift_finrank : Module.finrank ℝ LiftSpace = 4 := by
  simp [LiftSpace,Module.finrank_prod,finrank_euclideanSpace_fin]

/-- A supporting affine hyperplane lowers the Carathéodory bound by one. -/
lemma independent_card_supporting {ι : Type*} [Fintype ι]
    {z : ι → LiftSpace} (hz : AffineIndependent ℝ z)
    {f : LiftSpace →ₗ[ℝ] ℝ} (hf : f ≠ 0) {c : ℝ} (hc : ∀ i, f (z i) = c) :
    Fintype.card ι ≤ 4 := by
  have hspan : vectorSpan ℝ (Set.range z) ≤ f.ker := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro _ ⟨u,⟨i,rfl⟩,v,⟨j,rfl⟩,rfl⟩
    change f (z i-z j) = 0
    rw [map_sub,hc i,hc j,sub_self]
  have hk : f.ker ≠ ⊤ := by
    intro hk
    apply hf
    apply LinearMap.ext
    intro v
    have hv : v ∈ f.ker := by rw [hk]; trivial
    exact hv
  have hdim := Submodule.finrank_lt hk
  rw [lift_finrank] at hdim
  apply hz.card_le_finrank_succ.trans
  apply (Nat.add_le_add_right (Submodule.finrank_mono hspan) 1).trans
  exact hdim

/-- Strictly positive barycentric weights cannot average nonnegative supporting
slacks to zero unless every selected vertex belongs to the supporting plane. -/
lemma supporting_selected {ι : Type*} [Fintype ι] {z : ι → LiftSpace} {w : ι → ℝ}
    {x : LiftSpace} {f : LiftSpace →ₗ[ℝ] ℝ} {c : ℝ}
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) (hx : ∑ i, w i • z i = x)
    (hfx : f x = c) (hz : ∀ i, c ≤ f (z i)) : ∀ i, f (z i) = c := by
  have he : ∑ i, w i*(f (z i)-c) = 0 := by
    have hmap := congrArg f hx
    simp only [map_sum,map_smul,smul_eq_mul] at hmap
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,hsum,one_mul]
    linarith only [hmap,hfx]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (hw i).le (sub_nonneg.mpr (hz i)))).mp he
  intro i
  have hi := hzero i (Finset.mem_univ i)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (ne_of_gt (hw i)))

/-- Every lifted separation admits a representation by at most five vertices.
For two triangles this already forces one side onto an edge. -/
theorem sparse_lift {S : Set LiftSpace} {x : LiftSpace} (hx : x ∈ convexHull ℝ S) :
    ∃ (ι : Type) (_ : Fintype ι) (z : ι → LiftSpace) (w : ι → ℝ),
      Set.range z ⊆ S ∧ (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • z i = x) ∧ Fintype.card ι ≤ 5 := by
  obtain ⟨ι,hi,z,w,hz,hind,hw,hs,hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
  letI := hi
  refine ⟨ι,hi,z,w,hz,hw,hs,hx,?_⟩
  apply hind.card_le_finrank_succ.trans
  have hd := (vectorSpan ℝ (Set.range z)).finrank_le
  rw [lift_finrank] at hd
  exact Nat.add_le_add_right hd 1

/-- A lifted closest separation in a nontrivial supporting plane admits only
four vertices. Splitting them between the two inputs yields vertex/face or
edge/edge feature pairs. -/
theorem sparse_lift_supporting {S : Set LiftSpace} {x : LiftSpace}
    (hx : x ∈ convexHull ℝ S) {f : LiftSpace →ₗ[ℝ] ℝ} (hf : f ≠ 0)
    {c : ℝ} (hfx : f x = c) (hS : ∀ z ∈ S, c ≤ f z) :
    ∃ (ι : Type) (_ : Fintype ι) (z : ι → LiftSpace) (w : ι → ℝ),
      Set.range z ⊆ S ∧ (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • z i = x) ∧ Fintype.card ι ≤ 4 := by
  obtain ⟨ι,hi,z,w,hz,hind,hw,hs,hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
  letI := hi
  have hc := supporting_selected hw hs hx hfx (fun i => hS (z i) (hz ⟨i,rfl⟩))
  exact ⟨ι,hi,z,w,hz,hw,hs,hx,independent_card_supporting hind hf hc⟩

/-- The standard projection variational inequality derived directly from
minimality, with no smoothness assumption on the convex set. -/
lemma closest_normal {S : Set E3} (hS : Convex ℝ S) {a b : E3} (ha : a ∈ S)
    (hmin : ∀ x ∈ S, ‖b-a‖ ≤ ‖b-x‖) :
    ∀ x ∈ S, inner ℝ (b-a) (x-a) ≤ 0 := by
  letI : Nonempty S := ⟨⟨a,ha⟩⟩
  have hbd : BddBelow (Set.range (fun w : S => ‖b-(w:E3)‖)) := by
    refine ⟨0,?_⟩
    rintro _ ⟨w,rfl⟩
    exact norm_nonneg _
  have hnorm : ‖b-a‖ = ⨅ w : S, ‖b-(w:E3)‖ := le_antisymm
    (le_ciInf (fun w => hmin w w.property)) (ciInf_le hbd ⟨a,ha⟩)
  exact (norm_eq_iInf_iff_real_inner_le_zero hS ha).mp hnorm

noncomputable def leftLift : E3 →ᵃ[ℝ] LiftSpace :=
  (LinearMap.prod (0 : E3 →ₗ[ℝ] ℝ) (-LinearMap.id)).toAffineMap

noncomputable def rightLift : E3 →ᵃ[ℝ] LiftSpace :=
  (LinearMap.prod (0 : E3 →ₗ[ℝ] ℝ) LinearMap.id).toAffineMap+
    AffineMap.const ℝ E3 ((1:ℝ),(0:E3))

@[simp] lemma leftLift_apply (x : E3) : leftLift x = ((0:ℝ),-x) := rfl
@[simp] lemma rightLift_apply (x : E3) : rightLift x = ((1:ℝ),x) := by simp [rightLift]

/-- A separation is a midpoint in the augmented hull. The first coordinate
will force equal total weight from the two simplexes in every representation. -/
lemma separation_in_lifted_hull {X Y : Set E3} {a b : E3}
    (ha : a ∈ convexHull ℝ X) (hb : b ∈ convexHull ℝ Y) :
    ((1/2:ℝ),(1/2:ℝ) • (b-a)) ∈ convexHull ℝ
      ((leftLift '' X) ∪ (rightLift '' Y)) := by
  have hleft : leftLift a ∈ convexHull ℝ (leftLift '' X) := by
    rw [← AffineMap.image_convexHull]
    exact ⟨a,ha,rfl⟩
  have hright : rightLift b ∈ convexHull ℝ (rightLift '' Y) := by
    rw [← AffineMap.image_convexHull]
    exact ⟨b,hb,rfl⟩
  have hl : leftLift a ∈ convexHull ℝ ((leftLift '' X) ∪ (rightLift '' Y)) :=
    convexHull_mono Set.subset_union_left hleft
  have hr : rightLift b ∈ convexHull ℝ ((leftLift '' X) ∪ (rightLift '' Y)) :=
    convexHull_mono Set.subset_union_right hright
  have hh := (convex_convexHull ℝ ((leftLift '' X) ∪ (rightLift '' Y))) hl hr
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num : (1/2:ℝ)+1/2=1)
  convert hh using 1
  simp [Prod.smul_mk,smul_sub]
  module

noncomputable def separator (a b : E3) : LiftSpace →ₗ[ℝ] ℝ :=
  ((innerSL ℝ (b-a)).toLinearMap.comp (LinearMap.snd ℝ ℝ E3))-
    (inner ℝ (b-a) (a+b)) • (LinearMap.fst ℝ ℝ E3)

lemma separator_apply (a b : E3) (z : LiftSpace) :
    separator a b z = inner ℝ (b-a) z.2-inner ℝ (b-a) (a+b)*z.1 := rfl

lemma separator_nonzero {a b : E3} (hab : a ≠ b) : separator a b ≠ 0 := by
  intro h
  have hh := congrArg (fun f : LiftSpace →ₗ[ℝ] ℝ => f (0,b-a)) h
  change inner ℝ (b-a) (b-a)-inner ℝ (b-a) (a+b)*0 = 0 at hh
  rw [mul_zero,sub_zero,real_inner_self_eq_norm_sq] at hh
  have hn : ‖b-a‖ = 0 := by nlinarith [norm_nonneg (b-a)]
  exact hab (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

/-- A nonzero closest separation gives a nontrivial supporting hyperplane of
the augmented hull, so the sparse bound improves from five to four. -/
lemma closest_supporting_plane {X Y : Set E3} {a b : E3}
    (ha : a ∈ convexHull ℝ X) (hb : b ∈ convexHull ℝ Y)
    (hmin : ∀ x ∈ convexHull ℝ X, ∀ y ∈ convexHull ℝ Y, ‖b-a‖ ≤ ‖y-x‖) :
    separator a b ((1/2:ℝ),(1/2:ℝ) • (b-a)) = -inner ℝ (b-a) a ∧
    ∀ z ∈ (leftLift '' X) ∪ (rightLift '' Y), -inner ℝ (b-a) a ≤ separator a b z := by
  have hleft : ∀ x ∈ convexHull ℝ X, inner ℝ (b-a) (x-a) ≤ 0 :=
    closest_normal (convex_convexHull ℝ X) ha (fun x hx => hmin x hx b hb)
  have hright : ∀ y ∈ convexHull ℝ Y, inner ℝ (a-b) (y-b) ≤ 0 := by
    apply closest_normal (convex_convexHull ℝ Y) hb
    intro y hy
    rw [norm_sub_rev a b,norm_sub_rev a y]
    exact hmin a ha y hy
  constructor
  · rw [separator_apply]
    simp only [inner_smul_right,inner_sub_right,inner_add_right]
    ring
  · intro z hz
    rcases hz with ⟨x,hx,rfl⟩ | ⟨y,hy,rfl⟩
    · have hh := hleft x (subset_convexHull ℝ X hx)
      simp only [separator_apply,leftLift_apply,inner_neg_right,inner_sub_right,mul_zero,sub_zero]
      simp only [inner_sub_right] at hh
      linarith
    · have hh := hright y (subset_convexHull ℝ Y hy)
      have hneg : a-b = -(b-a) := by module
      rw [hneg,inner_neg_left,inner_sub_right] at hh
      simp only [separator_apply,rightLift_apply,inner_add_right,mul_one]
      linarith

/-- Split an augmented convex representation back into two ordinary convex
representations. Total support cannot increase. -/
theorem split_lift {ι : Type} [Fintype ι] {X Y : Set E3}
    {z : ι → LiftSpace} {w : ι → ℝ} {r : E3}
    (hz : Set.range z ⊆ (leftLift '' X) ∪ (rightLift '' Y))
    (hw : ∀ i, 0 < w i) (hs : ∑ i, w i = 1)
    (hr : ∑ i, w i • z i = ((1/2:ℝ),(1/2:ℝ) • r)) :
    ∃ (A B : Finset E3) (a b : E3), (A:Set E3) ⊆ X ∧ (B:Set E3) ⊆ Y ∧
      a ∈ convexHull ℝ (A:Set E3) ∧ b ∈ convexHull ℝ (B:Set E3) ∧
      b-a=r ∧ A.card+B.card ≤ Fintype.card ι := by
  classical
  let L := Finset.univ.filter (fun i => (z i).1=0)
  let R := Finset.univ.filter (fun i => (z i).1=1)
  have hk (i : ι) : (z i).1=0 ∨ (z i).1=1 := by
    rcases hz ⟨i,rfl⟩ with ⟨x,hx,he⟩ | ⟨y,hy,he⟩
    · left; rw [← he]; rfl
    · right; rw [← he]; simp
  have hdis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' : (z i).1=0 := (Finset.mem_filter.mp hi).2
    have hj' : (z i).1=1 := (Finset.mem_filter.mp hj).2
    linarith
  have huni : L ∪ R = Finset.univ := by
    ext i
    simp only [L,R,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
    exact hk i
  have hfirst : ∑ i, w i*(z i).1 = 1/2 := by
    have hh := congrArg (LinearMap.fst ℝ ℝ E3) hr
    simpa only [map_sum,map_smul,LinearMap.fst_apply,smul_eq_mul] using hh
  have hR : ∑ i ∈ R, w i = 1/2 := by
    rw [Finset.sum_filter]
    convert hfirst using 1
    apply Finset.sum_congr rfl
    intro i _
    rcases hk i with h | h <;> simp [h]
  have hL : ∑ i ∈ L, w i = 1/2 := by
    have hh := Finset.sum_union hdis (f := w)
    rw [huni,hs,hR] at hh
    linarith
  let A := L.image (fun i => -(z i).2)
  let B := R.image (fun i => (z i).2)
  let a := ∑ i ∈ L, (2*w i) • (-(z i).2)
  let b := ∑ i ∈ R, (2*w i) • (z i).2
  have hA : (A:Set E3) ⊆ X := by
    rintro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    rcases hz ⟨i,rfl⟩ with ⟨x,hx,he⟩ | ⟨y,hy,he⟩
    · simpa only [← he,leftLift_apply,neg_neg] using hx
    · have h0 := (Finset.mem_filter.mp hi).2
      rw [← he,rightLift_apply] at h0
      norm_num at h0
  have hB : (B:Set E3) ⊆ Y := by
    rintro y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    rcases hz ⟨i,rfl⟩ with ⟨x,hx,he⟩ | ⟨y,hy,he⟩
    · have h1 := (Finset.mem_filter.mp hi).2
      rw [← he,leftLift_apply] at h1
      norm_num at h1
    · simpa only [← he,rightLift_apply] using hy
  have ha : a ∈ convexHull ℝ (A:Set E3) := by
    apply (convex_convexHull ℝ (A:Set E3)).sum_mem
    · intro i _; exact mul_nonneg (by norm_num) (hw i).le
    · rw [← Finset.mul_sum,hL]; norm_num
    · intro i hi
      exact subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  have hb : b ∈ convexHull ℝ (B:Set E3) := by
    apply (convex_convexHull ℝ (B:Set E3)).sum_mem
    · intro i _; exact mul_nonneg (by norm_num) (hw i).le
    · rw [← Finset.mul_sum,hR]; norm_num
    · intro i hi
      exact subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  have hsecond : ∑ i, w i • (z i).2 = (1/2:ℝ) • r := by
    have hh := congrArg (LinearMap.snd ℝ ℝ E3) hr
    simpa only [map_sum,map_smul,LinearMap.snd_apply] using hh
  have hsum := Finset.sum_union hdis (f := fun i => w i • (z i).2)
  rw [huni,hsecond] at hsum
  have haeq : a = -((2:ℝ) • (∑ i ∈ L, w i • (z i).2)) := by
    dsimp [a]
    simp_rw [mul_smul,smul_neg]
    rw [Finset.sum_neg_distrib,← Finset.smul_sum]
  have hbeq : b = (2:ℝ) • (∑ i ∈ R, w i • (z i).2) := by
    dsimp [b]
    simp_rw [mul_smul]
    rw [← Finset.smul_sum]
  refine ⟨A,B,a,b,hA,hB,ha,hb,?_,?_⟩
  · rw [haeq,hbeq]
    have hh := congrArg (fun x : E3 => (2:ℝ) • x) hsum
    simp only [smul_smul] at hh
    norm_num at hh
    calc
      (2:ℝ) • (∑ i ∈ R, w i • (z i).2) - -((2:ℝ) • (∑ i ∈ L, w i • (z i).2)) =
        (2:ℝ) • (∑ i ∈ L, w i • (z i).2)+(2:ℝ) • (∑ i ∈ R, w i • (z i).2) := by module
      _ = r := hh.symm
  · have hc := Finset.card_union_of_disjoint hdis
    rw [huni,Finset.card_univ] at hc
    have hca := Finset.card_image_le (s := L) (f := fun i => -(z i).2)
    have hcb := Finset.card_image_le (s := R) (f := fun i => (z i).2)
    dsimp [A,B]
    omega

theorem separation_support_five {X Y : Set E3} {a b : E3}
    (ha : a ∈ convexHull ℝ X) (hb : b ∈ convexHull ℝ Y) :
    ∃ (A B : Finset E3) (a' b' : E3), (A:Set E3) ⊆ X ∧ (B:Set E3) ⊆ Y ∧
      a' ∈ convexHull ℝ (A:Set E3) ∧ b' ∈ convexHull ℝ (B:Set E3) ∧
      b'-a'=b-a ∧ A.card+B.card ≤ 5 := by
  obtain ⟨ι,hi,z,w,hz,hw,hs,hr,hcard⟩ := sparse_lift (separation_in_lifted_hull ha hb)
  letI := hi
  obtain ⟨A,B,a',b',hA,hB,ha',hb',hr',hc⟩ := split_lift hz hw hs hr
  exact ⟨A,B,a',b',hA,hB,ha',hb',hr',hc.trans hcard⟩

theorem closest_support_four {X Y : Set E3} {a b : E3}
    (ha : a ∈ convexHull ℝ X) (hb : b ∈ convexHull ℝ Y) (hab : a ≠ b)
    (hmin : ∀ x ∈ convexHull ℝ X, ∀ y ∈ convexHull ℝ Y, ‖b-a‖ ≤ ‖y-x‖) :
    ∃ (A B : Finset E3) (a' b' : E3), (A:Set E3) ⊆ X ∧ (B:Set E3) ⊆ Y ∧
      a' ∈ convexHull ℝ (A:Set E3) ∧ b' ∈ convexHull ℝ (B:Set E3) ∧
      b'-a'=b-a ∧ A.card+B.card ≤ 4 := by
  obtain ⟨hfx,hS⟩ := closest_supporting_plane ha hb hmin
  obtain ⟨ι,hi,z,w,hz,hw,hs,hr,hcard⟩ := sparse_lift_supporting
    (separation_in_lifted_hull ha hb) (separator_nonzero hab) hfx hS
  letI := hi
  obtain ⟨A,B,a',b',hA,hB,ha',hb',hr',hc⟩ := split_lift hz hw hs hr
  exact ⟨A,B,a',b',hA,hB,ha',hb',hr',hc.trans hcard⟩

lemma hull_support_nonempty {A : Finset E3} {a : E3}
    (ha : a ∈ convexHull ℝ (A:Set E3)) : A.Nonempty := by
  by_contra h
  have hA : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  simpa [hA] using ha

lemma support_card_three (I : FP.IEEE.Interchange) (x : IEEEAlgorithm.Simplex I)
    {A : Finset E3} (hA : (A:Set E3) ⊆ Set.range (fun j => decodeVec I (vertices I x j))) :
    A.card ≤ 3 := by
  classical
  have hh : A ⊆ Finset.univ.image (fun j => decodeVec I (vertices I x j)) := by
    intro a ha
    obtain ⟨j,rfl⟩ := hA ha
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩
  have hc := Finset.card_image_le (s := (Finset.univ : Finset (Fin 3)))
    (f := fun j => decodeVec I (vertices I x j))
  have hc' : (Finset.univ.image (fun j => decodeVec I (vertices I x j))).card ≤ 3 := by simpa using hc
  exact (Finset.card_le_card hh).trans hc'

/-- Exact nearest pairs with positive distance have support pattern 1/3, 3/1,
or 2/2. This is the global vertex/face-or-edge/edge theorem in support form. -/
theorem nearest_positive_support (I : FP.IEEE.Interchange) (x y : IEEEAlgorithm.Simplex I)
    (hd : 0 < distance I x y) :
    ∃ (A B : Finset E3) (a b : E3),
      (A:Set E3) ⊆ Set.range (fun j => decodeVec I (vertices I x j)) ∧
      (B:Set E3) ⊆ Set.range (fun j => decodeVec I (vertices I y j)) ∧
      a ∈ convexHull ℝ (A:Set E3) ∧ b ∈ convexHull ℝ (B:Set E3) ∧
      distance I x y = ‖b-a‖ ∧
      (A.card=1 ∨ B.card=1 ∨ (A.card≤2 ∧ B.card≤2)) := by
  obtain ⟨a,ha,b,hb,hdist⟩ := closest_pair I x y
  have hab : a ≠ b := by intro h; rw [h,sub_self,norm_zero] at hdist; linarith
  have hmin : ∀ a' ∈ carrier I x, ∀ b' ∈ carrier I y, ‖b-a‖ ≤ ‖b'-a'‖ := by
    intro a' ha' b' hb'
    rw [← hdist]
    exact distance_le I ha' hb'
  obtain ⟨A,B,a',b',hA,hB,ha',hb',hsep,hcard⟩ := closest_support_four ha hb hab hmin
  have hApos := Finset.card_pos.mpr (hull_support_nonempty ha')
  have hBpos := Finset.card_pos.mpr (hull_support_nonempty hb')
  refine ⟨A,B,a',b',hA,hB,ha',hb',by rw [hsep]; exact hdist,?_⟩
  omega

/-- For intersecting input simplexes there is an equal pair of points, with
at least one point using at most two input vertices. Thus triangle overlap is
always witnessed by edge/face containment (vertices included). -/
theorem intersection_support (I : FP.IEEE.Interchange) (x y : IEEEAlgorithm.Simplex I)
    (hd : distance I x y = 0) :
    ∃ (A B : Finset E3) (a : E3),
      (A:Set E3) ⊆ Set.range (fun j => decodeVec I (vertices I x j)) ∧
      (B:Set E3) ⊆ Set.range (fun j => decodeVec I (vertices I y j)) ∧
      a ∈ convexHull ℝ (A:Set E3) ∧ a ∈ convexHull ℝ (B:Set E3) ∧
      (A.card≤2 ∨ B.card≤2) := by
  obtain ⟨a,ha,b,hb,hdist⟩ := closest_pair I x y
  have hab : b-a = 0 := norm_eq_zero.mp (by linarith only [hdist,hd])
  obtain ⟨A,B,a',b',hA,hB,ha',hb',hsep,hcard⟩ := separation_support_five ha hb
  have heq : b'=a' := sub_eq_zero.mp (hsep.trans hab)
  subst b'
  exact ⟨A,B,a',hA,hB,ha',hb',by omega⟩

lemma support_singleton_vertex (I : FP.IEEE.Interchange) (x : IEEEAlgorithm.Simplex I)
    {A : Finset E3} {a : E3}
    (hA : (A:Set E3) ⊆ Set.range (fun j => decodeVec I (vertices I x j)))
    (ha : a ∈ convexHull ℝ (A:Set E3)) (hc : A.card=1) :
    ∃ j : Fin 3, a=decodeVec I (vertices I x j) := by
  obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp hc
  have hap : a=p := by simpa using ha
  obtain ⟨j,hj⟩ := hA (by simp : p ∈ ({p}:Finset E3))
  exact ⟨j,hap.trans hj.symm⟩

lemma two_indices_edge (i j : Fin 3) :
    ∃ e ∈ IEEEAlgorithm.edges, (i=e.1 ∨ i=e.2) ∧ (j=e.1 ∨ j=e.2) := by
  fin_cases i <;> fin_cases j <;> decide

lemma small_support_pair {A : Finset E3} (hne : A.Nonempty) (hc : A.card≤2) :
    ∃ p ∈ A, ∃ q ∈ A, (A:Set E3) ⊆ {p,q} := by
  classical
  by_cases h1 : A.card=1
  · obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp h1
    exact ⟨p,by simp,p,by simp,by simp⟩
  · have h2 : A.card=2 := by have := Finset.card_pos.mpr hne; omega
    obtain ⟨p,q,_,rfl⟩ := Finset.card_eq_two.mp h2
    exact ⟨p,by simp,q,by simp,by simp⟩

lemma small_support_triangle_edge (I : FP.IEEE.Interchange) (x : IEEEAlgorithm.Triangle I)
    {A : Finset E3} {a : E3}
    (hA : (A:Set E3) ⊆ Set.range (fun j => decodeVec I (x j)))
    (ha : a ∈ convexHull ℝ (A:Set E3)) (hc : A.card≤2) :
    ∃ e ∈ IEEEAlgorithm.edges, a ∈ carrier I (.segment (IEEEAlgorithm.edge I x e)) := by
  obtain ⟨p,hp,q,hq,hsub⟩ := small_support_pair (hull_support_nonempty ha) hc
  obtain ⟨i,rfl⟩ := hA hp
  obtain ⟨j,rfl⟩ := hA hq
  obtain ⟨e,he,hi,hj⟩ := two_indices_edge i j
  have vertex (k : Fin 3) (hk : k=e.1 ∨ k=e.2) :
      decodeVec I (x k) ∈ carrier I (.segment (IEEEAlgorithm.edge I x e)) := by
    rcases hk with rfl | rfl
    · exact vertex_mem I (.segment (IEEEAlgorithm.edge I x e)) 0
    · exact vertex_mem I (.segment (IEEEAlgorithm.edge I x e)) 1
  refine ⟨e,he,?_⟩
  apply convexHull_min (s := (A:Set E3)) ?_ (carrier_convex I _) ha
  intro p hp
  rcases hsub hp with hp | hp <;> subst p
  · exact vertex i hi
  · exact vertex j hj

/-- Global positive-distance coverage for two triangles. Each alternative is
an exact equality of independently defined geometric distances. -/
theorem triangle_triangle_positive_features (I : FP.IEEE.Interchange)
    (x y : IEEEAlgorithm.Triangle I) (hd : 0 < distance I (.triangle x) (.triangle y)) :
    (∃ i : Fin 3, distance I (.triangle x) (.triangle y)=distance I (.point (x i)) (.triangle y)) ∨
    (∃ j : Fin 3, distance I (.triangle x) (.triangle y)=distance I (.triangle x) (.point (y j))) ∨
    (∃ e ∈ IEEEAlgorithm.edges, ∃ f ∈ IEEEAlgorithm.edges,
      distance I (.triangle x) (.triangle y)=
        distance I (.segment (IEEEAlgorithm.edge I x e)) (.segment (IEEEAlgorithm.edge I y f))) := by
  obtain ⟨A,B,a,b,hA,hB,ha,hb,hsep,hcases⟩ := nearest_positive_support I (.triangle x) (.triangle y) hd
  have haX : a ∈ carrier I (.triangle x) := convexHull_mono hA ha
  have hbY : b ∈ carrier I (.triangle y) := convexHull_mono hB hb
  rcases hcases with h | h | ⟨h1,h2⟩
  · obtain ⟨i,hai⟩ := support_singleton_vertex I (.triangle x) hA ha h
    left; refine ⟨i,le_antisymm (distance_mono I (point_carrier_subset I (.triangle x) i) (Set.Subset.refl _)) ?_⟩
    rw [hsep,hai]
    exact distance_le I (vertex_mem I (.point (x i)) 0) hbY
  · obtain ⟨j,hbj⟩ := support_singleton_vertex I (.triangle y) hB hb h
    right; left; refine ⟨j,le_antisymm (distance_mono I (Set.Subset.refl _) (point_carrier_subset I (.triangle y) j)) ?_⟩
    rw [hsep,hbj]
    exact distance_le I haX (vertex_mem I (.point (y j)) 0)
  · obtain ⟨e,he,hae⟩ := small_support_triangle_edge I x hA ha h1
    obtain ⟨f,hf,hbf⟩ := small_support_triangle_edge I y hB hb h2
    right; right; refine ⟨e,he,f,hf,le_antisymm (distance_mono I (edge_carrier_subset I x e) (edge_carrier_subset I y f)) ?_⟩
    rw [hsep]
    exact distance_le I hae hbf

/-- Intersecting triangles have an edge of one intersecting the other's face,
including coplanar overlap and all degenerate inputs. -/
theorem triangle_triangle_intersection_features (I : FP.IEEE.Interchange)
    (x y : IEEEAlgorithm.Triangle I) (hd : distance I (.triangle x) (.triangle y)=0) :
    (∃ e ∈ IEEEAlgorithm.edges, distance I (.segment (IEEEAlgorithm.edge I x e)) (.triangle y)=0) ∨
    (∃ e ∈ IEEEAlgorithm.edges, distance I (.triangle x) (.segment (IEEEAlgorithm.edge I y e))=0) := by
  obtain ⟨A,B,a,hA,hB,ha,hb,hcases⟩ := intersection_support I (.triangle x) (.triangle y) hd
  rcases hcases with h | h
  · obtain ⟨e,he,hae⟩ := small_support_triangle_edge I x hA ha h
    exact Or.inl ⟨e,he,distance_zero_of_intersection I hae (convexHull_mono hB hb)⟩
  · obtain ⟨e,he,hbe⟩ := small_support_triangle_edge I y hB hb h
    exact Or.inr ⟨e,he,distance_zero_of_intersection I (convexHull_mono hA ha) hbe⟩

/-- For positive-distance segment/triangle pairs, one of the two endpoint
faces or three segment/edge pairs attains the exact distance. -/
theorem segment_triangle_positive_features (I : FP.IEEE.Interchange)
    (x : IEEEAlgorithm.Segment I) (y : IEEEAlgorithm.Triangle I)
    (hd : 0 < distance I (.segment x) (.triangle y)) :
    (∃ i : Fin 2, distance I (.segment x) (.triangle y)=distance I (.point (x i)) (.triangle y)) ∨
    (∃ e ∈ IEEEAlgorithm.edges, distance I (.segment x) (.triangle y)=
      distance I (.segment x) (.segment (IEEEAlgorithm.edge I y e))) := by
  obtain ⟨A,B,a,b,hA,hB,ha,hb,hsep,hcases⟩ := nearest_positive_support I (.segment x) (.triangle y) hd
  have hcases' : A.card=1 ∨ B.card≤2 := by omega
  have haX : a ∈ carrier I (.segment x) := convexHull_mono hA ha
  have hbY : b ∈ carrier I (.triangle y) := convexHull_mono hB hb
  rcases hcases' with h | h
  · obtain ⟨j,hai⟩ := support_singleton_vertex I (.segment x) hA ha h
    have hj : ∃ i : Fin 2, vertices I (.segment x) j=x i := by
      fin_cases j
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨0,rfl⟩
    obtain ⟨i,hi⟩ := hj
    have hsub : carrier I (.point (x i)) ⊆ carrier I (.segment x) := by
      rw [← hi]
      exact point_carrier_subset I (.segment x) j
    rw [hi] at hai
    left; refine ⟨i,le_antisymm (distance_mono I hsub (Set.Subset.refl _)) ?_⟩
    rw [hsep,hai]
    exact distance_le I (vertex_mem I (.point (x i)) 0) hbY
  · obtain ⟨e,he,hbe⟩ := small_support_triangle_edge I y hB hb h
    right; refine ⟨e,he,le_antisymm (distance_mono I (Set.Subset.refl _) (edge_carrier_subset I y e)) ?_⟩
    rw [hsep]
    exact distance_le I haX hbe

end DistanceAccuracy.GeometryFeatures

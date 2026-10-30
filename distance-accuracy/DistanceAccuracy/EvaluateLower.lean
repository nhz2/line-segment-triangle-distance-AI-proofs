import DistanceAccuracy.BCLower
import DistanceAccuracy.Selection
import DistanceAccuracy.GeometrySubsimplex
import DistanceAccuracy.FormatBudgets
import DistanceAccuracy.FormatRange

/-! End-to-end lower accuracy, including all candidate selections and folds. -/
set_option maxHeartbeats 2000000
namespace DistanceAccuracy.EvaluateLower
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds Geometry CandidateLower
variable (I : Interchange) [I.Valid]

structure Budget (L : ℝ) : Prop where
  nonneg : 0 ≤ L
  one : value? I (IEEEAlgorithm.one I) = some 1
  representable : I.format.Representable 1
  rho : I.format.unitRoundoff ≤ 1/1024
  eta1 : I.format.minSubnormal ≤ 1
  etaRho : I.format.minSubnormal ≤ I.format.unitRoundoff
  eta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L
  underflow : 2*Real.sqrt I.format.minSubnormal ≤ I.format.unitRoundoff*L
  linear : 32*L < I.format.overflowThreshold
  quadratic : 512*L*L+4 < I.format.overflowThreshold

structure Vertex (S : Set E3) (L : ℝ) (x : Vec3 I) where
  values : Fin 3 → ℚ
  decode : ∀ k, value? I (x k) = some (values k)
  bound : ∀ k, |(values k : ℝ)| ≤ L
  member : ratVec values ∈ S

structure Pair (S T : Set E3) (d : ℝ) : Prop where
  left : Convex ℝ S
  right : Convex ℝ T
  distance : ∀ a ∈ S, ∀ b ∈ T, d ≤ ‖b-a‖

variable {I}
lemma Pair.swap {S T : Set E3} {d : ℝ} (p : Pair S T d) : Pair T S d := by
  refine ⟨p.right, p.left, ?_⟩
  intro a ha b hb
  simpa [norm_sub_rev] using p.distance b hb a ha

variable {S T : Set E3} {d L : ℝ}
variable (budget : Budget I L) (pair : Pair S T d)
include budget pair

lemma point {x y : Vec3 I} (hx : Vertex I S L x) (hy : Vertex I T L y) :
    Safe I d (120*I.format.unitRoundoff*L) (pointPoint I x y).q :=
  pointPoint_safe I hx.decode hy.decode pair.left pair.right hx.member hy.member pair.distance
    budget.nonneg hx.bound hy.bound budget.rho budget.eta1 budget.eta budget.underflow budget.linear budget.quadratic

lemma segment {x : Vec3 I} {y : Segment I} (hx : Vertex I S L x)
    (hy : ∀ k, Vertex I T L (y k)) :
    Safe I d (120*I.format.unitRoundoff*L) (pointSegment I x y).q :=
  pointSegment_safe I hx.decode (hy 0).decode (hy 1).decode pair.left pair.right hx.member
    (hy 0).member (hy 1).member pair.distance budget.nonneg hx.bound (hy 0).bound (hy 1).bound
    budget.one budget.rho budget.eta1 budget.eta budget.underflow budget.linear budget.quadratic

lemma face {a b c x n : Vec3 I} (hx : Vertex I S L x)
    (ha : Vertex I T L a) (hb : Vertex I T L b) (hc : Vertex I T L c) :
    Safe I d (120*I.format.unitRoundoff*L)
      (IEEEAlgorithm.face I (vsub I a x) (vsub I b a) (vsub I c a) n).q :=
  face_safe I ha.decode hb.decode hc.decode hx.decode pair.left pair.right hx.member
    ha.member hb.member hc.member pair.distance budget.nonneg ha.bound hb.bound hc.bound hx.bound
    budget.one budget.representable budget.rho budget.eta1 budget.etaRho budget.eta
    budget.underflow budget.linear budget.quadratic

lemma pointTriangle {x : Vec3 I} {y : Triangle I} (hx : Vertex I S L x)
    (hy : ∀ k, Vertex I T L (y k)) :
    Safe I d (120*I.format.unitRoundoff*L) (IEEEAlgorithm.pointTriangle I x y).q :=
  BCLower.pointTriangle_safe I y (hy 0).decode (hy 1).decode (hy 2).decode hx.decode
    pair.left pair.right hx.member (hy 0).member (hy 1).member (hy 2).member pair.distance
    budget.nonneg (hy 0).bound (hy 1).bound (hy 2).bound hx.bound budget.one budget.representable
    budget.rho budget.eta1 budget.etaRho budget.eta budget.underflow budget.linear budget.quadratic

lemma segmentSegment {x y : Segment I} (hx : ∀ k, Vertex I S L (x k))
    (hy : ∀ k, Vertex I T L (y k)) :
    Safe I d (120*I.format.unitRoundoff*L) (IEEEAlgorithm.segmentSegment I x y).q :=
  segmentSegment_safe I (hx 0).decode (hx 1).decode (hy 0).decode (hy 1).decode
    pair.left pair.right (hx 0).member (hx 1).member (hy 0).member (hy 1).member pair.distance
    budget.nonneg (hx 0).bound (hx 1).bound (hy 0).bound (hy 1).bound
    budget.one budget.rho budget.eta1 budget.eta budget.underflow budget.linear budget.quadratic

lemma crossing {x : Segment I} {a b c n : Vec3 I} (hx : ∀ k, Vertex I S L (x k))
    (ha : Vertex I T L a) (hb : Vertex I T L b) (hc : Vertex I T L c) :
    Safe I d (120*I.format.unitRoundoff*L)
      (IEEEAlgorithm.crossing I x a (vsub I b a) (vsub I c a) n).q :=
  crossing_safe I ha.decode hb.decode hc.decode (hx 0).decode (hx 1).decode
    pair.left pair.right (hx 0).member (hx 1).member ha.member hb.member hc.member pair.distance
    budget.nonneg ha.bound hb.bound hc.bound (hx 0).bound (hx 1).bound
    budget.one budget.representable budget.rho budget.eta1 budget.etaRho budget.eta
    budget.underflow budget.linear budget.quadratic

omit budget pair in
def vertex_edge {U : Set E3} {x : Triangle I} (hx : ∀ k, Vertex I U L (x k))
    (e : Fin 3 × Fin 3) : ∀ k, Vertex I U L (edge I x e k) := by
  intro k
  refine Fin.cases (motive := fun k => Vertex I U L (edge I x e k)) (hx e.1) ?_ k
  intro j
  have hj : j = 0 := Fin.eq_zero j
  subst j
  exact hx e.2

lemma segmentTriangle {x : Segment I} {y : Triangle I}
    (hx : ∀ k, Vertex I S L (x k)) (hy : ∀ k, Vertex I T L (y k)) :
    Safe I d (120*I.format.unitRoundoff*L) (IEEEAlgorithm.segmentTriangle I x y).q := by
  apply Selection.segmentTriangle_property I
  · intro e; exact segmentSegment budget pair hx (vertex_edge hy e)
  · intro k; exact face budget pair (hx k) (hy 0) (hy 1) (hy 2)
  · exact crossing budget pair hx (hy 0) (hy 1) (hy 2)

lemma triangleTriangle {x y : Triangle I}
    (hx : ∀ k, Vertex I S L (x k)) (hy : ∀ k, Vertex I T L (y k)) :
    Safe I d (120*I.format.unitRoundoff*L) (IEEEAlgorithm.triangleTriangle I x y).q := by
  apply Selection.triangleTriangle_property I
  · exact point budget pair (hx 0) (hy 0)
  · intro e f; exact segmentSegment budget pair (vertex_edge hx e) (vertex_edge hy f)
  · intro k; exact face budget pair (hx k) (hy 0) (hy 1) (hy 2)
  · intro k; exact face budget pair.swap (hy k) (hx 0) (hx 1) (hx 2)
  · intro e; exact crossing budget pair (vertex_edge hx e) (hy 0) (hy 1) (hy 2)
  · intro e; exact crossing budget pair.swap (vertex_edge hy e) (hx 0) (hx 1) (hx 2)

/-- All nine simplex combinations, with no assumptions on computed candidates. -/
theorem evaluate {x y : Simplex I}
    (hx : ∀ j, Vertex I S L (vertices I x j))
    (hy : ∀ j, Vertex I T L (vertices I y j)) :
    Safe I d (120*I.format.unitRoundoff*L) (IEEEAlgorithm.evaluate I x y).q := by
  have seg {U : Set E3} {z : Segment I} (hz : ∀ j, Vertex I U L (vertices I (.segment z) j)) :
      ∀ k, Vertex I U L (z k) := by
    intro k
    refine Fin.cases (motive := fun k => Vertex I U L (z k)) (hz 0) ?_ k
    intro j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    exact hz 1
  cases x with
  | point x =>
    cases y with
    | point y => exact point budget pair (hx 0) (hy 0)
    | segment y => exact segment budget pair (hx 0) (seg hy)
    | triangle y => exact pointTriangle (x := x) (y := y) budget pair (hx 0) hy
  | segment x =>
    cases y with
    | point y => exact segment budget pair.swap (hy 0) (seg hx)
    | segment y => exact segmentSegment budget pair (seg hx) (seg hy)
    | triangle y => exact segmentTriangle (x := x) (y := y) budget pair (seg hx) hy
  | triangle x =>
    cases y with
    | point y => exact pointTriangle (x := y) (y := x) budget pair.swap (hy 0) hx
    | segment y => exact segmentTriangle (x := y) (y := x) budget pair.swap (seg hy) hx
    | triangle y =>
      simp only [IEEEAlgorithm.evaluate]
      exact triangleTriangle (x := x) (y := y) budget pair hx hy

omit budget pair in
noncomputable def vertex_of_bounded {x : Simplex I} (hx : boundedInput I x L) (j : Fin 3) :
    Vertex I (carrier I x) L (vertices I x j) := by
  classical
  choose v hv hb using hx j
  choose q hq he using fun k => rat_of_real I (hv k)
  refine ⟨q, hq, ?_, ?_⟩
  · intro k; rw [he k]; exact hb k
  · rw [ratVec_eq_decodeVec I hq]
    exact vertex_mem I x j

omit pair in
theorem evaluate_bounded {x y : Simplex I}
    (hx : boundedInput I x L) (hy : boundedInput I y L) :
    Safe I (distance I x y) (120*I.format.unitRoundoff*L) (IEEEAlgorithm.evaluate I x y).q := by
  let pair : Pair (carrier I x) (carrier I y) (distance I x y) :=
    ⟨carrier_convex I x, carrier_convex I y, fun _ ha _ hb => distance_le I ha hb⟩
  exact evaluate budget pair (vertex_of_bounded hx) (vertex_of_bounded hy)

omit budget pair in
set_option exponentiation.threshold 2048 in
lemma format_budget (f : Format) {L : ℝ} (hL : 0 ≤ L)
    (hupper : L < fourthRoot f.interchange.format.maxFinite/4)
    (hlower : fourthRoot f.leastNormal/64 ≤ L) : Budget f.interchange L := by
  have hρ : f.interchange.format.unitRoundoff = f.rho := by
    cases f
    · exact fp32_parameters.1
    · exact fp64_parameters.1
  have hη : f.interchange.format.minSubnormal = f.leastSubnormal := by
    cases f
    · exact fp32_parameters.2.2
    · exact fp64_parameters.2.2
  refine ⟨hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, f.linear_range hL hupper, ?_⟩
  · cases f
    · exact one_fp32
    · exact one_fp64
  · cases f <;> refine ⟨1, 0, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32, FP.IEEE.binary64, FP.IEEE.Format.precision]
  · rw [hρ]; have hh := f.rho_le; norm_num at hh ⊢; linarith
  · rw [hη]; cases f <;> norm_num [Format.leastSubnormal]
  · rw [hη, hρ]; cases f <;> norm_num [Format.leastSubnormal, Format.rho]
  · rw [hη, hρ]; exact f.large_subnormal_budget hlower
  · rw [hη, hρ]; exact f.large_sqrt_subnormal_budget hlower
  · have hh := f.quadratic_range hL hupper; linarith

omit budget pair in
/-- Unconditional lower accuracy of the complete IEEE implementation in the
    large-coordinate regime, for both supported formats. -/
theorem large_lower (f : Format) (x y : Simplex f.interchange) (L : ℝ)
    (hadm : admissible f.interchange x y L)
    (hlarge : fourthRoot f.leastNormal/64 ≤ L) :
    ∃ q : ℝ, f.interchange.decode? (IEEEAlgorithm.evaluate f.interchange x y).q = some q ∧
      0 ≤ q ∧ distance f.interchange x y-Real.sqrt q ≤ 120*f.interchange.format.unitRoundoff*L := by
  obtain ⟨hL, hupper, hx, hy⟩ := hadm
  obtain ⟨q, hq, hq0, hbound, _⟩ := evaluate_bounded (format_budget f hL hupper hlarge) hx hy
  exact ⟨(q : ℝ), real_decode f.interchange hq, by exact_mod_cast hq0, hbound⟩

omit budget pair in
lemma bounded_mono {x : Simplex I} {L K : ℝ} (hx : boundedInput I x L) (hLK : L ≤ K) :
    boundedInput I x K := by
  intro j k
  obtain ⟨v, hv, hb⟩ := hx j k
  exact ⟨v, hv, hb.trans hLK⟩

omit budget pair in
/-- Full lower side of claim 4, without a small-coordinate exception. -/
theorem lower (f : Format) (x y : Simplex f.interchange) (L : ℝ)
    (hadm : admissible f.interchange x y L) :
    ∃ q : ℝ, f.interchange.decode? (IEEEAlgorithm.evaluate f.interchange x y).q = some q ∧
      0 ≤ q ∧ distance f.interchange x y-Real.sqrt q ≤
        64*(2*f.interchange.format.unitRoundoff)*L+fourthRoot f.interchange.format.minNormal := by
  have hρ : f.interchange.format.unitRoundoff = f.rho := by
    cases f
    · exact fp32_parameters.1
    · exact fp64_parameters.1
  have hnormal : f.interchange.format.minNormal = f.leastNormal := by
    cases f
    · exact fp32_parameters.2.1
    · exact fp64_parameters.2.1
  obtain ⟨hL, hupper, hx, hy⟩ := hadm
  by_cases hlarge : fourthRoot f.leastNormal/64 ≤ L
  · obtain ⟨q, hq, hq0, hb⟩ := large_lower f x y L ⟨hL, hupper, hx, hy⟩ hlarge
    refine ⟨q, hq, hq0, ?_⟩
    have hm := mul_nonneg f.interchange.format.unitRoundoff_pos.le hL
    nlinarith [fourthRoot_nonneg f.interchange.format.minNormal]
  · have hsmall : L ≤ fourthRoot f.leastNormal/64 := (le_of_not_ge hlarge)
    have hscale : 0 ≤ fourthRoot f.leastNormal/64 := div_nonneg (fourthRoot_nonneg _) (by norm_num)
    obtain ⟨q, hq, hq0, hb⟩ := large_lower f x y (fourthRoot f.leastNormal/64)
      ⟨hscale, f.small_scale_admissible, bounded_mono hx hsmall, bounded_mono hy hsmall⟩ le_rfl
    refine ⟨q, hq, hq0, ?_⟩
    rw [hnormal]
    have hm := mul_nonneg f.interchange.format.unitRoundoff_pos.le hL
    have hρmax := f.rho_le
    have hH := fourthRoot_nonneg f.leastNormal
    have hh : 120*f.interchange.format.unitRoundoff*(fourthRoot f.leastNormal/64) ≤ fourthRoot f.leastNormal := by
      rw [hρ]
      have hcoef : 120*f.rho/64 ≤ 1 := by norm_num at hρmax; linarith
      have hh := mul_le_mul_of_nonneg_right hcoef hH
      nlinarith
    nlinarith

omit budget pair in
/-- Full two-sided accuracy in the small-coordinate regime. The magnitude
    reserve is obtained by evaluating the same words at the inflated scale H/64. -/
theorem small_accuracy (f : Format) (x y : Simplex f.interchange) (L : ℝ)
    (hadm : admissible f.interchange x y L)
    (hsmall : L ≤ fourthRoot f.leastNormal/64) :
    ∃ q : ℝ, f.interchange.decode? (IEEEAlgorithm.evaluate f.interchange x y).q = some q ∧
      0 ≤ q ∧ |Real.sqrt q-distance f.interchange x y| ≤ fourthRoot f.leastNormal := by
  obtain ⟨hL, _, hx, hy⟩ := hadm
  have hscale : 0 ≤ fourthRoot f.leastNormal/64 := div_nonneg (fourthRoot_nonneg _) (by norm_num)
  let bud := format_budget f hscale f.small_scale_admissible (le_refl _)
  obtain ⟨q, hq, hq0, hlo, hhi⟩ := evaluate_bounded bud (bounded_mono hx hsmall) (bounded_mono hy hsmall)
  refine ⟨(q : ℝ), real_decode f.interchange hq, by exact_mod_cast hq0, ?_⟩
  have hρ : f.interchange.format.unitRoundoff = f.rho := by
    cases f
    · exact fp32_parameters.1
    · exact fp64_parameters.1
  have hden : 120*f.interchange.format.unitRoundoff*(fourthRoot f.leastNormal/64)/
      (12*f.interchange.format.unitRoundoff) = 10*(fourthRoot f.leastNormal/64) := by
    field_simp [ne_of_gt f.interchange.format.unitRoundoff_pos]
    <;> ring
  rw [hden] at hhi
  have hρmax := f.rho_le
  have hH := fourthRoot_nonneg f.leastNormal
  have hlowBudget : 120*f.interchange.format.unitRoundoff*(fourthRoot f.leastNormal/64) ≤ fourthRoot f.leastNormal := by
    rw [hρ]
    have hcoef : 120*f.rho/64 ≤ 1 := by norm_num at hρmax; linarith
    have hh := mul_le_mul_of_nonneg_right hcoef hH
    nlinarith
  have hd := distance_nonneg f.interchange x y
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end DistanceAccuracy.EvaluateLower

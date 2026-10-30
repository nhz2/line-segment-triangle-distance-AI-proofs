import Mathlib
import DistanceAccuracy.IEEEAlgorithm
import DistanceAccuracy.Formats

/-!
# Exact geometric meaning and the final proof obligation

Simplexes are convex hulls of their input vertices, so repeated vertices and
collinear triangles are included. The Euclidean metric is used, not the sup
norm on functions. `accuracyStatement` is the intended theorem statement;
this file does not assert that it has been proved.
-/
namespace DistanceAccuracy.Geometry
open FP.IEEE FP.IEEE.Interchange
open IEEEAlgorithm

abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable (I : Interchange)

/-- Padding a point/segment with repeated vertices does not change its hull. -/
def vertices : Simplex I → Fin 3 → Vec3 I
  | .point x => fun _ => x
  | .segment x => ![x 0, x 1, x 0]
  | .triangle x => x

/-- Only finite inputs are used in the accuracy statement. The arbitrary value
for a non-finite coordinate makes this function total without assuming finiteness. -/
noncomputable def decodeVec (v : Vec3 I) : E3 :=
  WithLp.toLp 2 (fun k => (I.decode? (v k)).getD 0)

noncomputable def carrier (x : Simplex I) : Set E3 :=
  convexHull ℝ (Set.range (fun j => decodeVec I (vertices I x j)))

lemma vertex_mem (x : Simplex I) (j : Fin 3) : decodeVec I (vertices I x j) ∈ carrier I x :=
  subset_convexHull ℝ _ (Set.mem_range_self j)

lemma carrier_nonempty (x : Simplex I) : (carrier I x).Nonempty :=
  ⟨_, vertex_mem I x 0⟩

lemma carrier_compact (x : Simplex I) : IsCompact (carrier I x) :=
  (Set.finite_range _).isCompact_convexHull ℝ

lemma carrier_convex (x : Simplex I) : Convex ℝ (carrier I x) := convex_convexHull ℝ _

noncomputable def separations (x y : Simplex I) : Set E3 :=
  (fun p : E3 × E3 => p.2 - p.1) '' (carrier I x ×ˢ carrier I y)

lemma separations_nonempty (x y : Simplex I) : (separations I x y).Nonempty :=
  ((carrier_nonempty I x).prod (carrier_nonempty I y)).image _

lemma separations_compact (x y : Simplex I) : IsCompact (separations I x y) :=
  ((carrier_compact I x).prod (carrier_compact I y)).image
    (continuous_snd.sub continuous_fst)

noncomputable def distance (x y : Simplex I) : ℝ := Metric.infDist 0 (separations I x y)

lemma distance_nonneg (x y : Simplex I) : 0 ≤ distance I x y := Metric.infDist_nonneg

lemma distance_le {x y : Simplex I} {a b : E3}
    (ha : a ∈ carrier I x) (hb : b ∈ carrier I y) : distance I x y ≤ ‖b - a‖ := by
  have hm : b - a ∈ separations I x y := ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  simpa only [distance, dist_eq_norm, zero_sub, norm_neg] using
    (Metric.infDist_le_dist_of_mem (x := (0 : E3)) hm)

lemma closest_pair (x y : Simplex I) :
    ∃ a ∈ carrier I x, ∃ b ∈ carrier I y, distance I x y = ‖b - a‖ := by
  obtain ⟨r, hr, he⟩ := (separations_compact I x y).exists_infDist_eq_dist
    (separations_nonempty I x y) 0
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hr
  exact ⟨a, ha, b, hb, by simpa only [distance, dist_eq_norm, zero_sub, norm_neg] using he⟩

lemma distance_zero_of_intersection {x y : Simplex I} {p : E3}
    (hx : p ∈ carrier I x) (hy : p ∈ carrier I y) : distance I x y = 0 := by
  have h := distance_le I hx hy
  simp only [sub_self, norm_zero] at h
  exact le_antisymm h (distance_nonneg I x y)

/-- Finiteness is enforced through successful real decoding of every coordinate. -/
def boundedInput (x : Simplex I) (L : ℝ) : Prop :=
  ∀ j k, ∃ v : ℝ, I.decode? (vertices I x j k) = some v ∧ |v| ≤ L

/-- No bounds on returned quantities or certificates are assumed here. -/
def admissible (x y : Simplex I) (L : ℝ) : Prop :=
  0 ≤ L ∧ L < fourthRoot I.format.maxFinite / 4 ∧ boundedInput I x L ∧ boundedInput I y L

variable [I.Valid]

/-- The actual end-to-end target: evaluate IEEE words, decode the result, and
compare to the independently defined exact Euclidean distance. This is a
proposition definition, NOT an accuracy theorem. -/
def accuracyStatement : Prop :=
  ∀ (x y : Simplex I) (L : ℝ), admissible I x y L →
    ∃ q : ℝ, I.decode? (evaluate I x y).q = some q ∧
      |Real.sqrt q - distance I x y| ≤
        64 * (2 * I.format.unitRoundoff) * L + fourthRoot I.format.minNormal

end DistanceAccuracy.Geometry

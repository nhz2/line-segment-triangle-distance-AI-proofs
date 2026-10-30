import DistanceAccuracy.EvaluateLower
import DistanceAccuracy.UpperSelection

namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge

/-- Every face candidate is finite for admissible original vertices, including
    short or zero edges and arbitrary exceptional upstream normal words. -/
theorem face_finite_admissible (fmt : Format)
    {a b c x n : Vec3 fmt.interchange} {A B C X : Fin 3 → ℚ} {L : ℝ}
    (ha : ∀ k, value? fmt.interchange (a k) = some (A k))
    (hb : ∀ k, value? fmt.interchange (b k) = some (B k))
    (hc : ∀ k, value? fmt.interchange (c k) = some (C k))
    (hx : ∀ k, value? fmt.interchange (x k) = some (X k))
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hA : ∀ k, |(A k : ℝ)| ≤ L) (hB : ∀ k, |(B k : ℝ)| ≤ L)
    (hC : ∀ k, |(C k : ℝ)| ≤ L) (hX : ∀ k, |(X k : ℝ)| ≤ L) :
    UpperSelection.Finite fmt.interchange
      (face fmt.interchange (vsub fmt.interchange a x) (vsub fmt.interchange b a)
        (vsub fmt.interchange c a) n).q := by
  let K := max L (fourthRoot fmt.leastNormal/64)
  have hLK : L ≤ K := le_max_left _ _
  have hK : 0 ≤ K := hL.trans hLK
  have hKlim : K < fourthRoot fmt.interchange.format.maxFinite/4 := max_lt hadm fmt.small_scale_admissible
  let budget := EvaluateLower.format_budget fmt hK hKlim (le_max_right _ _)
  let pair : EvaluateLower.Pair (Set.univ : Set Geometry.E3) Set.univ 0 :=
    ⟨convex_univ, convex_univ, fun _ _ _ _ => norm_nonneg _⟩
  let va : EvaluateLower.Vertex fmt.interchange Set.univ K a := ⟨A, ha, fun k => (hA k).trans hLK, Set.mem_univ _⟩
  let vb : EvaluateLower.Vertex fmt.interchange Set.univ K b := ⟨B, hb, fun k => (hB k).trans hLK, Set.mem_univ _⟩
  let vc : EvaluateLower.Vertex fmt.interchange Set.univ K c := ⟨C, hc, fun k => (hC k).trans hLK, Set.mem_univ _⟩
  let vx : EvaluateLower.Vertex fmt.interchange Set.univ K x := ⟨X, hx, fun k => (hX k).trans hLK, Set.mem_univ _⟩
  obtain ⟨q, hq, _⟩ := EvaluateLower.face (n := n) budget pair vx va vb vc
  exact ⟨q, hq⟩

end DistanceAccuracy.ProjectionRounding

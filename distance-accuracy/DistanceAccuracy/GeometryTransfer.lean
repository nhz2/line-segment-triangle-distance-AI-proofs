import DistanceAccuracy.GeometryCoverage

/-! Scalar coordinate budgets for transferring witnesses between the independently
rounded affine geometries used by the face and edge kernels. -/
namespace DistanceAccuracy.GeometryCoverage

lemma coordinate_difference {a b L : ℝ} (ha : |a| ≤ L) (hb : |b| ≤ L) :
    |a - b| ≤ 2 * L := by
  calc
    |a - b| ≤ |a| + |b| := abs_sub a b
    _ ≤ 2 * L := by linarith

/-- A scalar three-cycle has length at most twice the coordinate range. -/
lemma coordinate_triangle {a b c L : ℝ}
    (ha : |a| ≤ L) (hb : |b| ≤ L) (hc : |c| ≤ L) :
    |a-b| + |b-c| + |c-a| ≤ 4*L := by
  obtain ⟨ha0, ha1⟩ := abs_le.mp ha
  obtain ⟨hb0, hb1⟩ := abs_le.mp hb
  obtain ⟨hc0, hc1⟩ := abs_le.mp hc
  rcases le_total a b with hab | hba <;>
    rcases le_total b c with hbc | hcb <;>
    rcases le_total c a with hca | hac <;>
    (repeat first | rw [abs_of_nonneg (by linarith)] | rw [abs_of_nonpos (by linarith)]) <;>
    linarith

lemma coordinate_four_cycle {a b c d L : ℝ}
    (ha : |a| ≤ L) (hb : |b| ≤ L) (hc : |c| ≤ L) (hd : |d| ≤ L) :
    |a-b| + |b-c| + |c-d| + |d-a| ≤ 8*L := by
  linarith [coordinate_difference ha hb, coordinate_difference hb hc,
    coordinate_difference hc hd, coordinate_difference hd ha]

lemma coordinate_five_cycle {a b c d e L : ℝ}
    (ha : |a| ≤ L) (hb : |b| ≤ L) (hc : |c| ≤ L)
    (hd : |d| ≤ L) (he : |e| ≤ L) :
    |a-b| + |b-c| + |c-d| + |d-e| + |e-a| ≤ 8*L := by
  have hcd : |c-d| ≤ |c-a| + |a-d| := by
    calc |c-d| = |(c-a)+(a-d)| := by congr 1; ring
         _ ≤ |c-a| + |a-d| := abs_add_le _ _
  linarith [coordinate_triangle ha hb hc, coordinate_triangle ha hd he]

/-- BC edge and unshifted face use different rounded differences. This is the
absolute-coordinate budget for the difference of those affine representations. -/
theorem bc_coordinate_budget {A B C P t L : ℝ}
    (ha : |A| ≤ L) (hb : |B| ≤ L) (hc : |C| ≤ L) (hp : |P| ≤ L)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |B-P| + t*|C-B| + |A-P| + (1-t)*|B-A| + t*|C-A| ≤ 8*L := by
  have h0 : |B-P| + |A-P| + |B-A| ≤ 8*L := by
    have := coordinate_triangle hb hp ha
    rw [abs_sub_comm P A, abs_sub_comm A B] at this
    have : 0 ≤ L := (abs_nonneg A).trans ha
    linarith
  have h1 : |B-P| + |C-B| + |A-P| + |C-A| ≤ 8*L := by
    have := coordinate_four_cycle hb hp ha hc
    rw [abs_sub_comm P A, abs_sub_comm A C, abs_sub_comm C B] at this
    rw [abs_sub_comm C B]
    linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h0),
    mul_nonneg ht (sub_nonneg.mpr h1)]

/-- The endpoint face solves use an additional rounded segment difference.
Its graph is a four-cycle at t=0 and a five-cycle at t=1. -/
theorem endpoint_coordinate_budget {A B C P Q t L : ℝ}
    (ha : |A| ≤ L) (hb : |B| ≤ L) (hc : |C| ≤ L)
    (hp : |P| ≤ L) (hq : |Q| ≤ L) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |B-P| + |Q-P| + |A-Q| + (1-t)*|B-A| + t*|C-A| + t*|C-B| ≤ 8*L := by
  have h0 : |B-P| + |Q-P| + |A-Q| + |B-A| ≤ 8*L := by
    have := coordinate_four_cycle hb hp hq ha
    rw [abs_sub_comm P Q, abs_sub_comm Q A, abs_sub_comm A B] at this
    exact this
  have h1 : |B-P| + |Q-P| + |A-Q| + |C-A| + |C-B| ≤ 8*L := by
    have := coordinate_five_cycle hb hp hq ha hc
    rw [abs_sub_comm P Q, abs_sub_comm Q A, abs_sub_comm A C] at this
    exact this
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h0),
    mul_nonneg ht (sub_nonneg.mpr h1)]

/-- Transfer from five local round-to-nearest error bounds to the common
unshifted BC geometry. Eta denotes the smallest subnormal spacing. -/
theorem bc_rounding_transfer {A B C P t L rho eta eBP eCB eAP eBA eCA : ℝ}
    (ha : |A| ≤ L) (hb : |B| ≤ L) (hc : |C| ≤ L) (hp : |P| ≤ L)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hr : 0 ≤ rho) (he : 0 ≤ eta)
    (hBP : |eBP| ≤ rho*|B-P|+eta/2)
    (hCB : |eCB| ≤ rho*|C-B|+eta/2)
    (hAP : |eAP| ≤ rho*|A-P|+eta/2)
    (hBA : |eBA| ≤ rho*|B-A|+eta/2)
    (hCA : |eCA| ≤ rho*|C-A|+eta/2) :
    |eBP + t*eCB - eAP - (1-t)*eBA - t*eCA| ≤ 8*rho*L+2*eta := by
  have hsum : |eBP + t*eCB - eAP - (1-t)*eBA - t*eCA| ≤
      |eBP|+t*|eCB|+|eAP|+(1-t)*|eBA|+t*|eCA| := by
    have h1 := abs_add_le eBP (t*eCB)
    have h2 := abs_sub (eBP+t*eCB) eAP
    have h3 := abs_sub (eBP+t*eCB-eAP) ((1-t)*eBA)
    have h4 := abs_sub (eBP+t*eCB-eAP-(1-t)*eBA) (t*eCA)
    simp only [abs_mul, abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr ht1)] at *
    linarith
  have hbudget := bc_coordinate_budget ha hb hc hp ht ht1
  have hCB' := mul_le_mul_of_nonneg_left hCB ht
  have hBA' := mul_le_mul_of_nonneg_left hBA (sub_nonneg.mpr ht1)
  have hCA' := mul_le_mul_of_nonneg_left hCA ht
  have hb' := mul_le_mul_of_nonneg_left hbudget hr
  nlinarith [mul_nonneg he (sub_nonneg.mpr ht1)]

/-- Original-to-common-proxy displacement, in any normed vector space.
The triangle interpolation costs one edge error; the moving segment costs two. -/
theorem original_proxy_transfer {eAB eAC eAP ePQ : E3} {u v z delta : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v ≤ 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hd : 0 ≤ delta)
    (hAB : ‖eAB‖ ≤ delta) (hAC : ‖eAC‖ ≤ delta)
    (hAP : ‖eAP‖ ≤ delta) (hPQ : ‖ePQ‖ ≤ delta) :
    ‖u • eAB + v • eAC + eAP - z • ePQ‖ ≤ 3*delta := by
  have h1 := norm_add_le (u • eAB) (v • eAC)
  have h2 := norm_add_le (u • eAB+v • eAC) eAP
  have h3 := norm_sub_le (u • eAB+v • eAC+eAP) (z • ePQ)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu,
    abs_of_nonneg hv, abs_of_nonneg hz] at *
  nlinarith [mul_le_mul_of_nonneg_left hAB hu,
    mul_le_mul_of_nonneg_left hAC hv, mul_le_mul_of_nonneg_left hPQ hz,
    mul_nonneg hd (sub_nonneg.mpr huv), mul_nonneg hd (sub_nonneg.mpr hz1)]

/-- Expanding the actual affine formulas leaves precisely the five local
rounding errors controlled above; the exact coordinate terms cancel. -/
lemma bc_affine_error_identity (A B C P t eBP eCB eAP eBA eCA : ℝ) :
    ((B-P+eBP)+t*(C-B+eCB)) -
      ((A-P+eAP)+(1-t)*(B-A+eBA)+t*(C-A+eCA)) =
      eBP+t*eCB-eAP-(1-t)*eBA-t*eCA := by ring

/-- The shifted common geometry incurs exactly one additional FMA residual
error. The unshifted thin fallback avoids this extra term. -/
theorem shifted_proxy_transfer {eAB eAC eAP ePQ shift : E3} {u v z delta sigma : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v ≤ 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hd : 0 ≤ delta)
    (hAB : ‖eAB‖ ≤ delta) (hAC : ‖eAC‖ ≤ delta)
    (hAP : ‖eAP‖ ≤ delta) (hPQ : ‖ePQ‖ ≤ delta) (hs : ‖shift‖ ≤ sigma) :
    ‖u • eAB + v • eAC + eAP - z • ePQ + shift‖ ≤ 3*delta+sigma := by
  exact (norm_add_le _ _).trans (add_le_add
    (original_proxy_transfer hu hv huv hz hz1 hd hAB hAC hAP hPQ) hs)

/-- Reusable witness transfer in the exact common geometry: adding a bounded
residual displacement increases the witness distance by at most that bound. -/
lemma transfer_witness_norm {r delta : E3} {B e : ℝ}
    (hr : ‖r‖ ≤ B) (he : ‖delta‖ ≤ e) : ‖r+delta‖ ≤ B+e :=
  (norm_add_le _ _).trans (add_le_add hr he)

lemma coordinate_norm_bound {v : E3} {b : ℝ} (hb : 0 ≤ b)
    (hv : ∀ i, |v i| ≤ b) : ‖v‖ ≤ Real.sqrt 3*b := by
  have hi (i : Fin 3) : (v i)^2 ≤ b^2 := by
    have := hv i
    nlinarith [sq_abs (v i), mul_nonneg (sub_nonneg.mpr this) (show 0 ≤ b+|v i| by positivity)]
  have hn : ‖v‖^2 ≤ 3*b^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i : Fin 3, (v i)^2 ≤ ∑ _i : Fin 3, b^2 := Finset.sum_le_sum (fun i _ => hi i)
      _ = 3*b^2 := by simp
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  nlinarith [norm_nonneg v, Real.sqrt_nonneg (3:ℝ),
    mul_nonneg (Real.sqrt_nonneg (3:ℝ)) hb]

/-- Vector lifting of the BC discrepancy gives 4 rho D plus an explicit
subnormal remainder, where D=2 sqrt(3) L. -/
theorem bc_vector_transfer {A B C P eBP eCB eAP eBA eCA : E3}
    {t L rho eta : ℝ}
    (ha : ∀ i, |A i| ≤ L) (hb : ∀ i, |B i| ≤ L)
    (hc : ∀ i, |C i| ≤ L) (hp : ∀ i, |P i| ≤ L)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hr : 0 ≤ rho) (he : 0 ≤ eta)
    (hBP : ∀ i, |eBP i| ≤ rho*|B i-P i|+eta/2)
    (hCB : ∀ i, |eCB i| ≤ rho*|C i-B i|+eta/2)
    (hAP : ∀ i, |eAP i| ≤ rho*|A i-P i|+eta/2)
    (hBA : ∀ i, |eBA i| ≤ rho*|B i-A i|+eta/2)
    (hCA : ∀ i, |eCA i| ≤ rho*|C i-A i|+eta/2) :
    ‖eBP+t • eCB-eAP-(1-t) • eBA-t • eCA‖ ≤
      4*rho*(2*Real.sqrt 3*L)+2*Real.sqrt 3*eta := by
  have hL : 0 ≤ L := (abs_nonneg (A 0)).trans (ha 0)
  have h := coordinate_norm_bound (show 0 ≤ 8*rho*L+2*eta by positivity)
    (v := eBP+t • eCB-eAP-(1-t) • eBA-t • eCA) (fun i => by
      simpa using bc_rounding_transfer (ha i) (hb i) (hc i) (hp i)
        ht ht1 hr he (hBP i) (hCB i) (hAP i) (hBA i) (hCA i))
  nlinarith only [h]

/-- One independently rounded coordinate difference has norm error rho D
plus its explicit subnormal remainder. -/
theorem difference_error_norm {A B e : E3} {L rho eta : ℝ}
    (ha : ∀ i, |A i| ≤ L) (hb : ∀ i, |B i| ≤ L)
    (hr : 0 ≤ rho) (he : 0 ≤ eta)
    (herr : ∀ i, |e i| ≤ rho*|A i-B i|+eta/2) :
    ‖e‖ ≤ rho*(2*Real.sqrt 3*L)+Real.sqrt 3*eta/2 := by
  have hL : 0 ≤ L := (abs_nonneg (A 0)).trans (ha 0)
  have h := coordinate_norm_bound (show 0 ≤ 2*rho*L+eta/2 by positivity)
    (v := e) (fun i => (herr i).trans (by
      have := mul_le_mul_of_nonneg_left (coordinate_difference (ha i) (hb i)) hr
      linarith))
  nlinarith only [h]

end DistanceAccuracy.GeometryCoverage

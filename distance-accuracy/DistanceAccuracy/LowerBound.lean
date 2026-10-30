import DistanceAccuracy.Geometry
import DistanceAccuracy.Reconstruction

/-!
# A loose lower bound sufficient for claim 4

This does not use claim 5's tight crossing analysis. Error propagation and
barycentric repair are separated, with 120ρL available for the lower side.
-/
namespace DistanceAccuracy.LowerBound
open DistanceAccuracy.Geometry

lemma norm_le_three {x : E3} {K : ℝ} (hK : 0 ≤ K) (hx : ∀ i, |x i| ≤ K) : ‖x‖ ≤ 3*K := by
  have hs := EuclideanSpace.real_norm_sq_eq x
  simp [Fin.sum_univ_succ] at hs
  have h0 := sq_le_sq₀ (abs_nonneg (x 0)) hK |>.2 (hx 0)
  have h1 := sq_le_sq₀ (abs_nonneg (x 1)) hK |>.2 (hx 1)
  have h2 := sq_le_sq₀ (abs_nonneg (x 2)) hK |>.2 (hx 2)
  rw [sq_abs] at h0 h1 h2
  nlinarith [norm_nonneg x, sq_nonneg K]

noncomputable def bary (A B C : E3) (u v : ℝ) : E3 := A + u • (B-A) + v • (C-A)

lemma bary_mem {S : Set E3} (hS : Convex ℝ S) {A B C : E3}
    (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v ≤ 1) : bary A B C u v ∈ S := by
  have h := hS.sum_mem (t := Finset.univ) (w := ![1-u-v,u,v]) (z := ![A,B,C])
    (by intro i hi; fin_cases i <;> simp <;> linarith)
    (by simp [Fin.sum_univ_succ])
    (by intro i hi; fin_cases i <;> simp [hA,hB,hC])
  convert h using 1
  simp [bary, Fin.sum_univ_succ]
  module

lemma repaired_weights {u v tau : ℝ} (htau : 0 ≤ tau) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v)
    (hsum : u+v ≤ 1+tau) :
    0 ≤ min v (1-u) ∧ u + min v (1-u) ≤ 1 ∧
      0 ≤ v-min v (1-u) ∧ v-min v (1-u) ≤ tau := by
  have hmin := min_le_right v (1-u)
  have hminv := min_le_left v (1-u)
  refine ⟨le_min hv0 (by linarith), by linarith, by linarith, ?_⟩
  by_cases hv : v ≤ 1-u
  · rw [min_eq_left hv]; linarith
  · rw [min_eq_right (le_of_not_ge hv)]; linarith

lemma bary_repair_error {A B C : E3} {u v tau D : ℝ}
    (htau : 0 ≤ tau) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hsum : u+v ≤ 1+tau)
    (hD : ‖C-A‖ ≤ D) :
    ‖bary A B C u v - bary A B C u (min v (1-u))‖ ≤ tau*D := by
  obtain ⟨_, _, hd0, hd⟩ := repaired_weights htau hu0 hu1 hv0 hsum
  have he : bary A B C u v - bary A B C u (min v (1-u)) =
      (v-min v (1-u)) • (C-A) := by unfold bary; module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd0]
  exact mul_le_mul hd hD (norm_nonneg _) (by linarith)

lemma bary_coordinate_bound {A B C : E3} {u v tau L : ℝ}
    (htau : 0 ≤ tau) (hL : 0 ≤ L) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v)
    (hsum : u+v ≤ 1+tau)
    (hA : ∀ k, |A k| ≤ L) (hB : ∀ k, |B k| ≤ L) (hC : ∀ k, |C k| ≤ L) :
    ∀ k, |bary A B C u v k| ≤ (1+2*tau)*L := by
  intro k
  obtain ⟨hm0, hsum', hd0, hd⟩ := repaired_weights htau hu0 hu1 hv0 hsum
  have hrepair : |bary A B C u (min v (1-u)) k| ≤ L := by
    have ha := hA k; have hb := hB k; have hc := hC k
    have h := abs_add_le ((1-u-min v (1-u))*A k + u*B k) (min v (1-u)*C k)
    have h' := abs_add_le ((1-u-min v (1-u))*A k) (u*B k)
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-u-min v (1-u)),
      abs_of_nonneg hu0] at h'
    rw [abs_mul, abs_of_nonneg hm0] at h
    have ha' := mul_le_mul_of_nonneg_left ha (show 0 ≤ 1-u-min v (1-u) by linarith)
    have hb' := mul_le_mul_of_nonneg_left hb hu0
    have hc' := mul_le_mul_of_nonneg_left hc hm0
    have he : bary A B C u (min v (1-u)) k =
        (1-u-min v (1-u))*A k + u*B k + min v (1-u)*C k := by
      simp [bary]; ring
    rw [he]; nlinarith
  have herr : |bary A B C u v k - bary A B C u (min v (1-u)) k| ≤ 2*tau*L := by
    have he : bary A B C u v k - bary A B C u (min v (1-u)) k =
        (v-min v (1-u))*(C k-A k) := by simp [bary]; ring
    rw [he, abs_mul, abs_of_nonneg hd0]
    have hc := Reconstruction.difference_abs (hC k) (hA k)
    have h := mul_le_mul hd hc (abs_nonneg _) (by linarith)
    nlinarith
  have h := Reconstruction.abs_triangle_sub (bary A B C u v k)
    (bary A B C u (min v (1-u)) k) 0
  simp only [sub_zero] at h
  linarith

lemma sqrt_lower {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q)
    (hs : a^2-b^2 ≤ q) : a-b ≤ Real.sqrt q := by
  have hroot := Real.sqrt_nonneg q
  have hsq := Real.sq_sqrt hq
  by_cases hab : a ≤ b
  · linarith
  · have hprod := mul_nonneg hb (show 0 ≤ a-b by linarith)
    nlinarith

lemma sqrt_upper {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : q ≤ a^2+b^2) :
    Real.sqrt q ≤ a+b := by
  apply Real.sqrt_le_iff.mpr
  exact ⟨by linarith, by nlinarith [mul_nonneg ha hb]⟩

/-- Square-root evaluation error, including gradual underflow. -/
theorem norm_evaluation {rho eta r q : ℝ}
    (hrho : 0 ≤ rho) (hrhomax : rho ≤ 1/1024)
    (heta : 0 ≤ eta) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (herror : |q-r^2| ≤ 3*rho*(1+rho)^2*r^2+2*eta) :
    |Real.sqrt q-r| ≤ 2*rho*r+2*Real.sqrt eta := by
  have hetaSq := Real.sq_sqrt heta
  have hetaRoot := Real.sqrt_nonneg eta
  have hcoef : 3*rho*(1+rho)^2 ≤ 4*rho-4*rho^2 := by
    have h1 := mul_self_le_mul_self hrho hrhomax
    have h2 := mul_nonneg hrho (show 0 ≤ 1-10*rho-3*rho^2 by nlinarith)
    nlinarith
  have hcoefR := mul_le_mul_of_nonneg_right hcoef (sq_nonneg r)
  obtain ⟨hqlo, hqhi⟩ := abs_le.mp herror
  have ha : 0 ≤ (1-2*rho)*r := mul_nonneg (by linarith) hr
  have hb : 0 ≤ 2*Real.sqrt eta := by positivity
  have hlo : (1-2*rho)*r - 2*Real.sqrt eta ≤ Real.sqrt q := by
    apply sqrt_lower ha hb hq
    nlinarith
  have hhi : Real.sqrt q ≤ (1+2*rho)*r + 2*Real.sqrt eta := by
    apply sqrt_upper (mul_nonneg (by linarith) hr) hb
    nlinarith [sq_nonneg (rho*r)]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Lower assembly from coordinate reconstruction errors, loose feasible weights,
    and the three-operation squared-norm error. No minimizer accuracy is assumed. -/
theorem lower_120 {rho eta L d q : ℝ} {A B C D E F r : E3} {u v s t : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/1024) (he : 0 ≤ eta) (hL : 0 ≤ L)
    (hunder : 2*Real.sqrt eta ≤ rho*L)
    (hA : ∀ k, |A k| ≤ L) (hB : ∀ k, |B k| ≤ L) (hC : ∀ k, |C k| ≤ L)
    (hD : ∀ k, |D k| ≤ L) (hE : ∀ k, |E k| ≤ L) (hF : ∀ k, |F k| ≤ L)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (huv : u+v ≤ 1+(3/2)*rho)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (hst : s+t ≤ 1+(3/2)*rho)
    (hrec : ∀ k, |(r-(bary D E F s t-bary A B C u v)) k| ≤ 29*rho*L)
    (hd : d ≤ ‖bary D E F s (min t (1-s))-bary A B C u (min v (1-u))‖)
    (hq : 0 ≤ q)
    (hqerr : |q-‖r‖^2| ≤ 3*rho*(1+rho)^2*‖r‖^2+2*eta) :
    d-Real.sqrt q ≤ 120*rho*L := by
  let X := bary A B C u v
  let Y := bary D E F s t
  let X' := bary A B C u (min v (1-u))
  let Y' := bary D E F s (min t (1-s))
  have hrec' : ‖r-(Y-X)‖ ≤ 87*rho*L := by
    have h := norm_le_three (by positivity : 0 ≤ 29*rho*L) hrec
    dsimp [X,Y]; nlinarith
  have hCA : ‖C-A‖ ≤ 6*L := by
    have h := norm_le_three (x := C-A) (by positivity : 0 ≤ 2*L)
      (fun k => Reconstruction.difference_abs (hC k) (hA k))
    nlinarith
  have hFD : ‖F-D‖ ≤ 6*L := by
    have h := norm_le_three (x := F-D) (by positivity : 0 ≤ 2*L)
      (fun k => Reconstruction.difference_abs (hF k) (hD k))
    nlinarith
  have hXX : ‖X-X'‖ ≤ 9*rho*L := by
    have h := bary_repair_error (B := B) (by positivity) hu0 hu1 hv0 huv hCA
    dsimp [X,X']; nlinarith
  have hYY : ‖Y-Y'‖ ≤ 9*rho*L := by
    have h := bary_repair_error (B := E) (by positivity) hs0 hs1 ht0 hst hFD
    dsimp [Y,Y']; nlinarith
  have hYX : ‖Y-X‖ ≤ 6*(1+3*rho)*L := by
    have hx := bary_coordinate_bound (by positivity) hL hu0 hu1 hv0 huv hA hB hC
    have hy := bary_coordinate_bound (by positivity) hL hs0 hs1 ht0 hst hD hE hF
    have h := norm_le_three (x := Y-X) (by positivity : 0 ≤ 2*((1+2*((3/2)*rho))*L))
      (fun k => Reconstruction.difference_abs (hy k) (hx k))
    dsimp [Y,X]; nlinarith
  have hrnorm : ‖r‖ ≤ 7*L := by
    have h := norm_add_le (r-(Y-X)) (Y-X)
    rw [sub_add_cancel] at h
    have hs := mul_nonneg hL (show 0 ≤ 1-105*rho by linarith)
    nlinarith
  have hpair : ‖Y'-X'‖ ≤ ‖r‖+105*rho*L := by
    have h1 := norm_sub_le (Y'-Y) (X'-X)
    rw [norm_sub_rev Y' Y, norm_sub_rev X' X] at h1
    have h2 := norm_add_le ((Y'-Y)-(X'-X)) (Y-X)
    have heq : ((Y'-Y)-(X'-X))+(Y-X) = Y'-X' := by module
    rw [heq] at h2
    have h3 := norm_sub_le r (r-(Y-X))
    rw [sub_sub_cancel] at h3
    linarith
  have heval := norm_evaluation hr hrmax he (norm_nonneg r) hq hqerr
  have hlower := (abs_le.mp heval).1
  have hprod := mul_le_mul_of_nonneg_left hrnorm (show 0 ≤ 2*rho by positivity)
  change d ≤ ‖Y'-X'‖ at hd
  nlinarith

end DistanceAccuracy.LowerBound

import Mathlib

/-!
# A deliberately loose reconstruction bound for claim 4

Unlike the sharper claim-5 argument, this module uses only clamped parameter
bounds and local IEEE rounding inequalities. The crossing computation needs
23ρL per coordinate. This leaves ample room in claim 4's 128ρL budget and
avoids the special approximate-stationarity lemma used to prove claim 5.
-/
namespace DistanceAccuracy.Reconstruction

def RoundError (rho eta exact rounded : ℝ) : Prop :=
  |rounded - exact| ≤ rho * |exact| + eta / 2

lemma abs_triangle_sub (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
  convert abs_add_le (a-b) (b-c) using 1 <;> congr 1 <;> ring

lemma interval_abs {L a b t : ℝ} (hL : 0 ≤ L) (ha : |a| ≤ L) (hb : |b| ≤ L)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |(1-t)*a+t*b| ≤ L := by
  have h := abs_add_le ((1-t)*a) (t*b)
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-t), abs_of_nonneg ht0] at h
  have h₁ := mul_le_mul_of_nonneg_left ha (show 0 ≤ 1-t by linarith)
  have h₂ := mul_le_mul_of_nonneg_left hb ht0
  nlinarith

lemma difference_abs {L a b : ℝ} (ha : |a| ≤ L) (hb : |b| ≤ L) : |a-b| ≤ 2*L := by
  have h := abs_triangle_sub a 0 b
  simp only [sub_zero, zero_sub, abs_neg] at h
  linarith

lemma affine_input_error {rho L C D a b a₀ b₀ t : ℝ}
    (hr : 0 ≤ rho) (hL : 0 ≤ L) (ht : |t| ≤ 1)
    (ha : |a-a₀| ≤ C*rho*L) (hb : |b-b₀| ≤ D*rho*L) :
    |(a+t*b)-(a₀+t*b₀)| ≤ (C+D)*rho*L := by
  have hb0 : 0 ≤ D*rho*L := (abs_nonneg _).trans hb
  calc
    |(a+t*b)-(a₀+t*b₀)| = |(a-a₀)+t*(b-b₀)| := by congr 1; ring
    _ ≤ |a-a₀|+|t*(b-b₀)| := abs_add_le _ _
    _ = |a-a₀|+|t| *|b-b₀| := by rw [abs_mul]
    _ ≤ C*rho*L + 1*(D*rho*L) :=
      add_le_add ha (mul_le_mul ht hb (abs_nonneg _) (by norm_num))
    _ = (C+D)*rho*L := by ring

/-- Propagate a local rounding error through a perturbed argument.
`C` is the accumulated input error and `K` the exact argument magnitude. -/
lemma round_propagate {rho eta L C K a a₀ out : ℝ}
    (hr : 0 ≤ rho) (hL : 0 ≤ L) (heta : eta ≤ rho^2*L)
    (hsmall : (C+1/2)*rho ≤ 1)
    (ha : |a-a₀| ≤ C*rho*L) (ha₀ : |a₀| ≤ K*L)
    (hround : RoundError rho eta a out) :
    |out-a₀| ≤ (C+K+1)*rho*L := by
  have harg : |a| ≤ K*L+C*rho*L := by
    have h := abs_triangle_sub a a₀ 0
    simp only [sub_zero] at h
    linarith
  have harg' := mul_le_mul_of_nonneg_left harg hr
  have hbudget := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hr hL)
  have htotal := abs_triangle_sub out a a₀
  unfold RoundError at hround
  nlinarith

lemma round_difference {rho eta L a b out : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/1024) (hL : 0 ≤ L) (heta : eta ≤ rho^2*L)
    (ha : |a| ≤ L) (hb : |b| ≤ L) (hround : RoundError rho eta (a-b) out) :
    |out-(a-b)| ≤ 3*rho*L := by
  have h := round_propagate (C := 0) (K := 2) hr hL heta (by linarith)
    (show |(a-b)-(a-b)| ≤ 0*rho*L by simp) (difference_abs ha hb) hround
  norm_num at h ⊢
  exact h

/-- Worst affine schedule: AP - sP, then +uE0, then +vE1.
No optimality/accuracy assumption on s,u,v is used. -/
theorem crossing_scalar_error {rho eta L a b c p₀ p₁ s u v E F P AP AX W R : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/1024) (hL : 0 ≤ L) (heta : eta ≤ rho^2*L)
    (ha : |a| ≤ L) (hb : |b| ≤ L) (hc : |c| ≤ L)
    (hp₀ : |p₀| ≤ L) (hp₁ : |p₁| ≤ L)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hE : RoundError rho eta (b-a) E) (hF : RoundError rho eta (c-a) F)
    (hP : RoundError rho eta (p₁-p₀) P) (hAP : RoundError rho eta (a-p₀) AP)
    (hAX : RoundError rho eta (AP-s*P) AX)
    (hW : RoundError rho eta (AX+u*E) W)
    (hR : RoundError rho eta (W+v*F) R) :
    |R - (a+u*(b-a)+v*(c-a)-((1-s)*p₀+s*p₁))| ≤ 23*rho*L := by
  have he := round_difference hr hrmax hL heta hb ha hE
  have hf := round_difference hr hrmax hL heta hc ha hF
  have hp := round_difference hr hrmax hL heta hp₁ hp₀ hP
  have hap := round_difference hr hrmax hL heta ha hp₀ hAP
  have hs : |(-s)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hs0]; exact hs1
  have hu : |u| ≤ 1 := by rwa [abs_of_nonneg hu0]
  have hv : |v| ≤ 1 := by rwa [abs_of_nonneg hv0]
  let X := (1-s)*p₀+s*p₁
  have hX : |X| ≤ L := interval_abs hL hp₀ hp₁ hs0 hs1
  have haxin : |(AP-s*P)-(a-X)| ≤ 6*rho*L := by
    have h := affine_input_error hr hL hs hap hp
    dsimp [X]
    convert h using 1 <;> congr 1 <;> ring
  have hax : |AX-(a-X)| ≤ 9*rho*L := by
    have h := round_propagate (C := 6) (K := 2) hr hL heta (by linarith) haxin
      (difference_abs ha hX) hAX
    norm_num at h ⊢; exact h
  have hAB : |a+u*(b-a)| ≤ L := by
    have h := interval_abs hL ha hb hu0 hu1
    convert h using 1 <;> congr 1 <;> ring
  have hwin : |(AX+u*E)-(a+u*(b-a)-X)| ≤ 12*rho*L := by
    have h := affine_input_error hr hL hu hax he
    convert h using 1 <;> congr 1 <;> ring
  have hw : |W-(a+u*(b-a)-X)| ≤ 15*rho*L := by
    have h := round_propagate (C := 12) (K := 2) hr hL heta (by linarith) hwin
      (difference_abs hAB hX) hW
    norm_num at h ⊢; exact h
  have hrin : |(W+v*F)-(a+u*(b-a)+v*(c-a)-X)| ≤ 18*rho*L := by
    have h := affine_input_error hr hL hv hw hf
    convert h using 1 <;> congr 1 <;> ring
  have hideal : |a+u*(b-a)+v*(c-a)-X| ≤ 4*L := by
    have h := abs_add_le (a+u*(b-a)-X) (v*(c-a))
    have h₁ := difference_abs hAB hX
    have h₂ := difference_abs hc ha
    have h₃ := mul_le_mul hv h₂ (abs_nonneg (c-a)) (by norm_num : (0:ℝ) ≤ 1)
    rw [abs_mul] at h
    have heq : a+u*(b-a)+v*(c-a)-X = (a+u*(b-a)-X)+v*(c-a) := by ring
    rw [heq]
    linarith
  have h := round_propagate (C := 18) (K := 4) hr hL heta (by linarith) hrin hideal hR
  norm_num at h
  exact h


lemma round_self {rho eta a : ℝ} (hr : 0 ≤ rho) (he : 0 ≤ eta) : RoundError rho eta a a := by
  unfold RoundError
  simp only [sub_self, abs_zero]
  positivity

theorem face_scalar_error {rho eta L a b c x u v E F AX W R : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/1024) (he : 0 ≤ eta)
    (hL : 0 ≤ L) (heta : eta ≤ rho^2*L)
    (ha : |a| ≤ L) (hb : |b| ≤ L) (hc : |c| ≤ L) (hx : |x| ≤ L)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hE : RoundError rho eta (b-a) E) (hF : RoundError rho eta (c-a) F)
    (hAX : RoundError rho eta (a-x) AX)
    (hW : RoundError rho eta (AX+u*E) W) (hR : RoundError rho eta (W+v*F) R) :
    |R-(a+u*(b-a)+v*(c-a)-x)| ≤ 23*rho*L := by
  have h := crossing_scalar_error (p₀ := x) (p₁ := x) (s := 0) (P := 0) (AP := AX)
    hr hrmax hL heta ha hb hc hx hx (by norm_num) (by norm_num) hu0 hu1 hv0 hv1
    hE hF (by simpa only [sub_self] using round_self (a := 0) hr he) hAX
    (by simpa using round_self (a := AX) hr he) hW hR
  simpa using h

theorem segment_scalar_error {rho eta L p₀ p₁ q₀ q₁ s t P Q AP W R : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/1024) (hL : 0 ≤ L) (heta : eta ≤ rho^2*L)
    (hp₀ : |p₀| ≤ L) (hp₁ : |p₁| ≤ L) (hq₀ : |q₀| ≤ L) (hq₁ : |q₁| ≤ L)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hP : RoundError rho eta (p₁-p₀) P) (hQ : RoundError rho eta (q₁-q₀) Q)
    (hAP : RoundError rho eta (q₀-p₀) AP)
    (hW : RoundError rho eta (AP+t*Q) W) (hR : RoundError rho eta (W-s*P) R) :
    |R-(((1-t)*q₀+t*q₁)-((1-s)*p₀+s*p₁))| ≤ 15*rho*L := by
  have hp := round_difference hr hrmax hL heta hp₁ hp₀ hP
  have hq := round_difference hr hrmax hL heta hq₁ hq₀ hQ
  have hap := round_difference hr hrmax hL heta hq₀ hp₀ hAP
  have ht : |t| ≤ 1 := by rwa [abs_of_nonneg ht0]
  have hs : |(-s)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hs0]; exact hs1
  have hX := interval_abs hL hp₀ hp₁ hs0 hs1
  have hY := interval_abs hL hq₀ hq₁ ht0 ht1
  have hwin : |(AP+t*Q)-(((1-t)*q₀+t*q₁)-p₀)| ≤ 6*rho*L := by
    have h := affine_input_error hr hL ht hap hq
    convert h using 1 <;> congr 1 <;> ring
  have hw : |W-(((1-t)*q₀+t*q₁)-p₀)| ≤ 9*rho*L := by
    have h := round_propagate (C := 6) (K := 2) hr hL heta (by linarith) hwin
      (difference_abs hY hp₀) hW
    norm_num at h ⊢; exact h
  have hrin : |(W-s*P)-(((1-t)*q₀+t*q₁)-((1-s)*p₀+s*p₁))| ≤ 12*rho*L := by
    have h := affine_input_error hr hL hs hw hp
    convert h using 1 <;> congr 1 <;> ring
  have h := round_propagate (C := 12) (K := 2) hr hL heta (by linarith) hrin
    (difference_abs hY hX) hR
  norm_num at h ⊢; exact h

theorem segment_endpoint_scalar_error {rho eta L p₀ p₁ q₀ q₁ t P Q AP D R : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/1024) (hL : 0 ≤ L) (heta : eta ≤ rho^2*L)
    (hp₀ : |p₀| ≤ L) (hp₁ : |p₁| ≤ L) (hq₀ : |q₀| ≤ L) (hq₁ : |q₁| ≤ L)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hP : RoundError rho eta (p₁-p₀) P) (hQ : RoundError rho eta (q₁-q₀) Q)
    (hAP : RoundError rho eta (q₀-p₀) AP)
    (hD : RoundError rho eta (AP-P) D) (hR : RoundError rho eta (D+t*Q) R) :
    |R-(((1-t)*q₀+t*q₁)-p₁)| ≤ 15*rho*L := by
  have hp := round_difference hr hrmax hL heta hp₁ hp₀ hP
  have hq := round_difference hr hrmax hL heta hq₁ hq₀ hQ
  have hap := round_difference hr hrmax hL heta hq₀ hp₀ hAP
  have ht : |t| ≤ 1 := by rwa [abs_of_nonneg ht0]
  have hY := interval_abs hL hq₀ hq₁ ht0 ht1
  have hdin : |(AP-P)-(q₀-p₁)| ≤ 6*rho*L := by
    have h := affine_input_error hr hL (t := -1) (by norm_num) hap hp
    convert h using 1 <;> congr 1 <;> ring
  have hd : |D-(q₀-p₁)| ≤ 9*rho*L := by
    have h := round_propagate (C := 6) (K := 2) hr hL heta (by linarith) hdin
      (difference_abs hq₀ hp₁) hD
    norm_num at h ⊢; exact h
  have hrin : |(D+t*Q)-(((1-t)*q₀+t*q₁)-p₁)| ≤ 12*rho*L := by
    have h := affine_input_error hr hL ht hd hq
    convert h using 1 <;> congr 1 <;> ring
  have h := round_propagate (C := 12) (K := 2) hr hL heta (by linarith) hrin
    (difference_abs hY hp₁) hR
  norm_num at h ⊢; exact h

theorem bc_scalar_error {rho eta L a b c x t E F AX E2 BX R : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/1024) (hL : 0 ≤ L) (heta : eta ≤ rho^2*L)
    (ha : |a| ≤ L) (hb : |b| ≤ L) (hc : |c| ≤ L) (hx : |x| ≤ L)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hE : RoundError rho eta (b-a) E) (hF : RoundError rho eta (c-a) F)
    (hAX : RoundError rho eta (a-x) AX)
    (hE2 : RoundError rho eta (F-E) E2) (hBX : RoundError rho eta (AX+E) BX)
    (hR : RoundError rho eta (BX+t*E2) R) :
    |R-(((1-t)*b+t*c)-x)| ≤ 21*rho*L := by
  have he := round_difference hr hrmax hL heta hb ha hE
  have hf := round_difference hr hrmax hL heta hc ha hF
  have hax := round_difference hr hrmax hL heta ha hx hAX
  have ht : |t| ≤ 1 := by rwa [abs_of_nonneg ht0]
  have hY := interval_abs hL hb hc ht0 ht1
  have he2in : |(F-E)-(c-b)| ≤ 6*rho*L := by
    have h := affine_input_error hr hL (t := -1) (by norm_num) hf he
    convert h using 1 <;> congr 1 <;> ring
  have he2 : |E2-(c-b)| ≤ 9*rho*L := by
    have h := round_propagate (C := 6) (K := 2) hr hL heta (by linarith) he2in
      (difference_abs hc hb) hE2
    norm_num at h ⊢; exact h
  have hbxin : |(AX+E)-(b-x)| ≤ 6*rho*L := by
    have h := affine_input_error hr hL (t := 1) (by norm_num) hax he
    convert h using 1 <;> congr 1 <;> ring
  have hbx : |BX-(b-x)| ≤ 9*rho*L := by
    have h := round_propagate (C := 6) (K := 2) hr hL heta (by linarith) hbxin
      (difference_abs hb hx) hBX
    norm_num at h ⊢; exact h
  have hrin : |(BX+t*E2)-(((1-t)*b+t*c)-x)| ≤ 18*rho*L := by
    have h := affine_input_error hr hL ht hbx he2
    convert h using 1 <;> congr 1 <;> ring
  have h := round_propagate (C := 18) (K := 2) hr hL heta (by linarith) hrin
    (difference_abs hY hx) hR
  norm_num at h ⊢; exact h

/-- A rounded complement needs no exact-subtraction theorem for the loose lower bound. -/
lemma complement_error {rho eta u w : ℝ} (hr : 0 ≤ rho) (he : eta ≤ rho)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hw : RoundError rho eta (1-u) w) :
    |w-(1-u)| ≤ (3/2)*rho := by
  unfold RoundError at hw
  rw [abs_of_nonneg (by linarith : 0 ≤ 1-u)] at hw
  nlinarith [mul_nonneg hr hu0]

lemma capped_weight_sum {rho eta u w v : ℝ} (hr : 0 ≤ rho) (he : eta ≤ rho)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hw : RoundError rho eta (1-u) w)
    (hv : v ≤ w) : u+v ≤ 1+(3/2)*rho := by
  have h := (abs_le.mp (complement_error hr he hu0 hu1 hw)).2
  linarith

/-- Complement rounding in an edge embedding contributes at most 3ρL per coordinate. -/
lemma edge_embedding_error {rho L a b t w : ℝ} (hr : 0 ≤ rho) (hL : 0 ≤ L)
    (ha : |a| ≤ L) (hb : |b| ≤ L) (hw : |w-(1-t)| ≤ (3/2)*rho) :
    |(w*a+t*b)-((1-t)*a+t*b)| ≤ (3/2)*rho*L := by
  have he : (w*a+t*b)-((1-t)*a+t*b) = (w-(1-t))*a := by ring
  rw [he, abs_mul]
  exact mul_le_mul hw ha (abs_nonneg _) (by positivity)

lemma rounded_accumulation {rho eta a b A out e : ℝ}
    (hr : 0 ≤ rho) (ha : 0 ≤ a) (hb : 0 ≤ b) (he : |A-a| ≤ e)
    (hout : RoundError rho eta (A+b) out) :
    |out-(a+b)| ≤ (1+rho)*e+rho*(a+b)+eta/2 := by
  have hi : |A+b| ≤ e+a+b := by
    have h := abs_add_le (A-a) (a+b)
    have heq : A-a+(a+b) = A+b := by ring
    rw [heq, abs_of_nonneg (add_nonneg ha hb)] at h
    linarith
  have hm := mul_le_mul_of_nonneg_left hi hr
  have h := abs_triangle_sub out (A+b) (a+b)
  have heq : A+b-(a+b) = A-a := by ring
  rw [heq] at h
  unfold RoundError at hout
  nlinarith

/-- Error of the exact multiply/FMA/FMA schedule used by `dot3(r,r)`. -/
theorem squared_norm_error {rho eta x y z a b q : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1/1024) (he : 0 ≤ eta)
    (ha : RoundError rho eta (x*x) a)
    (hb : RoundError rho eta (y*y+a) b)
    (hq : RoundError rho eta (z*z+b) q) :
    |q-(x*x+y*y+z*z)| ≤ 3*rho*(1+rho)^2*(x*x+y*y+z*z)+2*eta := by
  have ha' : |a-x*x| ≤ rho*(x*x)+eta/2 := by
    simpa only [RoundError, abs_of_nonneg (mul_self_nonneg x)] using ha
  have hb' : RoundError rho eta (a+y*y) b := by simpa [add_comm] using hb
  have hq' : RoundError rho eta (b+z*z) q := by simpa [add_comm] using hq
  have hB := rounded_accumulation hr (mul_self_nonneg x) (mul_self_nonneg y) ha' hb'
  have hQ := rounded_accumulation hr (add_nonneg (mul_self_nonneg x) (mul_self_nonneg y))
    (mul_self_nonneg z) hB hq'
  have hx := mul_self_nonneg x; have hy := mul_self_nonneg y; have hz := mul_self_nonneg z
  have hc : 0 ≤ rho^2 := sq_nonneg rho
  have hc3 : 0 ≤ rho^3 := pow_nonneg hr 3
  have het : ((1+rho)^2+(1+rho)+1)/2 ≤ 2 := by nlinarith
  have het' := mul_le_mul_of_nonneg_right het he
  have hxx := mul_nonneg (show 0 ≤ 3*rho*(1+rho)^2-((1+rho)^2*rho+(1+rho)*rho+rho) by nlinarith) hx
  have hyy := mul_nonneg (show 0 ≤ 3*rho*(1+rho)^2-((1+rho)*rho+rho) by nlinarith) hy
  have hzz := mul_nonneg (show 0 ≤ 3*rho*(1+rho)^2-rho by nlinarith) hz
  nlinarith

end DistanceAccuracy.Reconstruction

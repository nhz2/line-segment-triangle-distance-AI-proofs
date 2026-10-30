import DistanceAccuracy.ReconstructionIEEE

/-! Lower accuracy of concrete candidate squared distances. -/
namespace DistanceAccuracy.CandidateLower
open FP.IEEE FP.IEEE.Interchange
open IEEEAlgorithm IEEEBridge OperationBounds Geometry LowerBound
variable (I : Interchange) [I.Valid]

/-- Lower accuracy plus a magnitude reserve. For B=120ρL the last bound is10L. -/
noncomputable def Safe (d B : ℝ) (q : I.Word) : Prop :=
  ∃ z : ℚ, value? I q = some z ∧ 0 ≤ z ∧ d-Real.sqrt (z : ℝ) ≤ B ∧
    Real.sqrt (z : ℝ) ≤ B/(12*I.format.unitRoundoff)

/-- A local convex-hull witness suffices; the candidate's returned weights are irrelevant. -/
theorem from_reconstruction {S T : Set E3} {A B C D E F : E3} {r : Vec3 I}
    {rv : Fin 3 → ℚ} {u v s t d L : ℝ}
    (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hAm : A ∈ S) (hBm : B ∈ S) (hCm : C ∈ S)
    (hDm : D ∈ T) (hEm : E ∈ T) (hFm : F ∈ T)
    (hd : ∀ a ∈ S, ∀ b ∈ T, d ≤ ‖b-a‖)
    (hL : 0 ≤ L) (hA : ∀ k, |A k| ≤ L) (hB : ∀ k, |B k| ≤ L)
    (hC : ∀ k, |C k| ≤ L) (hD : ∀ k, |D k| ≤ L)
    (hE : ∀ k, |E k| ≤ L) (hF : ∀ k, |F k| ≤ L)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v)
    (huv : u+v ≤ 1+(3/2)*I.format.unitRoundoff)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (hst : s+t ≤ 1+(3/2)*I.format.unitRoundoff)
    (hr : ∀ k, value? I (r k) = some (rv k))
    (hrec : ∀ k, |(rv k : ℝ)-(bary D E F s t-bary A B C u v) k| ≤ 29*I.format.unitRoundoff*L)
    (hrho : I.format.unitRoundoff ≤ 1/1024) (heta : I.format.minSubnormal ≤ 1)
    (hunder : 2*Real.sqrt I.format.minSubnormal ≤ I.format.unitRoundoff*L)
    (hlim : 512*L*L+4 < I.format.overflowThreshold) :
    Safe I d (120*I.format.unitRoundoff*L) (dot3 I r r) := by
  let R : E3 := WithLp.toLp 2 (fun k => (rv k : ℝ))
  have hρ := I.format.unitRoundoff_pos.le
  have hη : 0 ≤ I.format.minSubnormal := by unfold Format.minSubnormal; positivity
  have hX := bary_coordinate_bound (by positivity) hL hu0 hu1 hv0 huv hA hB hC
  have hY := bary_coordinate_bound (by positivity) hL hs0 hs1 ht0 hst hD hE hF
  have hrBound : ∀ k, |(rv k : ℝ)| ≤ 3*L := by
    intro k
    have hxy := Reconstruction.difference_abs (hY k) (hX k)
    have hh := abs_add_le ((rv k : ℝ)-(bary D E F s t-bary A B C u v) k)
      ((bary D E F s t-bary A B C u v) k)
    rw [sub_add_cancel] at hh
    have he := hrec k
    have hm := mul_le_mul_of_nonneg_right hrho hL
    change |(bary D E F s t-bary A B C u v) k| ≤ _ at hxy
    nlinarith
  obtain ⟨q, hq, hq0, hqerr⟩ := ReconstructionIEEE.dot3_self_finite_error I hr
    (by positivity : 0 ≤ 3*L) hrBound hrho heta (by nlinarith [sq_nonneg L])
  have hnorm : ‖R‖^2 = (rv 0 : ℝ)*(rv 0 : ℝ)+(rv 1 : ℝ)*(rv 1 : ℝ)+(rv 2 : ℝ)*(rv 2 : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [R, Fin.sum_univ_succ, pow_two, add_assoc]
  rw [← hnorm] at hqerr
  obtain ⟨hv', huv', _, _⟩ := repaired_weights (by positivity) hu0 hu1 hv0 huv
  obtain ⟨ht', hst', _, _⟩ := repaired_weights (by positivity) hs0 hs1 ht0 hst
  have hd' := hd _ (bary_mem hS hAm hBm hCm hu0 hv' huv')
    _ (bary_mem hT hDm hEm hFm hs0 ht' hst')
  refine ⟨q, hq, hq0, ?_, ?_⟩
  · exact lower_120 (r := R) hρ hrho hη hL hunder hA hB hC hD hE hF
      hu0 hu1 hv0 huv hs0 hs1 ht0 hst hrec hd' (by exact_mod_cast hq0) hqerr
  · have hnormBound : ‖R‖ ≤ 9*L := by
      have hh := norm_le_three (x := R) (by positivity : 0 ≤ 3*L) hrBound
      nlinarith
    have hev := LowerBound.norm_evaluation hρ hrho hη (norm_nonneg R)
      (show (0 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq0) hqerr
    have hupper := (abs_le.mp hev).2
    have hm := mul_le_mul_of_nonneg_left hnormBound (show 0 ≤ 2*I.format.unitRoundoff by positivity)
    have hcoef := mul_le_mul_of_nonneg_right hrho hL
    have hden : 120*I.format.unitRoundoff*L/(12*I.format.unitRoundoff) = 10*L := by
      field_simp [ne_of_gt I.format.unitRoundoff_pos]
      <;> ring
    rw [hden]
    nlinarith

lemma choose_safe {d B : ℝ} {a b : Candidate I}
    (ha : Safe I d B a.q) (hb : Safe I d B b.q) : Safe I d B (choose I a b).q := by
  unfold choose
  split <;> assumption

lemma reverse_safe {d B : ℝ} {c : Candidate I} (hc : Safe I d B c.q) :
    Safe I d B (reverse I c).q := hc

noncomputable def ratVec (x : Fin 3 → ℚ) : E3 := WithLp.toLp 2 (fun k => (x k : ℝ))

/-- The actual face candidate has the lower bound for arbitrary upstream normal,
    reciprocal, and solve results, including exceptional values. -/
theorem face_safe {S T : Set E3} {a b c x n : Vec3 I} {A B C X : Fin 3 → ℚ} {d L : ℝ}
    (ha : ∀ k, value? I (a k) = some (A k)) (hb : ∀ k, value? I (b k) = some (B k))
    (hc : ∀ k, value? I (c k) = some (C k)) (hx : ∀ k, value? I (x k) = some (X k))
    (hS : Convex ℝ S) (hT : Convex ℝ T) (hXm : ratVec X ∈ S)
    (hAm : ratVec A ∈ T) (hBm : ratVec B ∈ T) (hCm : ratVec C ∈ T)
    (hd : ∀ p ∈ S, ∀ q ∈ T, d ≤ ‖q-p‖)
    (hL : 0 ≤ L) (hA : ∀ k, |(A k : ℝ)| ≤ L) (hB : ∀ k, |(B k : ℝ)| ≤ L)
    (hC : ∀ k, |(C k : ℝ)| ≤ L) (hX : ∀ k, |(X k : ℝ)| ≤ L)
    (hone : value? I (one I) = some 1) (hrep : I.format.Representable 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024) (heta1 : I.format.minSubnormal ≤ 1)
    (hetarho : I.format.minSubnormal ≤ I.format.unitRoundoff)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hunder : 2*Real.sqrt I.format.minSubnormal ≤ I.format.unitRoundoff*L)
    (hlin : 32*L < I.format.overflowThreshold)
    (hquad : 512*L*L+4 < I.format.overflowThreshold) :
    Safe I d (120*I.format.unitRoundoff*L)
      (face I (vsub I a x) (vsub I b a) (vsub I c a) n).q := by
  let e := vsub I b a
  let f := vsub I c a
  let ax := vsub I a x
  let ia := div I (one I) (dot3 I e e)
  let c1 := mul I (dot3 I e f) ia
  let rawV := div I (neg I (dot3 I n (cross3 I e ax))) (dot3 I n n)
  let v0 := clamp01nan I rawV
  let rawU := fma I (neg I v0) c1 (mul I (neg I (dot3 I e ax)) ia)
  let u := clamp01nan I rawU
  let w := sub I (one I) u
  let v := if lt I v0 w then v0 else w
  have hlim1 : (1 : ℝ) < I.format.overflowThreshold := by nlinarith [sq_nonneg L]
  obtain ⟨U, V, hu, hv, hu0, hu1, hv0, hv1, huv⟩ :=
    capped_clamps_bounded I rawU rawV hone hrep hlim1
  change value? I u = some U at hu
  change value? I v = some V at hv
  choose rv hrv herr using fun k => ReconstructionIEEE.face_trace I
    (ha k) (hb k) (hc k) (hx k) hu hv hL (hA k) (hB k) (hC k) (hX k)
    hu0 hu1 hv0 hv1 hrho heta hlin
  have hu0r : (0 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hu0
  have hu1r : (U : ℝ) ≤ 1 := by exact_mod_cast hu1
  have hv0r : (0 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hv0
  have hr := I.format.unitRoundoff_pos.le
  change Safe I d (120*I.format.unitRoundoff*L) (dot3 I (fma3 I v f (fma3 I u e ax)) (fma3 I v f (fma3 I u e ax)))
  apply from_reconstruction I hS hT hXm hXm hXm hAm hBm hCm hd hL hX hX hX hA hB hC
    (u := 0) (v := 0) (s := (U : ℝ)) (t := (V : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by nlinarith)
    hu0r hu1r hv0r (by linarith) hrv _ hrho heta1 hunder hquad
  intro k
  have hh := herr k
  simp only [bary, ratVec, zero_smul, add_zero, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, WithLp.toLp_ofLp, smul_eq_mul]
  change |(rv k : ℝ)-((A k : ℝ)+(U : ℝ)*((B k : ℝ)-(A k : ℝ))+
    (V : ℝ)*((C k : ℝ)-(A k : ℝ))-(X k : ℝ))| ≤ _
  nlinarith [mul_nonneg hr hL]
theorem crossing_safe {S T : Set E3} {a b c n : Vec3 I} {x : Segment I} {A B C P₀ P₁ : Fin 3 → ℚ} {d L : ℝ}
    (ha : ∀ k, value? I (a k) = some (A k)) (hb : ∀ k, value? I (b k) = some (B k))
    (hc : ∀ k, value? I (c k) = some (C k)) (hp0 : ∀ k, value? I (x 0 k) = some (P₀ k))
    (hp1 : ∀ k, value? I (x 1 k) = some (P₁ k))
    (hS : Convex ℝ S) (hT : Convex ℝ T) (hp0m : ratVec P₀ ∈ S) (hp1m : ratVec P₁ ∈ S)
    (hAm : ratVec A ∈ T) (hBm : ratVec B ∈ T) (hCm : ratVec C ∈ T)
    (hd : ∀ p ∈ S, ∀ q ∈ T, d ≤ ‖q-p‖)
    (hL : 0 ≤ L) (hA : ∀ k, |(A k : ℝ)| ≤ L) (hB : ∀ k, |(B k : ℝ)| ≤ L)
    (hC : ∀ k, |(C k : ℝ)| ≤ L) (hP0 : ∀ k, |(P₀ k : ℝ)| ≤ L) (hP1 : ∀ k, |(P₁ k : ℝ)| ≤ L)
    (hone : value? I (one I) = some 1) (hrep : I.format.Representable 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024) (heta1 : I.format.minSubnormal ≤ 1)
    (hetarho : I.format.minSubnormal ≤ I.format.unitRoundoff)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hunder : 2*Real.sqrt I.format.minSubnormal ≤ I.format.unitRoundoff*L)
    (hlin : 32*L < I.format.overflowThreshold)
    (hquad : 512*L*L+4 < I.format.overflowThreshold) :
    Safe I d (120*I.format.unitRoundoff*L)
      (crossing I x a (vsub I b a) (vsub I c a) n).q := by
  let e := vsub I b a
  let f := vsub I c a
  let p := vsub I (x 1) (x 0)
  let ap := vsub I a (x 0)
  let sw := clamp01nan I (div I (dot3 I n ap) (dot3 I n p))
  let ax := fma3 I (neg I sw) p ap
  let ia := div I (one I) (dot3 I e e)
  let c1 := mul I (dot3 I e f) ia
  let rawV := div I (neg I (dot3 I n (cross3 I e ax))) (dot3 I n n)
  let v0 := clamp01nan I rawV
  let rawU := fma I (neg I v0) c1 (mul I (neg I (dot3 I e ax)) ia)
  let u := clamp01nan I rawU
  let w := sub I (one I) u
  let v := if lt I v0 w then v0 else w
  have hlim1 : (1 : ℝ) < I.format.overflowThreshold := by nlinarith [sq_nonneg L]
  obtain ⟨U, V, hu, hv, hu0, hu1, hv0, hv1, huv⟩ :=
    capped_clamps_bounded I rawU rawV hone hrep hlim1
  change value? I u = some U at hu
  change value? I v = some V at hv
  obtain ⟨W, hsw, hsw0, hsw1⟩ := clamp01nan_bounded I hone (div I (dot3 I n ap) (dot3 I n p))
  choose rv hrv herr using fun k => ReconstructionIEEE.crossing_trace I
    (ha k) (hb k) (hc k) (hp0 k) (hp1 k) hsw hu hv hL (hA k) (hB k) (hC k) (hP0 k) (hP1 k)
    hsw0 hsw1 hu0 hu1 hv0 hv1 hrho heta hlin
  have hu0r : (0 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hu0
  have hu1r : (U : ℝ) ≤ 1 := by exact_mod_cast hu1
  have hv0r : (0 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hv0
  have hr := I.format.unitRoundoff_pos.le
  change Safe I d (120*I.format.unitRoundoff*L) (dot3 I (fma3 I v f (fma3 I u e ax)) (fma3 I v f (fma3 I u e ax)))
  have hsw0r : (0 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hsw0
  have hsw1r : (W : ℝ) ≤ 1 := by exact_mod_cast hsw1
  apply from_reconstruction I hS hT hp0m hp1m hp0m hAm hBm hCm hd hL hP0 hP1 hP0 hA hB hC
    (u := (W : ℝ)) (v := 0) (s := (U : ℝ)) (t := (V : ℝ))
    hsw0r hsw1r (by norm_num) (by nlinarith)
    hu0r hu1r hv0r (by linarith) hrv _ hrho heta1 hunder hquad
  intro k
  have hh := herr k
  have hid : (bary (ratVec A) (ratVec B) (ratVec C) (U : ℝ) (V : ℝ) -
      bary (ratVec P₀) (ratVec P₁) (ratVec P₀) (W : ℝ) 0) k =
      (A k : ℝ)+(U : ℝ)*((B k : ℝ)-(A k : ℝ))+(V : ℝ)*((C k : ℝ)-(A k : ℝ))-
      ((1-(W : ℝ))*(P₀ k : ℝ)+(W : ℝ)*(P₁ k : ℝ)) := by
    simp [bary, ratVec]; ring
  rw [hid]
  nlinarith [mul_nonneg hr hL]


theorem segment_data_safe {S T : Set E3} {r : Vec3 I}
    {P₀ P₁ Q₀ Q₁ rv : Fin 3 → ℚ} {a b d L : ℝ}
    (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hp0m : ratVec P₀ ∈ S) (hp1m : ratVec P₁ ∈ S)
    (hq0m : ratVec Q₀ ∈ T) (hq1m : ratVec Q₁ ∈ T)
    (hd : ∀ p ∈ S, ∀ q ∈ T, d ≤ ‖q-p‖)
    (hL : 0 ≤ L) (hP0 : ∀ k, |(P₀ k : ℝ)| ≤ L) (hP1 : ∀ k, |(P₁ k : ℝ)| ≤ L)
    (hQ0 : ∀ k, |(Q₀ k : ℝ)| ≤ L) (hQ1 : ∀ k, |(Q₁ k : ℝ)| ≤ L)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hr : ∀ k, value? I (r k) = some (rv k))
    (herr : ∀ k, |(rv k : ℝ)-(((1-b)*(Q₀ k : ℝ)+b*(Q₁ k : ℝ))-
      ((1-a)*(P₀ k : ℝ)+a*(P₁ k : ℝ)))| ≤ 15*I.format.unitRoundoff*L)
    (hrho : I.format.unitRoundoff ≤ 1/1024) (heta1 : I.format.minSubnormal ≤ 1)
    (hunder : 2*Real.sqrt I.format.minSubnormal ≤ I.format.unitRoundoff*L)
    (hquad : 512*L*L+4 < I.format.overflowThreshold) :
    Safe I d (120*I.format.unitRoundoff*L) (dot3 I r r) := by
  have hρ := I.format.unitRoundoff_pos.le
  apply from_reconstruction I hS hT hp0m hp1m hp0m hq0m hq1m hq0m hd hL
    hP0 hP1 hP0 hQ0 hQ1 hQ0 (u := a) (v := 0) (s := b) (t := 0)
    ha0 ha1 (by norm_num) (by nlinarith) hb0 hb1 (by norm_num) (by nlinarith)
    hr _ hrho heta1 hunder hquad
  intro k
  have hid : (bary (ratVec Q₀) (ratVec Q₁) (ratVec Q₀) b 0-
    bary (ratVec P₀) (ratVec P₁) (ratVec P₀) a 0) k =
    ((1-b)*(Q₀ k : ℝ)+b*(Q₁ k : ℝ))-((1-a)*(P₀ k : ℝ)+a*(P₁ k : ℝ)) := by
    simp [bary, ratVec]; ring
  rw [hid]
  have hh := herr k
  nlinarith [mul_nonneg hρ hL]

/-- All three actual segment/segment candidates satisfy the lower bound. -/
theorem segmentSegment_safe {S T : Set E3} {x y : Segment I}
    {P₀ P₁ Q₀ Q₁ : Fin 3 → ℚ} {d L : ℝ}
    (hp0 : ∀ k, value? I (x 0 k) = some (P₀ k))
    (hp1 : ∀ k, value? I (x 1 k) = some (P₁ k))
    (hq0 : ∀ k, value? I (y 0 k) = some (Q₀ k))
    (hq1 : ∀ k, value? I (y 1 k) = some (Q₁ k))
    (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hp0m : ratVec P₀ ∈ S) (hp1m : ratVec P₁ ∈ S)
    (hq0m : ratVec Q₀ ∈ T) (hq1m : ratVec Q₁ ∈ T)
    (hd : ∀ p ∈ S, ∀ q ∈ T, d ≤ ‖q-p‖)
    (hL : 0 ≤ L) (hP0 : ∀ k, |(P₀ k : ℝ)| ≤ L) (hP1 : ∀ k, |(P₁ k : ℝ)| ≤ L)
    (hQ0 : ∀ k, |(Q₀ k : ℝ)| ≤ L) (hQ1 : ∀ k, |(Q₁ k : ℝ)| ≤ L)
    (hone : value? I (one I) = some 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024) (heta1 : I.format.minSubnormal ≤ 1)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hunder : 2*Real.sqrt I.format.minSubnormal ≤ I.format.unitRoundoff*L)
    (hlin : 32*L < I.format.overflowThreshold)
    (hquad : 512*L*L+4 < I.format.overflowThreshold) :
    Safe I d (120*I.format.unitRoundoff*L) (segmentSegment I x y).q := by
  let P := vsub I (x 1) (x 0)
  let Q := vsub I (y 1) (y 0)
  let R := vsub I (y 0) (x 0)
  let b := dot3 I P Q
  let c := dot3 I Q Q
  let e := dot3 I Q R
  let n := cross3 I P Q
  let tw := clamp01nan I (div I (neg I (dot3 I n (cross3 I P R))) (dot3 I n n))
  let sw := clamp01nan I (div I (fma I tw b (dot3 I P R)) (dot3 I P P))
  let t0w := clamp01nan I (div I (neg I e) c)
  let t1w := clamp01nan I (div I (sub I b e) c)
  obtain ⟨t, ht, ht0, ht1⟩ := clamp01nan_bounded I hone (div I (neg I (dot3 I n (cross3 I P R))) (dot3 I n n))
  obtain ⟨s, hs, hs0, hs1⟩ := clamp01nan_bounded I hone (div I (fma I tw b (dot3 I P R)) (dot3 I P P))
  obtain ⟨t0, ht0w, ht00, ht01⟩ := clamp01nan_bounded I hone (div I (neg I e) c)
  obtain ⟨t1, ht1w, ht10, ht11⟩ := clamp01nan_bounded I hone (div I (sub I b e) c)
  have hinside : Safe I d (120*I.format.unitRoundoff*L)
      (dot3 I (fma3 I (neg I sw) P (fma3 I tw Q R)) (fma3 I (neg I sw) P (fma3 I tw Q R))) := by
    choose rv hrv herr using fun k => ReconstructionIEEE.segment_trace I
      (hp0 k) (hp1 k) (hq0 k) (hq1 k) hs ht hL (hP0 k) (hP1 k) (hQ0 k) (hQ1 k)
      hs0 hs1 ht0 ht1 hrho heta hlin
    exact segment_data_safe I hS hT hp0m hp1m hq0m hq1m hd hL hP0 hP1 hQ0 hQ1
      (by exact_mod_cast hs0) (by exact_mod_cast hs1) (by exact_mod_cast ht0) (by exact_mod_cast ht1)
      hrv herr hrho heta1 hunder hquad
  have hbest : Safe I d (120*I.format.unitRoundoff*L)
      (dot3 I (fma3 I t0w Q R) (fma3 I t0w Q R)) := by
    choose rv hrv herr using fun k => ReconstructionIEEE.point_segment_trace I
      (hp0 k) (hq0 k) (hq1 k) ht0w hL (hP0 k) (hQ0 k) (hQ1 k) ht00 ht01 hrho heta hlin
    apply segment_data_safe I hS hT hp0m hp1m hq0m hq1m hd hL hP0 hP1 hQ0 hQ1
      (a := 0) (b := (t0 : ℝ)) (by norm_num) (by norm_num)
      (by exact_mod_cast ht00) (by exact_mod_cast ht01) hrv _ hrho heta1 hunder hquad
    simpa using herr
  have hend : Safe I d (120*I.format.unitRoundoff*L)
      (dot3 I (fma3 I t1w Q (vsub I R P)) (fma3 I t1w Q (vsub I R P))) := by
    choose rv hrv herr using fun k => ReconstructionIEEE.segment_end1_trace I
      (hp0 k) (hp1 k) (hq0 k) (hq1 k) ht1w hL (hP0 k) (hP1 k) (hQ0 k) (hQ1 k)
      ht10 ht11 hrho heta hlin
    apply segment_data_safe I hS hT hp0m hp1m hq0m hq1m hd hL hP0 hP1 hQ0 hQ1
      (a := 1) (b := (t1 : ℝ)) (by norm_num) (by norm_num)
      (by exact_mod_cast ht10) (by exact_mod_cast ht11) hrv _ hrho heta1 hunder hquad
    simpa using herr
  exact choose_safe I (choose_safe I hbest hend) hinside

lemma ratVec_eq_decodeVec {x : Vec3 I} {X : Fin 3 → ℚ}
    (hx : ∀ k, value? I (x k) = some (X k)) : ratVec X = decodeVec I x := by
  ext k
  simp [ratVec, decodeVec, real_decode I (hx k)]

/-- Actual point/segment candidate; no accuracy premise on the quotient solve. -/
theorem pointSegment_safe {S T : Set E3} {x : Vec3 I} {y : Segment I}
    {X Q₀ Q₁ : Fin 3 → ℚ} {d L : ℝ}
    (hx : ∀ k, value? I (x k) = some (X k))
    (hq0 : ∀ k, value? I (y 0 k) = some (Q₀ k))
    (hq1 : ∀ k, value? I (y 1 k) = some (Q₁ k))
    (hS : Convex ℝ S) (hT : Convex ℝ T) (hXm : ratVec X ∈ S)
    (hq0m : ratVec Q₀ ∈ T) (hq1m : ratVec Q₁ ∈ T)
    (hd : ∀ p ∈ S, ∀ q ∈ T, d ≤ ‖q-p‖)
    (hL : 0 ≤ L) (hX : ∀ k, |(X k : ℝ)| ≤ L)
    (hQ0 : ∀ k, |(Q₀ k : ℝ)| ≤ L) (hQ1 : ∀ k, |(Q₁ k : ℝ)| ≤ L)
    (hone : value? I (one I) = some 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024) (heta1 : I.format.minSubnormal ≤ 1)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hunder : 2*Real.sqrt I.format.minSubnormal ≤ I.format.unitRoundoff*L)
    (hlin : 32*L < I.format.overflowThreshold)
    (hquad : 512*L*L+4 < I.format.overflowThreshold) :
    Safe I d (120*I.format.unitRoundoff*L) (pointSegment I x y).q := by
  let Q := vsub I (y 1) (y 0)
  let R := vsub I (y 0) x
  let tw := clamp01nan I (div I (neg I (dot3 I R Q)) (dot3 I Q Q))
  obtain ⟨t, ht, ht0, ht1⟩ := clamp01nan_bounded I hone (div I (neg I (dot3 I R Q)) (dot3 I Q Q))
  choose rv hrv herr using fun k => ReconstructionIEEE.point_segment_trace I
    (hx k) (hq0 k) (hq1 k) ht hL (hX k) (hQ0 k) (hQ1 k) ht0 ht1 hrho heta hlin
  change Safe I d (120*I.format.unitRoundoff*L) (dot3 I (fma3 I tw Q R) (fma3 I tw Q R))
  apply segment_data_safe I hS hT hXm hXm hq0m hq1m hd hL hX hX hQ0 hQ1
    (a := 0) (b := (t : ℝ)) (by norm_num) (by norm_num)
    (by exact_mod_cast ht0) (by exact_mod_cast ht1) hrv _ hrho heta1 hunder hquad
  simpa using herr

theorem pointPoint_safe {S T : Set E3} {x y : Vec3 I} {X Y : Fin 3 → ℚ} {d L : ℝ}
    (hx : ∀ k, value? I (x k) = some (X k)) (hy : ∀ k, value? I (y k) = some (Y k))
    (hS : Convex ℝ S) (hT : Convex ℝ T) (hXm : ratVec X ∈ S) (hYm : ratVec Y ∈ T)
    (hd : ∀ p ∈ S, ∀ q ∈ T, d ≤ ‖q-p‖)
    (hL : 0 ≤ L) (hX : ∀ k, |(X k : ℝ)| ≤ L) (hY : ∀ k, |(Y k : ℝ)| ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1/1024) (heta1 : I.format.minSubnormal ≤ 1)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hunder : 2*Real.sqrt I.format.minSubnormal ≤ I.format.unitRoundoff*L)
    (hlin : 32*L < I.format.overflowThreshold)
    (hquad : 512*L*L+4 < I.format.overflowThreshold) :
    Safe I d (120*I.format.unitRoundoff*L) (pointPoint I x y).q := by
  have hρ := I.format.unitRoundoff_pos.le
  choose rv hrv herr hbound using fun k => ReconstructionIEEE.sub_coordinates I
    (hy k) (hx k) hL (hY k) (hX k) hrho heta (by linarith)
  apply segment_data_safe I hS hT hXm hXm hYm hYm hd hL hX hX hY hY
    (a := 0) (b := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hrv _ hrho heta1 hunder hquad
  intro k
  have hh := Reconstruction.round_difference hρ hrho hL heta (hY k) (hX k) (herr k)
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  nlinarith [mul_nonneg hρ hL]

end DistanceAccuracy.CandidateLower

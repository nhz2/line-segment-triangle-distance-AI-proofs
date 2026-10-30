import FP.IEEE.Software.ProductResidual
import DistanceAccuracy.OperationBounds
import DistanceAccuracy.LowerBound

/-! Concrete IEEE bridges for the reconstruction and lower-bound estimates. -/
namespace DistanceAccuracy.ReconstructionIEEE
open FP.IEEE FP.IEEE.Interchange
open IEEEAlgorithm IEEEBridge OperationBounds
variable (I : Interchange) [I.Valid]

lemma fma_value_eq_round {a b c : I.Word} {x y z r : ℚ}
    (ha : value? I a = some x) (hb : value? I b = some y) (hc : value? I c = some z)
    (hr : value? I (fma I a b c) = some r)
    (hlim : |(x : ℝ)*(y : ℝ)+(z : ℝ)| < I.format.overflowThreshold) :
    (r : ℝ) = I.format.roundFinite ((x : ℝ)*(y : ℝ)+(z : ℝ)) := by
  have h := Software.mixedFma_even_cast I I I I a b c x y z ha hb hc
  rw [FP.IEEE.Format.round?, if_pos hlim] at h
  exact Option.some.inj ((real_decode I hr).symm.trans h)

lemma bounded_square {K x : ℝ} (hK : 0 ≤ K) (hx : |x| ≤ K) : x*x ≤ K*K := by
  have h := (sq_le_sq₀ (abs_nonneg x) hK).2 hx
  rw [sq_abs] at h
  nlinarith

/-- The concrete multiply/FMA/FMA squared norm is finite and nonnegative,
    with its forward error, from a coordinate bound alone. -/
theorem dot3_self_finite_error {a : Vec3 I} {x : Fin 3 → ℚ} {K : ℝ}
    (ha : ∀ k, value? I (a k) = some (x k))
    (hK : 0 ≤ K) (hx : ∀ k, |(x k : ℝ)| ≤ K)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ 1)
    (hlim : 8*K*K+4 < I.format.overflowThreshold) :
    ∃ q : ℚ, value? I (dot3 I a a) = some q ∧ 0 ≤ q ∧
      |(q : ℝ)-((x 0 : ℝ)*(x 0 : ℝ)+(x 1 : ℝ)*(x 1 : ℝ)+(x 2 : ℝ)*(x 2 : ℝ))| ≤
      3*I.format.unitRoundoff*(1+I.format.unitRoundoff)^2*
        ((x 0 : ℝ)*(x 0 : ℝ)+(x 1 : ℝ)*(x 1 : ℝ)+(x 2 : ℝ)*(x 2 : ℝ))+
      2*I.format.minSubnormal := by
  have hr := I.format.unitRoundoff_pos.le
  have he : 0 ≤ I.format.minSubnormal := by unfold Format.minSubnormal; positivity
  have h0 := bounded_square hK (hx 0)
  have h1 := bounded_square hK (hx 1)
  have h2 := bounded_square hK (hx 2)
  have hKsq := mul_self_nonneg K
  have hs0 := mul_self_nonneg (x 0 : ℝ)
  have hs1 := mul_self_nonneg (x 1 : ℝ)
  have hs2 := mul_self_nonneg (x 2 : ℝ)
  have hpLim : |(Software.binaryExact .mul (x 0) (x 0) : ℝ)| < I.format.overflowThreshold := by
    simp only [Software.binaryExact, Rat.cast_mul, abs_of_nonneg hs0]
    linarith
  obtain ⟨p, hp, hpErr⟩ := binary_exists_error I .mul (ha 0) (ha 0)
    (no_overflow_of_lt I _ hpLim)
  change value? I (mul I (a 0) (a 0)) = some p at hp
  have hpRound := binary_value_eq_round I .mul (ha 0) (ha 0) hp hpLim
  simp only [Software.binaryExact, Rat.cast_mul] at hpRound hpErr
  have hp0 : 0 ≤ (p : ℝ) := by rw [hpRound]; exact roundFinite_nonneg I.format hs0
  have hpBound : (p : ℝ) ≤ 2*K*K+1 := by
    have hh := (abs_le.mp hpErr).2
    rw [abs_of_nonneg hs0] at hh
    have hm := mul_le_mul_of_nonneg_left h0 hr
    have hm' := mul_le_mul_of_nonneg_right hrho hKsq
    nlinarith
  have hsLim : |(x 1 : ℝ)*(x 1 : ℝ)+(p : ℝ)| < I.format.overflowThreshold := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  obtain ⟨s, hs, hsErr⟩ := fma_exists_error I (ha 1) (ha 1) hp
    (no_overflow_of_lt I _ (by simpa only [Rat.cast_add, Rat.cast_mul] using hsLim))
  simp only [Rat.cast_add, Rat.cast_mul] at hsErr
  have hsRound := fma_value_eq_round I (ha 1) (ha 1) hp hs hsLim
  have hs0' : 0 ≤ (s : ℝ) := by rw [hsRound]; exact roundFinite_nonneg I.format (by positivity)
  have hsBound : (s : ℝ) ≤ 4*K*K+2 := by
    have hh := (abs_le.mp hsErr).2
    rw [abs_of_nonneg (by positivity : 0 ≤ (x 1 : ℝ)*(x 1 : ℝ)+(p : ℝ))] at hh
    have hm := mul_le_mul_of_nonneg_left (show (x 1 : ℝ)*(x 1 : ℝ)+(p : ℝ) ≤ 3*K*K+1 by linarith) hr
    have hm' := mul_le_mul_of_nonneg_right hrho (show 0 ≤ 3*K*K+1 by positivity)
    nlinarith
  have hqLim : |(x 2 : ℝ)*(x 2 : ℝ)+(s : ℝ)| < I.format.overflowThreshold := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  obtain ⟨q, hq, hqErr⟩ := fma_exists_error I (ha 2) (ha 2) hs
    (no_overflow_of_lt I _ (by simpa only [Rat.cast_add, Rat.cast_mul] using hqLim))
  simp only [Rat.cast_add, Rat.cast_mul] at hqErr
  have hqRound := fma_value_eq_round I (ha 2) (ha 2) hs hq hqLim
  have hq0 : 0 ≤ (q : ℝ) := by rw [hqRound]; exact roundFinite_nonneg I.format (by positivity)
  refine ⟨q, hq, by exact_mod_cast hq0, ?_⟩
  exact Reconstruction.squared_norm_error hr hrho he hpErr hsErr hqErr

/-- Coordinate subtraction: output existence, local error, and reusable range. -/
theorem sub_coordinates {a b : I.Word} {x y : ℚ} {L : ℝ}
    (ha : value? I a = some x) (hb : value? I b = some y)
    (hL : 0 ≤ L) (hx : |(x : ℝ)| ≤ L) (hy : |(y : ℝ)| ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 3*L < I.format.overflowThreshold) :
    ∃ z : ℚ, value? I (sub I a b) = some z ∧
      Reconstruction.RoundError I.format.unitRoundoff I.format.minSubnormal
        ((x : ℝ)-(y : ℝ)) (z : ℝ) ∧ |(z : ℝ)| ≤ 3*L := by
  have hr := I.format.unitRoundoff_pos.le
  have hd := Reconstruction.difference_abs hx hy
  have hh : |(Software.binaryExact .sub x y : ℝ)| < I.format.overflowThreshold := by
    simp only [Software.binaryExact, Rat.cast_sub]; linarith
  obtain ⟨z, hz, he⟩ := binary_exists_error I .sub ha hb (no_overflow_of_lt I _ hh)
  simp only [Software.binaryExact, Rat.cast_sub] at he
  refine ⟨z, hz, he, ?_⟩
  have herr := Reconstruction.round_difference hr hrho hL heta hx hy he
  have h := abs_add_le ((z : ℝ)-((x : ℝ)-(y : ℝ))) ((x : ℝ)-(y : ℝ))
  rw [sub_add_cancel] at h
  have hm := mul_le_mul_of_nonneg_right hrho hL
  nlinarith

/-- One bounded affine FMA, with finite output and local IEEE error derived. -/
theorem affine_step {u v w : I.Word} {a b c : ℚ} {K J L : ℝ}
    (hu : value? I u = some a) (hv : value? I v = some b) (hw : value? I w = some c)
    (hL : 0 ≤ L) (ha : |(a : ℝ)| ≤ 1) (hb : |(b : ℝ)| ≤ K*L)
    (hc : |(c : ℝ)| ≤ J*L)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hbudget : (K+J)*I.format.unitRoundoff+I.format.unitRoundoff^2/2 ≤ 1)
    (hlim : (K+J)*L < I.format.overflowThreshold) :
    ∃ z : ℚ, value? I (fma I u v w) = some z ∧
      Reconstruction.RoundError I.format.unitRoundoff I.format.minSubnormal
        ((a : ℝ)*(b : ℝ)+(c : ℝ)) (z : ℝ) ∧ |(z : ℝ)| ≤ (K+J+1)*L := by
  have hr := I.format.unitRoundoff_pos.le
  have hb0 : 0 ≤ K*L := (abs_nonneg _).trans hb
  have hex : |(a : ℝ)*(b : ℝ)+(c : ℝ)| ≤ (K+J)*L := by
    have h := abs_add_le ((a : ℝ)*(b : ℝ)) (c : ℝ)
    rw [abs_mul] at h
    have hh := mul_le_mul ha hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hh : |((a*b+c : ℚ) : ℝ)| < I.format.overflowThreshold := by
    simp only [Rat.cast_add, Rat.cast_mul]; exact hex.trans_lt hlim
  obtain ⟨z, hz, he⟩ := fma_exists_error I hu hv hw (no_overflow_of_lt I _ hh)
  simp only [Rat.cast_add, Rat.cast_mul] at he
  refine ⟨z, hz, he, ?_⟩
  have h := abs_add_le ((z : ℝ)-((a : ℝ)*(b : ℝ)+(c : ℝ))) ((a : ℝ)*(b : ℝ)+(c : ℝ))
  rw [sub_add_cancel] at h
  have hm := mul_le_mul_of_nonneg_left hex hr
  have hbud := mul_le_mul_of_nonneg_right hbudget hL
  nlinarith

/-- The face reconstruction schedule is finite and has component error 23ρL
    even if the upstream normal/reciprocal computation was inaccurate. -/
theorem face_trace {a b c x u v : I.Word} {A B C X U V : ℚ} {L : ℝ}
    (ha : value? I a = some A) (hb : value? I b = some B)
    (hc : value? I c = some C) (hx : value? I x = some X)
    (hu : value? I u = some U) (hv : value? I v = some V)
    (hL : 0 ≤ L) (hA : |(A : ℝ)| ≤ L) (hB : |(B : ℝ)| ≤ L)
    (hC : |(C : ℝ)| ≤ L) (hX : |(X : ℝ)| ≤ L)
    (hu0 : 0 ≤ U) (hu1 : U ≤ 1) (hv0 : 0 ≤ V) (hv1 : V ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ∃ r : ℚ, value? I (fma I v (sub I c a) (fma I u (sub I b a) (sub I a x))) = some r ∧
      |(r : ℝ)-((A : ℝ)+(U : ℝ)*((B : ℝ)-(A : ℝ))+
        (V : ℝ)*((C : ℝ)-(A : ℝ))-(X : ℝ))| ≤ 23*I.format.unitRoundoff*L := by
  have hr := I.format.unitRoundoff_pos.le
  have hsub : 3*L < I.format.overflowThreshold := by linarith
  have hU0 : (0 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hu0
  have hU1 : (U : ℝ) ≤ 1 := by exact_mod_cast hu1
  have hV0 : (0 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hv0
  have hV1 : (V : ℝ) ≤ 1 := by exact_mod_cast hv1
  have hU : |(U : ℝ)| ≤ 1 := by rwa [abs_of_nonneg hU0]
  have hV : |(V : ℝ)| ≤ 1 := by rwa [abs_of_nonneg hV0]
  obtain ⟨e, he, heErr, heB⟩ := sub_coordinates I hb ha hL hB hA hrho heta hsub
  obtain ⟨f, hf, hfErr, hfB⟩ := sub_coordinates I hc ha hL hC hA hrho heta hsub
  obtain ⟨ax, hax, haxErr, haxB⟩ := sub_coordinates I ha hx hL hA hX hrho heta hsub
  have hr2 := mul_self_le_mul_self hr hrho
  obtain ⟨w, hw, hwErr, hwB⟩ := affine_step I hu he hax hL hU heB haxB heta
    (by nlinarith) (by linarith)
  obtain ⟨r, hrr, hrErr, _⟩ := affine_step I hv hf hw hL hV hfB hwB heta
    (by nlinarith) (by linarith)
  refine ⟨r, hrr, ?_⟩
  have he0 : 0 ≤ I.format.minSubnormal := by unfold Format.minSubnormal; positivity
  exact Reconstruction.face_scalar_error hr hrho he0 hL heta hA hB hC hX hU0 hU1 hV0 hV1
    heErr hfErr haxErr (by simpa [add_comm] using hwErr) (by simpa [add_comm] using hrErr)

lemma neg_value {a : I.Word} {x : ℚ} (ha : value? I a = some x) :
    value? I (neg I a) = some (-x) := by
  unfold value? at ha ⊢
  unfold neg
  rw [Software.negate_toRat?, ha]
  rfl

/-- Complete scalar crossing reconstruction, including the rounded subtraction
    of the chosen point on the segment. -/
theorem crossing_trace {a b c p₀ p₁ s u v : I.Word} {A B C P₀ P₁ S U V : ℚ} {L : ℝ}
    (ha : value? I a = some A) (hb : value? I b = some B)
    (hc : value? I c = some C) (hp0 : value? I p₀ = some P₀) (hp1 : value? I p₁ = some P₁)
    (hs : value? I s = some S) (hu : value? I u = some U) (hv : value? I v = some V)
    (hL : 0 ≤ L) (hA : |(A : ℝ)| ≤ L) (hB : |(B : ℝ)| ≤ L)
    (hC : |(C : ℝ)| ≤ L) (hP0 : |(P₀ : ℝ)| ≤ L) (hP1 : |(P₁ : ℝ)| ≤ L)
    (hs0 : 0 ≤ S) (hs1 : S ≤ 1) (hu0 : 0 ≤ U) (hu1 : U ≤ 1) (hv0 : 0 ≤ V) (hv1 : V ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ∃ r : ℚ, value? I (fma I v (sub I c a) (fma I u (sub I b a)
      (fma I (neg I s) (sub I p₁ p₀) (sub I a p₀)))) = some r ∧
      |(r : ℝ)-((A : ℝ)+(U : ℝ)*((B : ℝ)-(A : ℝ))+
        (V : ℝ)*((C : ℝ)-(A : ℝ))-((1-(S : ℝ))*(P₀ : ℝ)+(S : ℝ)*(P₁ : ℝ)))|
        ≤ 23*I.format.unitRoundoff*L := by
  have hr := I.format.unitRoundoff_pos.le
  have hsub : 3*L < I.format.overflowThreshold := by linarith
  have hS0 : (0 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hs0
  have hS1 : (S : ℝ) ≤ 1 := by exact_mod_cast hs1
  have hU0 : (0 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hu0
  have hU1 : (U : ℝ) ≤ 1 := by exact_mod_cast hu1
  have hV0 : (0 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hv0
  have hV1 : (V : ℝ) ≤ 1 := by exact_mod_cast hv1
  have hS : |((-S : ℚ) : ℝ)| ≤ 1 := by simpa [abs_of_nonneg hS0] using hS1
  have hU : |(U : ℝ)| ≤ 1 := by rwa [abs_of_nonneg hU0]
  have hV : |(V : ℝ)| ≤ 1 := by rwa [abs_of_nonneg hV0]
  obtain ⟨e, he, heErr, heB⟩ := sub_coordinates I hb ha hL hB hA hrho heta hsub
  obtain ⟨f, hf, hfErr, hfB⟩ := sub_coordinates I hc ha hL hC hA hrho heta hsub
  obtain ⟨p, hp, hpErr, hpB⟩ := sub_coordinates I hp1 hp0 hL hP1 hP0 hrho heta hsub
  obtain ⟨ap, hap, hapErr, hapB⟩ := sub_coordinates I ha hp0 hL hA hP0 hrho heta hsub
  have hr2 := mul_self_le_mul_self hr hrho
  obtain ⟨ax, hax, haxErr, haxB⟩ := affine_step I (neg_value I hs) hp hap hL hS hpB hapB heta
    (by nlinarith) (by linarith)
  obtain ⟨w, hw, hwErr, hwB⟩ := affine_step I hu he hax hL hU heB haxB heta
    (by nlinarith) (by linarith)
  obtain ⟨r, hrr, hrErr, _⟩ := affine_step I hv hf hw hL hV hfB hwB heta
    (by nlinarith) (by linarith)
  refine ⟨r, hrr, ?_⟩
  exact Reconstruction.crossing_scalar_error hr hrho hL heta hA hB hC hP0 hP1
    hS0 hS1 hU0 hU1 hV0 hV1 heErr hfErr hpErr hapErr
    (by simpa [Rat.cast_neg, sub_eq_add_neg, add_comm] using haxErr)
    (by simpa [add_comm] using hwErr) (by simpa [add_comm] using hrErr)

theorem binary_step (op : BinaryOp) {a b : I.Word} {x y : ℚ} {K L : ℝ}
    (ha : value? I a = some x) (hb : value? I b = some y) (hL : 0 ≤ L)
    (hex : |(Software.binaryExact op x y : ℝ)| ≤ K*L)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hbudget : K*I.format.unitRoundoff+I.format.unitRoundoff^2/2 ≤ 1)
    (hlim : K*L < I.format.overflowThreshold) :
    ∃ z : ℚ, value? I (Software.binary I op .nearestEven a b).value = some z ∧
      Reconstruction.RoundError I.format.unitRoundoff I.format.minSubnormal
        (Software.binaryExact op x y : ℝ) (z : ℝ) ∧ |(z : ℝ)| ≤ (K+1)*L := by
  obtain ⟨z, hz, he⟩ := binary_exists_error I op ha hb
    (no_overflow_of_lt I _ (hex.trans_lt hlim))
  refine ⟨z, hz, he, ?_⟩
  have h := abs_add_le ((z : ℝ)-(Software.binaryExact op x y : ℝ)) (Software.binaryExact op x y : ℝ)
  rw [sub_add_cancel] at h
  have hm := mul_le_mul_of_nonneg_left hex I.format.unitRoundoff_pos.le
  have hbud := mul_le_mul_of_nonneg_right hbudget hL
  nlinarith

/-- Segment/segment interior reconstruction, independent of parameter-solve accuracy. -/
theorem segment_trace {p₀ p₁ q₀ q₁ s t : I.Word} {P₀ P₁ Q₀ Q₁ S T : ℚ} {L : ℝ}
    (hp0 : value? I p₀ = some P₀) (hp1 : value? I p₁ = some P₁)
    (hq0 : value? I q₀ = some Q₀) (hq1 : value? I q₁ = some Q₁)
    (hs : value? I s = some S) (ht : value? I t = some T)
    (hL : 0 ≤ L) (hP0 : |(P₀ : ℝ)| ≤ L) (hP1 : |(P₁ : ℝ)| ≤ L)
    (hQ0 : |(Q₀ : ℝ)| ≤ L) (hQ1 : |(Q₁ : ℝ)| ≤ L)
    (hs0 : 0 ≤ S) (hs1 : S ≤ 1) (ht0 : 0 ≤ T) (ht1 : T ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ∃ r : ℚ, value? I (fma I (neg I s) (sub I p₁ p₀)
      (fma I t (sub I q₁ q₀) (sub I q₀ p₀))) = some r ∧
      |(r : ℝ)-(((1-(T : ℝ))*(Q₀ : ℝ)+(T : ℝ)*(Q₁ : ℝ))-
        ((1-(S : ℝ))*(P₀ : ℝ)+(S : ℝ)*(P₁ : ℝ)))| ≤ 15*I.format.unitRoundoff*L := by
  have hr := I.format.unitRoundoff_pos.le
  have hsub : 3*L < I.format.overflowThreshold := by linarith
  have hS0 : (0 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hs0
  have hS1 : (S : ℝ) ≤ 1 := by exact_mod_cast hs1
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht0
  have hT1 : (T : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hS : |((-S : ℚ) : ℝ)| ≤ 1 := by simpa [abs_of_nonneg hS0] using hS1
  have hT : |(T : ℝ)| ≤ 1 := by rwa [abs_of_nonneg hT0]
  obtain ⟨p, hp, hpErr, hpB⟩ := sub_coordinates I hp1 hp0 hL hP1 hP0 hrho heta hsub
  obtain ⟨q, hq, hqErr, hqB⟩ := sub_coordinates I hq1 hq0 hL hQ1 hQ0 hrho heta hsub
  obtain ⟨ap, hap, hapErr, hapB⟩ := sub_coordinates I hq0 hp0 hL hQ0 hP0 hrho heta hsub
  have hr2 := mul_self_le_mul_self hr hrho
  obtain ⟨w, hw, hwErr, hwB⟩ := affine_step I ht hq hap hL hT hqB hapB heta
    (by nlinarith) (by linarith)
  obtain ⟨r, hrr, hrErr, _⟩ := affine_step I (neg_value I hs) hp hw hL hS hpB hwB heta
    (by nlinarith) (by linarith)
  refine ⟨r, hrr, ?_⟩
  exact Reconstruction.segment_scalar_error hr hrho hL heta hP0 hP1 hQ0 hQ1
    hS0 hS1 hT0 hT1 hpErr hqErr hapErr
    (by simpa [add_comm] using hwErr)
    (by simpa [Rat.cast_neg, sub_eq_add_neg, add_comm] using hrErr)
theorem segment_end1_trace {p₀ p₁ q₀ q₁ t : I.Word} {P₀ P₁ Q₀ Q₁ T : ℚ} {L : ℝ}
    (hp0 : value? I p₀ = some P₀) (hp1 : value? I p₁ = some P₁)
    (hq0 : value? I q₀ = some Q₀) (hq1 : value? I q₁ = some Q₁)
    (ht : value? I t = some T)
    (hL : 0 ≤ L) (hP0 : |(P₀ : ℝ)| ≤ L) (hP1 : |(P₁ : ℝ)| ≤ L)
    (hQ0 : |(Q₀ : ℝ)| ≤ L) (hQ1 : |(Q₁ : ℝ)| ≤ L)
    (ht0 : 0 ≤ T) (ht1 : T ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ∃ r : ℚ, value? I (fma I t (sub I q₁ q₀) (sub I (sub I q₀ p₀) (sub I p₁ p₀))) = some r ∧
      |(r : ℝ)-(((1-(T : ℝ))*(Q₀ : ℝ)+(T : ℝ)*(Q₁ : ℝ))-
        (P₁ : ℝ))| ≤ 15*I.format.unitRoundoff*L := by
  have hr := I.format.unitRoundoff_pos.le
  have hsub : 3*L < I.format.overflowThreshold := by linarith
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht0
  have hT1 : (T : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hT : |(T : ℝ)| ≤ 1 := by rwa [abs_of_nonneg hT0]
  obtain ⟨p, hp, hpErr, hpB⟩ := sub_coordinates I hp1 hp0 hL hP1 hP0 hrho heta hsub
  obtain ⟨q, hq, hqErr, hqB⟩ := sub_coordinates I hq1 hq0 hL hQ1 hQ0 hrho heta hsub
  obtain ⟨ap, hap, hapErr, hapB⟩ := sub_coordinates I hq0 hp0 hL hQ0 hP0 hrho heta hsub
  have hr2 := mul_self_le_mul_self hr hrho
  have hdiff : |(Software.binaryExact .sub ap p : ℝ)| ≤ 6*L := by
    simp only [Software.binaryExact, Rat.cast_sub]
    have hh := Reconstruction.difference_abs hapB hpB
    nlinarith
  obtain ⟨w, hw, hwErr, hwB⟩ := binary_step I .sub hap hp hL hdiff heta
    (by nlinarith) (by linarith)
  change value? I (sub I (sub I q₀ p₀) (sub I p₁ p₀)) = some w at hw
  simp only [Software.binaryExact, Rat.cast_sub] at hwErr
  obtain ⟨r, hrr, hrErr, _⟩ := affine_step I ht hq hw hL hT hqB hwB heta
    (by nlinarith) (by linarith)
  refine ⟨r, hrr, ?_⟩
  exact Reconstruction.segment_endpoint_scalar_error hr hrho hL heta hP0 hP1 hQ0 hQ1
    hT0 hT1 hpErr hqErr hapErr hwErr (by simpa [add_comm] using hrErr)


theorem point_segment_trace {x q₀ q₁ t : I.Word} {X Q₀ Q₁ T : ℚ} {L : ℝ}
    (hx : value? I x = some X) (hq0 : value? I q₀ = some Q₀) (hq1 : value? I q₁ = some Q₁)
    (ht : value? I t = some T) (hL : 0 ≤ L) (hX : |(X : ℝ)| ≤ L)
    (hQ0 : |(Q₀ : ℝ)| ≤ L) (hQ1 : |(Q₁ : ℝ)| ≤ L) (ht0 : 0 ≤ T) (ht1 : T ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ∃ r : ℚ, value? I (fma I t (sub I q₁ q₀) (sub I q₀ x)) = some r ∧
      |(r : ℝ)-(((1-(T : ℝ))*(Q₀ : ℝ)+(T : ℝ)*(Q₁ : ℝ))-(X : ℝ))|
        ≤ 15*I.format.unitRoundoff*L := by
  have hr := I.format.unitRoundoff_pos.le
  have he : 0 ≤ I.format.minSubnormal := by unfold Format.minSubnormal; positivity
  have hsub : 3*L < I.format.overflowThreshold := by linarith
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht0
  have hT1 : (T : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hT : |(T : ℝ)| ≤ 1 := by rwa [abs_of_nonneg hT0]
  obtain ⟨q, hq, hqErr, hqB⟩ := sub_coordinates I hq1 hq0 hL hQ1 hQ0 hrho heta hsub
  obtain ⟨ap, hap, hapErr, hapB⟩ := sub_coordinates I hq0 hx hL hQ0 hX hrho heta hsub
  have hr2 := mul_self_le_mul_self hr hrho
  obtain ⟨r, hrr, hrErr, _⟩ := affine_step I ht hq hap hL hT hqB hapB heta
    (by nlinarith) (by linarith)
  refine ⟨r, hrr, ?_⟩
  have hh := Reconstruction.segment_scalar_error (p₀ := (X : ℝ)) (p₁ := (X : ℝ))
    (q₀ := (Q₀ : ℝ)) (q₁ := (Q₁ : ℝ)) (P := 0) (s := 0) (R := (r : ℝ))
    hr hrho hL heta hX hX hQ0 hQ1 (by norm_num) (by norm_num) hT0 hT1
    (by simpa using Reconstruction.round_self (a := (0 : ℝ)) hr he)
    hqErr hapErr (by simpa [add_comm] using hrErr)
    (by simpa using Reconstruction.round_self (a := (r : ℝ)) hr he)
  simpa using hh

end DistanceAccuracy.ReconstructionIEEE

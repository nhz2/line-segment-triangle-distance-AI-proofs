import DistanceAccuracy.CandidateLower

namespace DistanceAccuracy.BCLower
open FP.IEEE FP.IEEE.Interchange
open IEEEAlgorithm IEEEBridge OperationBounds ReconstructionIEEE
variable (I : Interchange) [I.Valid]

/-- The BC fallback uses two already rounded differences. This follows that
exact evaluation order, including its additional subtraction and addition. -/
theorem bc_trace {a b c x t : I.Word} {A B C X T : ℚ} {L : ℝ}
    (ha : value? I a = some A) (hb : value? I b = some B)
    (hc : value? I c = some C) (hx : value? I x = some X)
    (ht : value? I t = some T)
    (hL : 0 ≤ L) (hA : |(A : ℝ)| ≤ L) (hB : |(B : ℝ)| ≤ L)
    (hC : |(C : ℝ)| ≤ L) (hX : |(X : ℝ)| ≤ L)
    (ht0 : 0 ≤ T) (ht1 : T ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ∃ r : ℚ, value? I (fma I t (sub I (sub I c a) (sub I b a))
      (add I (sub I a x) (sub I b a))) = some r ∧
      |(r : ℝ)-(((1-(T : ℝ))*(B : ℝ)+(T : ℝ)*(C : ℝ))-(X : ℝ))| ≤ 21*I.format.unitRoundoff*L := by
  have hr := I.format.unitRoundoff_pos.le
  have hr2 := mul_self_le_mul_self hr hrho
  have hsub : 3*L < I.format.overflowThreshold := by linarith
  obtain ⟨e, he, heErr, heB⟩ := sub_coordinates I hb ha hL hB hA hrho heta hsub
  obtain ⟨f, hf, hfErr, hfB⟩ := sub_coordinates I hc ha hL hC hA hrho heta hsub
  obtain ⟨ax, hax, haxErr, haxB⟩ := sub_coordinates I ha hx hL hA hX hrho heta hsub
  have heta' : I.format.minSubnormal ≤ I.format.unitRoundoff^2*(3*L) := by
    nlinarith [mul_nonneg (sq_nonneg I.format.unitRoundoff) hL]
  obtain ⟨e2, he2, he2Err, he2B⟩ := sub_coordinates I hf he (by positivity) hfB heB hrho heta' (by linarith)
  have hsum : |(ax : ℝ)+(e : ℝ)| ≤ 6*L := (abs_add_le _ _).trans (by linarith)
  have hsafe : |(Software.binaryExact .add ax e : ℝ)| < I.format.overflowThreshold := by
    simp only [Software.binaryExact, Rat.cast_add]; linarith
  obtain ⟨bx, hbx, hbxErr⟩ := binary_exists_error I .add hax he (no_overflow_of_lt I _ hsafe)
  simp only [Software.binaryExact, Rat.cast_add] at hbxErr
  have hbxB : |(bx : ℝ)| ≤ 7*L := by
    have h := abs_add_le ((bx : ℝ)-((ax : ℝ)+(e : ℝ))) ((ax : ℝ)+(e : ℝ))
    rw [sub_add_cancel] at h
    have hm := mul_le_mul_of_nonneg_left hsum hr
    have hbudget : 6*I.format.unitRoundoff+I.format.unitRoundoff^2/2 ≤ 1 := by nlinarith
    have hbud := mul_le_mul_of_nonneg_right hbudget hL
    nlinarith
  have ht0r : (0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht0
  have ht1r : (T : ℝ) ≤ 1 := by exact_mod_cast ht1
  have htB : |(T : ℝ)| ≤ 1 := by rwa [abs_of_nonneg ht0r]
  have he2B' : |(e2 : ℝ)| ≤ 9*L := by nlinarith [he2B]
  obtain ⟨r, hrr, hrErr, _⟩ := affine_step I ht he2 hbx hL htB he2B' hbxB heta
    (by nlinarith) (by linarith)
  refine ⟨r, hrr, ?_⟩
  exact Reconstruction.bc_scalar_error hr hrho hL heta hA hB hC hX ht0r ht1r
    heErr hfErr haxErr he2Err hbxErr (by simpa [add_comm] using hrErr)

theorem edge_trace {a b x t : I.Word} {A B X T : ℚ} {L : ℝ}
    (ha : value? I a = some A) (hb : value? I b = some B)
    (hx : value? I x = some X) (ht : value? I t = some T)
    (hL : 0 ≤ L) (hA : |(A : ℝ)| ≤ L) (hB : |(B : ℝ)| ≤ L) (hX : |(X : ℝ)| ≤ L)
    (ht0 : 0 ≤ T) (ht1 : T ≤ 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hlim : 32*L < I.format.overflowThreshold) :
    ∃ r : ℚ, value? I (fma I t (sub I b a) (sub I a x)) = some r ∧
      |(r : ℝ)-(((1-(T : ℝ))*(A : ℝ)+(T : ℝ)*(B : ℝ))-(X : ℝ))| ≤ 9*I.format.unitRoundoff*L := by
  have hr := I.format.unitRoundoff_pos.le
  have hr2 := mul_self_le_mul_self hr hrho
  obtain ⟨e, he, heErr, heB⟩ := sub_coordinates I hb ha hL hB hA hrho heta (by linarith)
  obtain ⟨ax, hax, haxErr, haxB⟩ := sub_coordinates I ha hx hL hA hX hrho heta (by linarith)
  have ht0r : (0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht0
  have ht1r : (T : ℝ) ≤ 1 := by exact_mod_cast ht1
  have htB : |(T : ℝ)| ≤ 1 := by rwa [abs_of_nonneg ht0r]
  obtain ⟨r, hrr, hrErr, _⟩ := affine_step I ht he hax hL htB heB haxB heta
    (by nlinarith) (by linarith)
  have heE := Reconstruction.round_difference hr hrho hL heta hB hA heErr
  have heAX := Reconstruction.round_difference hr hrho hL heta hA hX haxErr
  have heinput := Reconstruction.affine_input_error hr hL htB heAX heE
  have hi : |((ax : ℝ)+(T : ℝ)*(e : ℝ))-
      (((1-(T : ℝ))*(A : ℝ)+(T : ℝ)*(B : ℝ))-(X : ℝ))| ≤ 6*I.format.unitRoundoff*L := by
    convert heinput using 1 <;> congr 1 <;> ring
  have hY := Reconstruction.interval_abs hL hA hB ht0r ht1r
  have h := Reconstruction.round_propagate (C := 6) (K := 2) hr hL heta (by linarith) hi
    (Reconstruction.difference_abs hY hX) (by simpa [add_comm] using hrErr)
  refine ⟨r, hrr, ?_⟩
  norm_num at h ⊢
  exact h

open DistanceAccuracy.Geometry CandidateLower LowerBound

theorem bc_safe {S T : Set E3} {a b c x : Vec3 I} (raw : I.Word)
    {A B C X : Fin 3 → ℚ} {d L : ℝ}
    (ha : ∀ k, value? I (a k) = some (A k)) (hb : ∀ k, value? I (b k) = some (B k))
    (hc : ∀ k, value? I (c k) = some (C k)) (hx : ∀ k, value? I (x k) = some (X k))
    (hS : Convex ℝ S) (hT : Convex ℝ T) (hXm : ratVec X ∈ S)
    (hBm : ratVec B ∈ T) (hCm : ratVec C ∈ T)
    (hd : ∀ p ∈ S, ∀ q ∈ T, d ≤ ‖q-p‖)
    (hL : 0 ≤ L) (hA : ∀ k, |(A k : ℝ)| ≤ L) (hB : ∀ k, |(B k : ℝ)| ≤ L)
    (hC : ∀ k, |(C k : ℝ)| ≤ L) (hX : ∀ k, |(X k : ℝ)| ≤ L)
    (hone : value? I (one I) = some 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024) (heta1 : I.format.minSubnormal ≤ 1)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hunder : 2*Real.sqrt I.format.minSubnormal ≤ I.format.unitRoundoff*L)
    (hlin : 32*L < I.format.overflowThreshold)
    (hquad : 512*L*L+4 < I.format.overflowThreshold) :
    let r := fma3 I (clamp01nan I raw) (vsub I (vsub I c a) (vsub I b a))
      (vadd I (vsub I a x) (vsub I b a))
    Safe I d (120*I.format.unitRoundoff*L) (dot3 I r r) := by
  obtain ⟨U, hu, hu0, hu1⟩ := clamp01nan_bounded I hone raw
  choose rv hrv herr using fun k => bc_trace I (ha k) (hb k) (hc k) (hx k)
    hu hL (hA k) (hB k) (hC k) (hX k) hu0 hu1 hrho heta hlin
  have hu0r : (0 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hu0
  have hu1r : (U : ℝ) ≤ 1 := by exact_mod_cast hu1
  have hr := I.format.unitRoundoff_pos.le
  dsimp only
  apply from_reconstruction I hS hT hXm hXm hXm hBm hCm hBm hd hL hX hX hX hB hC hB
    (u := 0) (v := 0) (s := (U : ℝ)) (t := 0)
    (by norm_num) (by norm_num) (by norm_num) (by nlinarith)
    hu0r hu1r (by norm_num) (by nlinarith) hrv _ hrho heta1 hunder hquad
  intro k
  have hid : (bary (ratVec B) (ratVec C) (ratVec B) (U : ℝ) 0 -
      bary (ratVec X) (ratVec X) (ratVec X) 0 0) k =
      ((1-(U : ℝ))*(B k : ℝ)+(U : ℝ)*(C k : ℝ))-(X k : ℝ) := by
    simp [bary, ratVec]; ring
  rw [hid]
  have h := herr k
  nlinarith [mul_nonneg hr hL]

theorem edge_safe {S T : Set E3} {a b x : Vec3 I} (raw : I.Word)
    {A B X : Fin 3 → ℚ} {d L : ℝ}
    (ha : ∀ k, value? I (a k) = some (A k)) (hb : ∀ k, value? I (b k) = some (B k))
    (hx : ∀ k, value? I (x k) = some (X k))
    (hS : Convex ℝ S) (hT : Convex ℝ T) (hXm : ratVec X ∈ S)
    (hAm : ratVec A ∈ T) (hBm : ratVec B ∈ T)
    (hd : ∀ p ∈ S, ∀ q ∈ T, d ≤ ‖q-p‖)
    (hL : 0 ≤ L) (hA : ∀ k, |(A k : ℝ)| ≤ L) (hB : ∀ k, |(B k : ℝ)| ≤ L)
    (hX : ∀ k, |(X k : ℝ)| ≤ L)
    (hone : value? I (one I) = some 1)
    (hrho : I.format.unitRoundoff ≤ 1/1024) (heta1 : I.format.minSubnormal ≤ 1)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff^2*L)
    (hunder : 2*Real.sqrt I.format.minSubnormal ≤ I.format.unitRoundoff*L)
    (hlin : 32*L < I.format.overflowThreshold)
    (hquad : 512*L*L+4 < I.format.overflowThreshold) :
    let r := fma3 I (clamp01nan I raw) (vsub I b a) (vsub I a x)
    Safe I d (120*I.format.unitRoundoff*L) (dot3 I r r) := by
  obtain ⟨U, hu, hu0, hu1⟩ := clamp01nan_bounded I hone raw
  choose rv hrv herr using fun k => edge_trace I (ha k) (hb k) (hx k)
    hu hL (hA k) (hB k) (hX k) hu0 hu1 hrho heta hlin
  have hu0r : (0 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hu0
  have hu1r : (U : ℝ) ≤ 1 := by exact_mod_cast hu1
  have hr := I.format.unitRoundoff_pos.le
  dsimp only
  apply from_reconstruction I hS hT hXm hXm hXm hAm hBm hAm hd hL hX hX hX hA hB hA
    (u := 0) (v := 0) (s := (U : ℝ)) (t := 0)
    (by norm_num) (by norm_num) (by norm_num) (by nlinarith)
    hu0r hu1r (by norm_num) (by nlinarith) hrv _ hrho heta1 hunder hquad
  intro k
  have hid : (bary (ratVec A) (ratVec B) (ratVec A) (U : ℝ) 0 -
      bary (ratVec X) (ratVec X) (ratVec X) 0 0) k =
      ((1-(U : ℝ))*(A k : ℝ)+(U : ℝ)*(B k : ℝ))-(X k : ℝ) := by
    simp [bary, ratVec]; ring
  rw [hid]
  have h := herr k
  nlinarith [mul_nonneg hr hL]

theorem pointTriangle_safe {S T : Set E3} {x : Vec3 I} (y : Triangle I) {A B C X : Fin 3 → ℚ} {d L : ℝ}
    (ha : ∀ k, value? I (y 0 k) = some (A k)) (hb : ∀ k, value? I (y 1 k) = some (B k))
    (hc : ∀ k, value? I (y 2 k) = some (C k)) (hx : ∀ k, value? I (x k) = some (X k))
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
    Safe I d (120*I.format.unitRoundoff*L) (pointTriangle I x y).q := by
  let e := vsub I (y 1) (y 0)
  let f := vsub I (y 2) (y 0)
  let ax := vsub I (y 0) x
  let e2 := vsub I f e
  let bx := vadd I ax e
  let raw1 := div I (neg I (dot3 I f ax)) (dot3 I f f)
  let raw2 := div I (neg I (dot3 I bx e2)) (dot3 I e2 e2)
  have hac := edge_safe I raw1 ha hc hx hS hT hXm hAm hCm hd hL hA hC hX
    hone hrho heta1 heta hunder hlin hquad
  have hbc := bc_safe I raw2 ha hb hc hx hS hT hXm hBm hCm hd hL hA hB hC hX
    hone hrho heta1 heta hunder hlin hquad
  have hf := CandidateLower.face_safe I (n := cross3 I e f) ha hb hc hx hS hT hXm hAm hBm hCm
    hd hL hA hB hC hX hone hrep hrho heta1 hetarho heta hunder hlin hquad
  unfold pointTriangle
  exact choose_safe I (choose_safe I hac hbc) hf

end DistanceAccuracy.BCLower

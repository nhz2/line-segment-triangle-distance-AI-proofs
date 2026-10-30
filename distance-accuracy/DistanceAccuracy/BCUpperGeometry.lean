import DistanceAccuracy.FaceCoordinates
import DistanceAccuracy.BCLower

namespace DistanceAccuracy.BCUpperGeometry
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds ReconstructionIEEE Determinant

/-- Intermediate BC edge and offset are accurate rounded differences, even
though their simple finiteness bounds used in the lower proof were loose. -/
theorem bc_scalar_data (I : Interchange) [I.Valid]
    {a b c x : I.Word} {A B C X : ℚ} {L : ℝ}
    (ha : value? I a = some A) (hb : value? I b = some B)
    (hc : value? I c = some C) (hx : value? I x = some X)
    (hL : 0 ≤ L) (hA : |(A : ℝ)| ≤ L) (hB : |(B : ℝ)| ≤ L)
    (hC : |(C : ℝ)| ≤ L) (hX : |(X : ℝ)| ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1 / 1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff ^ 2 * L)
    (hlim : 32 * L < I.format.overflowThreshold) :
    ∃ e2 bx : ℚ,
      value? I (sub I (sub I c a) (sub I b a)) = some e2 ∧
      value? I (add I (sub I a x) (sub I b a)) = some bx ∧
      |(e2 : ℝ) - ((C : ℝ) - (B : ℝ))| ≤ 9 * I.format.unitRoundoff * L ∧
      |(bx : ℝ) - ((B : ℝ) - (X : ℝ))| ≤ 9 * I.format.unitRoundoff * L := by
  have hr := I.format.unitRoundoff_pos.le
  have hsub : 3 * L < I.format.overflowThreshold := by linarith only [hlim, hL]
  obtain ⟨e, he, heErr, heB⟩ := sub_coordinates I hb ha hL hB hA hrho heta hsub
  obtain ⟨f, hf, hfErr, hfB⟩ := sub_coordinates I hc ha hL hC hA hrho heta hsub
  obtain ⟨ax, hax, haxErr, haxB⟩ := sub_coordinates I ha hx hL hA hX hrho heta hsub
  have heta' : I.format.minSubnormal ≤ I.format.unitRoundoff ^ 2 * (3 * L) := by
    nlinarith only [heta, mul_nonneg (sq_nonneg I.format.unitRoundoff) hL]
  obtain ⟨e2, he2, he2Err, _⟩ := sub_coordinates I hf he (by positivity) hfB heB hrho heta' (by linarith only [hlim, hL])
  have hsum : |(ax : ℝ) + (e : ℝ)| ≤ 6 * L := (abs_add_le _ _).trans (by linarith only [haxB, heB])
  obtain ⟨bx, hbx, hbxErr⟩ := binary_exists_error I .add hax he
    (no_overflow_of_lt I _ (by simp only [Software.binaryExact, Rat.cast_add]; linarith only [hsum, hlim, hL]))
  simp only [Software.binaryExact, Rat.cast_add] at hbxErr
  have hE := Reconstruction.round_difference hr hrho hL heta hB hA heErr
  have hF := Reconstruction.round_difference hr hrho hL heta hC hA hfErr
  have hAX := Reconstruction.round_difference hr hrho hL heta hA hX haxErr
  have he2in : |((f : ℝ) - (e : ℝ)) - ((C : ℝ) - (B : ℝ))| ≤ 6 * I.format.unitRoundoff * L := by
    have h := Reconstruction.affine_input_error hr hL (t := -1) (by norm_num) hF hE
    convert h using 1 <;> congr 1 <;> ring
  have hbxin : |((ax : ℝ) + (e : ℝ)) - ((B : ℝ) - (X : ℝ))| ≤ 6 * I.format.unitRoundoff * L := by
    have h := Reconstruction.affine_input_error hr hL (t := 1) (by norm_num) hAX hE
    convert h using 1 <;> congr 1 <;> ring
  have he2bound := Reconstruction.round_propagate (C := 6) (K := 2) hr hL heta
    (by linarith only [hrho]) he2in (Reconstruction.difference_abs hC hB) he2Err
  have hbxbound := Reconstruction.round_propagate (C := 6) (K := 2) hr hL heta
    (by linarith only [hrho]) hbxin (Reconstruction.difference_abs hB hX) hbxErr
  refine ⟨e2, bx, he2, hbx, ?_, ?_⟩
  · norm_num at he2bound ⊢; exact he2bound
  · norm_num at hbxbound ⊢; exact hbxbound

/-- Sharp upper geometry for the actual BC fallback, including the shared
sum BX+E2. All norms fit the same global diameter 3.5L. -/
theorem bc_geometry (I : Interchange) [I.Valid]
    {a b c x : Vec3 I} {A B C X : Fin 3 → ℚ} {L : ℝ}
    (ha : ∀ i, value? I (a i) = some (A i)) (hb : ∀ i, value? I (b i) = some (B i))
    (hc : ∀ i, value? I (c i) = some (C i)) (hx : ∀ i, value? I (x i) = some (X i))
    (hL : 0 ≤ L) (hA : ∀ i, |(A i : ℝ)| ≤ L) (hB : ∀ i, |(B i : ℝ)| ≤ L)
    (hC : ∀ i, |(C i : ℝ)| ≤ L) (hX : ∀ i, |(X i : ℝ)| ≤ L)
    (hrho : I.format.unitRoundoff ≤ 1 / 1024)
    (heta : I.format.minSubnormal ≤ I.format.unitRoundoff ^ 2 * L)
    (hlim : 32 * L < I.format.overflowThreshold) :
    ∃ e2 bx : Fin 3 → ℚ,
      (∀ i, value? I (vsub I (vsub I c a) (vsub I b a) i) = some (e2 i)) ∧
      (∀ i, value? I (vadd I (vsub I a x) (vsub I b a) i) = some (bx i)) ∧
      (∀ i, |(e2 i : ℝ)| ≤ ((7 / 2) * L) / Real.sqrt 3) ∧
      (∀ i, |(bx i : ℝ)| ≤ ((7 / 2) * L) / Real.sqrt 3) ∧
      ‖realVec e2‖ ≤ (7 / 2) * L ∧ ‖realVec bx‖ ≤ (7 / 2) * L ∧
      ‖realVec bx + realVec e2‖ ≤ (7 / 2) * L ∧
      (∀ i, |(e2 i : ℝ) - ((C i : ℝ) - (B i : ℝ))| ≤ 9 * I.format.unitRoundoff * L) ∧
      (∀ i, |(bx i : ℝ) - ((B i : ℝ) - (X i : ℝ))| ≤ 9 * I.format.unitRoundoff * L) := by
  choose e2 bx he2 hbx he2err hbxerr using fun i => bc_scalar_data I
    (ha i) (hb i) (hc i) (hx i) hL (hA i) (hB i) (hC i) (hX i) hrho heta hlim
  have hr := I.format.unitRoundoff_pos.le
  let K := (2 + 18 * I.format.unitRoundoff) * L
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have he2C : ∀ i, |(e2 i : ℝ)| ≤ K := by
    intro i
    have h := abs_add_le ((e2 i : ℝ) - ((C i : ℝ) - (B i : ℝ))) ((C i : ℝ) - (B i : ℝ))
    rw [sub_add_cancel] at h
    have hd := Reconstruction.difference_abs (hC i) (hB i)
    dsimp [K]
    nlinarith only [h, hd, he2err i, mul_nonneg hr hL]
  have hbxC : ∀ i, |(bx i : ℝ)| ≤ K := by
    intro i
    have h := abs_add_le ((bx i : ℝ) - ((B i : ℝ) - (X i : ℝ))) ((B i : ℝ) - (X i : ℝ))
    rw [sub_add_cancel] at h
    have hd := Reconstruction.difference_abs (hB i) (hX i)
    dsimp [K]
    nlinarith only [h, hd, hbxerr i, mul_nonneg hr hL]
  have hsumC : ∀ i, |(realVec bx + realVec e2) i| ≤ K := by
    intro i
    have h1 := abs_add_le ((bx i : ℝ) - ((B i : ℝ) - (X i : ℝ)))
      ((e2 i : ℝ) - ((C i : ℝ) - (B i : ℝ)))
    have h2 := abs_add_le (((bx i : ℝ) - ((B i : ℝ) - (X i : ℝ))) +
      ((e2 i : ℝ) - ((C i : ℝ) - (B i : ℝ)))) ((C i : ℝ) - (X i : ℝ))
    have heq : ((bx i : ℝ) - ((B i : ℝ) - (X i : ℝ))) +
      ((e2 i : ℝ) - ((C i : ℝ) - (B i : ℝ))) + ((C i : ℝ) - (X i : ℝ)) =
      (realVec bx + realVec e2) i := by simp [realVec]; ring
    rw [heq] at h2
    simp only [PiLp.add_apply] at h2
    have hd := Reconstruction.difference_abs (hC i) (hX i)
    dsimp [K]
    nlinarith only [h1, h2, hd, he2err i, hbxerr i]
  have hs : Real.sqrt (3 : ℝ) ≤ 26 / 15 := by apply Real.sqrt_le_iff.mpr; norm_num
  have hKupper : K ≤ (1009 / 500 : ℝ) * L := by
    dsimp [K]
    nlinarith only [mul_le_mul_of_nonneg_right hrho hL, hL]
  have hbudget : Real.sqrt 3 * K ≤ (7 / 2) * L := by
    have h := mul_le_mul hs hKupper hK (by norm_num : (0 : ℝ) ≤ 26 / 15)
    nlinarith only [h, hL]
  have hKdiv : K ≤ ((7 / 2) * L) / Real.sqrt 3 := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).2
    nlinarith only [hbudget]
  exact ⟨e2, bx, he2, hbx, fun i => (he2C i).trans hKdiv, fun i => (hbxC i).trans hKdiv,
    (GeometryCoverage.coordinate_norm_bound hK he2C).trans hbudget,
    (GeometryCoverage.coordinate_norm_bound hK hbxC).trans hbudget,
    (GeometryCoverage.coordinate_norm_bound hK hsumC).trans hbudget, he2err, hbxerr⟩

end DistanceAccuracy.BCUpperGeometry

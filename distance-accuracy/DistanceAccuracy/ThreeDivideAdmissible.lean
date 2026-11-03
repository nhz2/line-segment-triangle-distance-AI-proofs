import DistanceAccuracy.ThreeDivideWord
namespace DistanceAccuracy.ProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds Determinant
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2048
theorem second_line_or_endpoint (fmt : Format)
    {Pw Qw Rw : Vec3 fmt.interchange} {p q r : Fin 3 → ℚ}
    {tw : fmt.interchange.Word} {t : ℚ} {D L : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hP : ∀ i, value? fmt.interchange (Pw i) = some (p i))
    (hQ : ∀ i, value? fmt.interchange (Qw i) = some (q i))
    (hR : ∀ i, value? fmt.interchange (Rw i) = some (r i))
    (ht : value? fmt.interchange tw = some t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hA : fourthRoot fmt.leastSubnormal < ‖realVec p‖) (hDL : D ≤ 9*L)
    (hpD : ‖realVec p‖ ≤ D) (hqD : ‖realVec q‖ ≤ D) (hrD : ‖realVec r‖ ≤ D)
    (hkD : ‖realVec r+(t : ℝ)•realVec q‖ ≤ D)
    (hpC : ∀ i, |(p i : ℝ)| ≤ D/Real.sqrt 3)
    (hqC : ∀ i, |(q i : ℝ)| ≤ D/Real.sqrt 3)
    (hrC : ∀ i, |(r i : ℝ)| ≤ D/Real.sqrt 3) :
    ∃ s : ℚ, value? fmt.interchange (clamp01nan fmt.interchange
      (div fmt.interchange (fma fmt.interchange tw (dot3 fmt.interchange Pw Qw) (dot3 fmt.interchange Pw Rw))
        (dot3 fmt.interchange Pw Pw))) = some s ∧ 0 ≤ s ∧ s ≤ 1 ∧
      let u := LineReduction.parameter (-realVec p) (realVec r) (realVec q) (t:ℝ)
      ((s:ℝ)=0 ∧ u≤0) ∨ ((s:ℝ)=1 ∧ 1≤u) ∨
        |(s:ℝ)-u| * ‖realVec p‖ ≤ (419/50)*fmt.interchange.format.unitRoundoff*D+
          (32*fmt.interchange.format.minSubnormal*(1+‖realVec p‖^2))/‖realVec p‖ := by
  obtain ⟨a, b, d, ha, hb, hd, hap, haErr, haSharp, hbSharp, hdSharp, hbMag, hdMag⟩ :=
    three_dots_admissible fmt hP hQ hR hL hadm hA hDL hpD hqD hrD hpC hqC hrC
  obtain ⟨s, hs, hs0, hs1⟩ := clamp01nan_bounded fmt.interchange hone
    (div fmt.interchange (fma fmt.interchange tw (dot3 fmt.interchange Pw Qw) (dot3 fmt.interchange Pw Rw))
      (dot3 fmt.interchange Pw Pw))
  have hD : 0 ≤ D := (norm_nonneg _).trans hpD
  have hne : realVec p ≠ 0 := by
    have hh := lt_of_le_of_lt (fourthRoot_nonneg _) hA
    exact norm_pos_iff.mp hh
  have hρmax : fmt.interchange.format.unitRoundoff ≤ 1/16777216 := by
    have hh := fmt.rho_le
    cases fmt <;> norm_num [Format.interchange, fp32, fp64, FP.IEEE.binary32,
      FP.IEEE.binary64, FP.IEEE.Format.unitRoundoff]
  have hlim1 : (1:ℝ) < fmt.interchange.format.overflowThreshold := by
    have hh := fmt.quadratic_range hL hadm
    nlinarith [sq_nonneg L]
  have ht0r : (0:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht0
  have ht1r : (t : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hn := numerator_range fmt hL hadm hD hDL
    (show |(t : ℝ)| ≤ 1 by rwa [abs_of_nonneg ht0r]) hbMag hdMag
  refine ⟨s, hs, hs0, hs1, ?_⟩
  exact second_word_line_or_endpoint fmt.interchange hone ha hb hd ht hs hap hne hD hpD hkD
    ht0r ht1r (by exact_mod_cast hs0) (by exact_mod_cast hs1) hρmax hlim1 hn
    haErr haSharp hbSharp hdSharp

/-- The actual third solve uses the shared P·Q word, including its original
operand order, and the exactly negated Q·R word. -/
theorem third_solve_admissible (fmt : Format)
    {Pw Qw Rw : Vec3 fmt.interchange} {p q r : Fin 3 → ℚ}
    {sw : fmt.interchange.Word} {s : ℚ} {D L : ℝ}
    (hone : value? fmt.interchange (one fmt.interchange) = some 1)
    (hP : ∀ i, value? fmt.interchange (Pw i) = some (p i))
    (hQ : ∀ i, value? fmt.interchange (Qw i) = some (q i))
    (hR : ∀ i, value? fmt.interchange (Rw i) = some (r i))
    (hs : value? fmt.interchange sw = some s) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hL : 0 ≤ L) (hadm : L < fourthRoot fmt.interchange.format.maxFinite/4)
    (hA : fourthRoot fmt.leastSubnormal < ‖realVec q‖) (hDL : D ≤ 9*L)
    (hpD : ‖realVec p‖ ≤ D) (hqD : ‖realVec q‖ ≤ D) (hrD : ‖realVec r‖ ≤ D)
    (hkD : ‖realVec r-(s:ℝ)•realVec p‖ ≤ D)
    (hpC : ∀ i, |(p i:ℝ)| ≤ D/Real.sqrt 3)
    (hqC : ∀ i, |(q i:ℝ)| ≤ D/Real.sqrt 3)
    (hrC : ∀ i, |(r i:ℝ)| ≤ D/Real.sqrt 3) :
    ∃ t : ℚ, value? fmt.interchange (clamp01nan fmt.interchange
      (div fmt.interchange (fma fmt.interchange sw (dot3 fmt.interchange Pw Qw)
        (neg fmt.interchange (dot3 fmt.interchange Qw Rw))) (dot3 fmt.interchange Qw Qw))) = some t ∧
      0 ≤ t ∧ t ≤ 1 ∧ ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      ‖realVec r+(t:ℝ)•realVec q-(s:ℝ)•realVec p‖^2 ≤
        ‖realVec r+v•realVec q-(s:ℝ)•realVec p‖^2+
        ((419/50)*fmt.interchange.format.unitRoundoff*D)^2+
        64*fmt.interchange.format.minSubnormal*(1+‖realVec q‖^2) := by
  let I := fmt.interchange
  obtain ⟨a,b,e,ha,hb,he,hap,haErr,haSharp,hbSharp,heSharp,hbMag,heMag⟩ :=
    three_dots_admissible_reversed fmt hQ hP hR hL hadm hA hDL hqD hpD hrD hqC hpC hrC
  obtain ⟨t, ht, ht0, ht1⟩ := clamp01nan_bounded I hone
    (div I (fma I sw (dot3 I Pw Qw) (neg I (dot3 I Qw Rw))) (dot3 I Qw Qw))
  have hD : 0 ≤ D := (norm_nonneg _).trans hpD
  have hne : realVec q ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (fourthRoot_nonneg _) hA)
  have hρmax : I.format.unitRoundoff ≤ 1/16777216 := by
    cases fmt <;> norm_num [I, Format.interchange, fp32, fp64, FP.IEEE.binary32,
      FP.IEEE.binary64, FP.IEEE.Format.unitRoundoff]
  have hlim1 : (1:ℝ) < I.format.overflowThreshold := by
    have hh := fmt.quadratic_range hL hadm
    nlinarith [sq_nonneg L]
  have hs0r : (0:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs0
  have hs1r : (s:ℝ) ≤ 1 := by exact_mod_cast hs1
  have hn := numerator_range fmt hL hadm hD hDL
    (show |(s:ℝ)| ≤ 1 by rwa [abs_of_nonneg hs0r]) hbMag
    (show |((-e:ℚ):ℝ)| ≤ 2*D^2+2*I.format.minSubnormal by simpa using heMag)
  refine ⟨t,ht,ht0,ht1,?_⟩
  intro v hv0 hv1
  have hproj := second_word_projection_loss I (P := -realVec q) (Q := -realVec p) (R := realVec r)
    hone ha hb (neg_value I he) hs ht hap (neg_ne_zero.mpr hne) hD
    (by simpa using hqD) (by simpa [sub_eq_add_neg] using hkD)
    hs0r hs1r (by exact_mod_cast ht0) (by exact_mod_cast ht1) hv0 hv1 hρmax hlim1 hn
    (by simpa using haErr) (by simpa using haSharp) (by simpa using hbSharp)
    (by simpa only [Rat.cast_neg, inner_neg_left, neg_sub_neg, abs_sub_comm, norm_neg] using heSharp)
  have hid (w : ℝ) : (realVec r+(s:ℝ)•(-realVec p))+w•(-(-realVec q)) =
      realVec r+w•realVec q-(s:ℝ)•realVec p := by module
  simpa only [hid, norm_neg] using hproj

end DistanceAccuracy.ProjectionRounding

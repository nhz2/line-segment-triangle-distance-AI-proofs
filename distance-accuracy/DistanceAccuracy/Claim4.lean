import DistanceAccuracy.Formats

/-!
# Claim 4, conditional on implementation-level certificates

This file proves the final two-sided inequality from the lower-bound certificate
and one of the upper candidate estimates in `proof.md`. It intentionally does
NOT assert that the Julia routine supplies those certificates. That connection
requires formalizing its IEEE arithmetic, reconstruction, and geometric coverage.
See `README.md` for the exact remaining obligations.
-/
namespace DistanceAccuracy

/-- Which estimate supplies the upper-bound witness? -/
inductive CandidateCase where
  | pointFace | segmentSegment | separated | crossingFace | crossingEdge
  deriving DecidableEq

noncomputable def candidateCoefficient : CandidateCase → ℝ
  | .pointFace => P 0
  | .segmentSegment => F 3.02 + 3.53
  | .separated => 8.04 + max (P 0) (F 3.02 + 3.53)
  | .crossingFace => V 8.34 + 4.03
  | .crossingEdge => F (V 8.34 + 5.02) + 3.53

lemma candidate_coefficient_lt (k : CandidateCase) : candidateCoefficient k < 35.8 := by
  cases k with
  | pointFace => have := point_coefficient; dsimp [candidateCoefficient]; linarith
  | segmentSegment => have := line_coefficient; dsimp [candidateCoefficient]; linarith
  | separated => have := separated_coefficient; dsimp [candidateCoefficient]; linarith
  | crossingFace => exact direct_crossing_coefficient
  | crossingEdge => exact crossing_coefficient

/-- `reconstructed` represents the norm of the separation reconstructed exactly
from the returned weights; `residual` represents the norm of the returned r.
The fields are obligations, not automatically true facts about Julia. -/
structure LowerCertificate (rho L d computed : ℝ) where
  reconstructed : ℝ
  residual : ℝ
  feasibility : d ≤ reconstructed + 2 * Real.sqrt 3 * rho * L
  reconstruction : reconstructed ≤ residual + 16 * rho * L
  normEvaluation : residual ≤ computed + 9 * rho * L

lemma lower_from_certificate {rho L d computed : ℝ} (hrho : 0 ≤ rho) (hL : 0 ≤ L)
    (cert : LowerCertificate rho L d computed) : d - computed ≤ 32 * rho * L := by
  have hscale : 0 ≤ rho * L := mul_nonneg hrho hL
  have hc := mul_le_mul_of_nonneg_right sqrt_three_le hscale
  have hf := cert.feasibility
  have hr := cert.reconstruction
  have hn := cert.normEvaluation
  nlinarith

/-- An available candidate and an upper estimate for that candidate.
The selection inequality expresses the routine's minimum selection. -/
structure UpperCertificate (rho D h d computed : ℝ) where
  kind : CandidateCase
  candidate : ℝ
  selected : computed ≤ candidate
  estimate : candidate - d ≤ candidateCoefficient kind * rho * D + 8 * h

lemma upper_from_certificate {rho D h d computed : ℝ}
    (hrho : 0 ≤ rho) (hD : 0 ≤ D)
    (cert : UpperCertificate rho D h d computed) :
    computed - d ≤ 35.8 * rho * D + 8 * h := by
  have hc := mul_le_mul_of_nonneg_right (le_of_lt (candidate_coefficient_lt cert.kind))
    (mul_nonneg hrho hD)
  have hs := cert.selected
  have he := cert.estimate
  nlinarith

/-- The small-coordinate case needs only nonnegativity and magnitude bounds. -/
lemma small_case {computed d H : ℝ} (hc : 0 ≤ computed) (hd : 0 ≤ d)
    (hcH : computed ≤ H) (hdH : d ≤ H) : |computed - d| ≤ H := by
  apply abs_le.mpr
  constructor <;> linarith

/-- The real-square-root version of claim 4 with eps = 2rho.

The two certificate arguments are the formalization boundary. They are not
proved for `dist_sqr_r_s_t` by this development. -/
theorem claim4_of_certificates {rho L H h d computed : ℝ}
    (hrho : 0 ≤ rho) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hbudget : 8 * h ≤ H)
    (lower : LowerCertificate rho L d computed)
    (upper : UpperCertificate rho (2 * Real.sqrt 3 * L) h d computed) :
    |computed - d| ≤ 64 * (2 * rho) * L + H := by
  have hl := lower_from_certificate hrho hL lower
  have hu := upper_from_certificate hrho (by positivity) upper
  have hc := mul_le_mul_of_nonneg_right (le_of_lt exact_root_coefficient)
    (mul_nonneg hrho hL)
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hrho hL]

/-- The format-independent underflow budget proved in `Constants.lean`
discharges the h-budget in the previous theorem. -/
theorem claim4_large_of_certificates {rho L H h d computed : ℝ}
    (hrho : 0 ≤ rho) (hrhomax : rho ≤ 1 / 2 ^ 24)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hh : 0 ≤ h)
    (hfourth : h ^ 4 = 2 * rho * H ^ 4)
    (lower : LowerCertificate rho L d computed)
    (upper : UpperCertificate rho (2 * Real.sqrt 3 * L) h d computed) :
    |computed - d| ≤ 64 * (2 * rho) * L + H := by
  have hb := underflow_budget hrhomax hh hH hfourth
  exact claim4_of_certificates hrho hL hH (by linarith) lower upper

/-- Full small/large regime assembly, still conditional on the certificates
in the large regime and the magnitude estimates in the small regime. -/
theorem claim4_conditional {rho L H h d computed : ℝ}
    (hrho : 0 ≤ rho) (hrhomax : rho ≤ 1 / 2 ^ 24)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hh : 0 ≤ h)
    (hfourth : h ^ 4 = 2 * rho * H ^ 4)
    (hc : 0 ≤ computed) (hd : 0 ≤ d)
    (hsmall : L ≤ H / 64 → computed ≤ H ∧ d ≤ H)
    (hlarge : H / 64 < L →
      Nonempty (LowerCertificate rho L d computed) ∧
      Nonempty (UpperCertificate rho (2 * Real.sqrt 3 * L) h d computed)) :
    |computed - d| ≤ 64 * (2 * rho) * L + H := by
  by_cases hs : L ≤ H / 64
  · obtain ⟨hcH, hdH⟩ := hsmall hs
    have hb := small_case hc hd hcH hdH
    nlinarith [mul_nonneg hrho hL]
  · obtain ⟨⟨lower⟩, ⟨upper⟩⟩ := hlarge (lt_of_not_ge hs)
    exact claim4_large_of_certificates hrho hrhomax hL hH hh hfourth lower upper

/-- Allow an actually rounded sqrt, with the 1.01rhoD rounding allowance.
The absolute allowance from the small-coordinate case is handled separately. -/
theorem claim4_rounded_of_certificates {rho L H h d computed rounded : ℝ}
    (hrho : 0 ≤ rho) (hL : 0 ≤ L) (hH : 0 ≤ H) (hbudget : 8 * h ≤ H)
    (lower : LowerCertificate rho L d computed)
    (upper : UpperCertificate rho (2 * Real.sqrt 3 * L) h d computed)
    (hround : |rounded - computed| ≤ 1.01 * rho * (2 * Real.sqrt 3 * L)) :
    |rounded - d| ≤ 64 * (2 * rho) * L + H := by
  have hl := lower_from_certificate hrho hL lower
  have hu := upper_from_certificate hrho (by positivity) upper
  have hc := mul_le_mul_of_nonneg_right (le_of_lt rounded_root_coefficient)
    (mul_nonneg hrho hL)
  have hc3 := mul_le_mul_of_nonneg_right sqrt_three_le (mul_nonneg hrho hL)
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp hround
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hrho hL]

/-- Claim 4 written with the actual real square root and the exact binary32/64
format constants. This still requires the implementation certificates. -/
theorem format_claim4_conditional (f : Format) {L d q : ℝ}
    (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hsmall : L ≤ fourthRoot f.leastNormal / 64 →
      Real.sqrt q ≤ fourthRoot f.leastNormal ∧ d ≤ fourthRoot f.leastNormal)
    (hlarge : fourthRoot f.leastNormal / 64 < L →
      Nonempty (LowerCertificate f.rho L d (Real.sqrt q)) ∧
      Nonempty (UpperCertificate f.rho (2 * Real.sqrt 3 * L)
        (fourthRoot f.leastSubnormal) d (Real.sqrt q))) :
    |Real.sqrt q - d| ≤ 64 * (2 * f.rho) * L + fourthRoot f.leastNormal :=
  claim4_conditional f.rho_nonneg f.rho_le hL (fourthRoot_nonneg _)
    (fourthRoot_nonneg _) f.fourth_root_relation (Real.sqrt_nonneg _) hd hsmall hlarge

end DistanceAccuracy

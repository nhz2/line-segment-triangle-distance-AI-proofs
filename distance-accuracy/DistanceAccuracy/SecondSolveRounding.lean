import DistanceAccuracy.ProjectionRounding
import DistanceAccuracy.FaceProjectionRounding

namespace DistanceAccuracy.ProjectionRounding

lemma second_relative_envelope {rho : ℝ} (hr : 0 ≤ rho)
    (hrmax : rho ≤ 1 / 16777216) :
    2 * (2161 / 1000) * (1 + rho) ^ 3 + 1 +
      ((2042 / 1000) * (1 + rho) ^ 2 + 1) / (1 - rho) ≤ (419 / 50 : ℝ) := by
  have hr2 : rho ^ 2 ≤ rho / 16777216 := by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hrmax)]
  have hU2 : (1 + rho) ^ 2 ≤ (1000001 / 1000000 : ℝ) := by nlinarith only [hrmax, hr2]
  have hU3 : (1 + rho) ^ 3 ≤ (1000001 / 1000000 : ℝ) := by
    nlinarith only [hrmax, hr2, mul_le_mul_of_nonneg_left hr2 hr]
  have hden : 0 < 1 - rho := by linarith only [hrmax]
  have hdiv : ((2042 / 1000) * (1 + rho) ^ 2 + 1) / (1 - rho) ≤ (3043 / 1000 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith only [hU2, hrmax]
  nlinarith only [hU3, hdiv]

/-- Relative error of the actual FMA numerator, after splitting the two input
 dot errors into their relative and absolute parts. -/
lemma second_numerator_relative {b d db dd t delta rho S : ℝ}
    (hr : 0 ≤ rho) (hS : 0 ≤ S) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hd : |delta| ≤ rho) (hB : |t * b + d| ≤ S)
    (hdb : |db| ≤ (2161 / 1000) * rho * S * (1 + rho) ^ 2)
    (hdd : |dd| ≤ (2161 / 1000) * rho * S * (1 + rho) ^ 2) :
    |(t * db + dd) * (1 + delta) + (t * b + d) * delta| ≤
      rho * S * (2 * (2161 / 1000) * (1 + rho) ^ 3 + 1) := by
  have hd1 : |1 + delta| ≤ 1 + rho := by
    have h := abs_add_le (1 : ℝ) delta
    norm_num only [abs_one] at h
    linarith only [h, hd]
  have htd : |t * db + dd| ≤ 2 * ((2161 / 1000) * rho * S * (1 + rho) ^ 2) := by
    have h := abs_add_le (t * db) dd
    rw [abs_mul, abs_of_nonneg ht] at h
    have hm := mul_le_mul_of_nonneg_left hdb ht
    have hb := mul_le_mul_of_nonneg_right ht1 (show 0 ≤ (2161 / 1000) * rho * S * (1 + rho) ^ 2 by positivity)
    nlinarith only [h, hm, hb, hdd]
  have h1 := mul_le_mul htd hd1 (abs_nonneg _) (show 0 ≤ 2 * ((2161 / 1000) * rho * S * (1 + rho) ^ 2) by positivity)
  have h2 := mul_le_mul hB hd (abs_nonneg _) hS
  have h3 := abs_add_le ((t * db + dd) * (1 + delta)) ((t * b + d) * delta)
  rw [abs_mul, abs_mul] at h3
  nlinarith only [h1, h2, h3]

lemma second_numerator_absolute {db dd t delta zeta rho eta : ℝ}
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1 / 16) (heta : 0 ≤ eta)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hd : |delta| ≤ rho)
    (hdb : |db| ≤ 2 * eta) (hdd : |dd| ≤ 2 * eta) (hz : |zeta| ≤ eta / 2) :
    |(t * db + dd) * (1 + delta) + zeta| ≤ 5 * eta := by
  have hd1 : |1 + delta| ≤ 1 + rho := by
    have h := abs_add_le (1 : ℝ) delta
    norm_num only [abs_one] at h
    linarith only [h, hd]
  have htd : |t * db + dd| ≤ 4 * eta := by
    have h := abs_add_le (t * db) dd
    rw [abs_mul, abs_of_nonneg ht] at h
    have hm := mul_le_mul_of_nonneg_left hdb ht
    nlinarith only [h, hm, hdd, mul_le_mul_of_nonneg_right ht1 heta]
  have h1 := mul_le_mul htd hd1 (abs_nonneg _) (show 0 ≤ 4 * eta by positivity)
  have h2 := abs_add_le ((t * db + dd) * (1 + delta)) zeta
  rw [abs_mul] at h2
  nlinarith only [h1, h2, hz, heta, mul_le_mul_of_nonneg_right hrmax heta]

lemma second_numerator_split {b d bh dh dbR dbA ddR ddA t delta zeta n : ℝ}
    (hb : bh - b = dbR + dbA) (hd : dh - d = ddR + ddA)
    (hn : n = (t * bh + dh) * (1 + delta) + zeta) :
    n - (t * b + d) =
      ((t * dbR + ddR) * (1 + delta) + (t * b + d) * delta) +
      ((t * dbA + ddA) * (1 + delta) + zeta) := by
  have hb' : bh = b + dbR + dbA := by linarith only [hb]
  have hd' : dh = d + ddR + ddA := by linarith only [hd]
  rw [hn, hb', hd']
  ring

end DistanceAccuracy.ProjectionRounding

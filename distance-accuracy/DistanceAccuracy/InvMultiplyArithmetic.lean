import DistanceAccuracy.WordFaceFinite
import DistanceAccuracy.ReprojectProjection
namespace DistanceAccuracy.InvProjectionRounding
open FP.IEEE FP.IEEE.Interchange IEEEAlgorithm IEEEBridge OperationBounds Determinant ProjectionRounding
set_option maxHeartbeats 2000000

def rdiv (I : Interchange) [I.Valid] (n a : I.Word) : I.Word :=
  IEEEAlgorithm.mul I n (IEEEAlgorithm.div I (one I) a)

/-- Two rounded operations, with reciprocal and product safety proved explicitly. -/
theorem inv_fma_representation (I : Interchange) [I.Valid]
    {aw bw dw tw : I.Word} {a b d t s : ℚ} {T : ℝ}
    (hone : value? I (one I) = some 1)
    (ha : value? I aw = some a) (hb : value? I bw = some b)
    (hd : value? I dw = some d) (ht : value? I tw = some t)
    (hs : value? I (clamp01nan I (rdiv I (fma I tw bw dw) aw)) = some s)
    (hap : 0 < a) (htabs : |(t:ℝ)| ≤ 1)
    (hrmax : I.format.unitRoundoff ≤ 1/16777216)
    (hnumlim : |(t:ℝ)*(b:ℝ)+(d:ℝ)| < I.format.overflowThreshold)
    (hnormal : I.format.minNormal ≤ 1/(a:ℝ))
    (hrecip : 1/(a:ℝ) < I.format.overflowThreshold)
    (hT : 0 < T) (hbT : |(b:ℝ)| ≤ (a:ℝ)*T) (hdT : |(d:ℝ)| ≤ (a:ℝ)*T)
    (heta : I.format.minSubnormal ≤ (a:ℝ)*T)
    (hlim : 8*T < I.format.overflowThreshold) :
    ∃ n : ℚ, ∃ delta zeta dq zq : ℝ,
      (n:ℝ) = ((t:ℝ)*(b:ℝ)+(d:ℝ))*(1+delta)+zeta ∧
      |delta| ≤ I.format.unitRoundoff ∧ |zeta| ≤ I.format.minSubnormal/2 ∧
      |dq| ≤ (2001/1000)*I.format.unitRoundoff ∧ |zq| ≤ I.format.minSubnormal/2 ∧
      (s:ℝ) = max 0 (min 1 (((n:ℝ)/(a:ℝ))*(1+dq)+zq)) := by
  have hr := I.format.unitRoundoff_pos.le
  have har : (0:ℝ) < (a:ℝ) := by exact_mod_cast hap
  obtain ⟨n,hn,hne⟩ := fma_exists_error I ht hb hd
    (no_overflow_of_lt I _ (by simpa only [Rat.cast_add,Rat.cast_mul] using hnumlim))
  obtain ⟨delta,zeta,hnum,hdelta,hzeta⟩ := word_fma_decomposition I ht hb hd hn
  obtain ⟨ir,di,hir,hie,hdi⟩ := reciprocal_relative I hone ha hap hnormal hrecip
  have hi0 : 0 ≤ (ir:ℝ) := by
    rw [hie]; have hh := (abs_le.mp hdi).1
    exact mul_nonneg (by positivity) (by linarith)
  have hi2 : (ir:ℝ) ≤ 2/(a:ℝ) := by
    rw [hie]; have := (abs_le.mp hdi).2
    apply (le_div_iff₀ har).2
    field_simp
    linarith
  have hn2 : |(t:ℝ)*(b:ℝ)+(d:ℝ)| ≤ 2*((a:ℝ)*T) := by
    have h := abs_add_le ((t:ℝ)*(b:ℝ)) (d:ℝ)
    rw [abs_mul] at h
    have hm := mul_le_mul htabs hbT (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    linarith
  have hn3 : |(n:ℝ)| ≤ 3*((a:ℝ)*T) := by
    simp only [Rat.cast_add,Rat.cast_mul] at hne
    have hm := rounded_magnitude hr hn2 hne
    have h := mul_le_mul_of_nonneg_right hrmax (show 0 ≤ (a:ℝ)*T by positivity)
    nlinarith
  have hnprod : |(n:ℝ)*(ir:ℝ)| ≤ 6*T := by
    rw [abs_mul,abs_of_nonneg hi0]
    have h := mul_le_mul hn3 hi2 hi0 (show 0 ≤ 3*((a:ℝ)*T) by positivity)
    have he : 3*((a:ℝ)*T)*(2/(a:ℝ))=6*T := by field_simp; ring
    linarith
  obtain ⟨p,hp,_⟩ := binary_exists_error I .mul hn hir
    (no_overflow_of_lt I _ (by simpa only [Software.binaryExact,Rat.cast_mul] using
      (show |(n:ℝ)*(ir:ℝ)| < I.format.overflowThreshold by linarith)))
  obtain ⟨dm,zm,hpm,hdm,hzm⟩ := word_multiplication_decomposition I hn hir hp
  let dq := di+dm+di*dm
  have hdq : |dq| ≤ (2001/1000)*I.format.unitRoundoff := by
    have h := abs_add_le (di+dm) (di*dm)
    have hsum := abs_add_le di dm
    rw [abs_mul] at h
    have hm := mul_le_mul hdi hdm (abs_nonneg _) hr
    have hr2 := mul_le_mul_of_nonneg_left hrmax hr
    dsimp [dq]; nlinarith
  have hpform : (p:ℝ) = ((n:ℝ)/(a:ℝ))*(1+dq)+zm := by
    rw [hpm,hie]; dsimp [dq]; ring
  have hc := clamp01nan_finite I hone hp
  change value? I (clamp01nan I (rdiv I (fma I tw bw dw) aw)) = _ at hc
  rw [hs] at hc
  have hsc : (s:ℝ)=max 0 (min 1 (p:ℝ)) := by exact_mod_cast Option.some.inj hc
  exact ⟨n,delta,zeta,dq,zm,hnum,hdelta,hzeta,hdq,hzm,by rw [hsc,hpform]⟩
end DistanceAccuracy.InvProjectionRounding

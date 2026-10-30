import DistanceAccuracy.RevisedConstants
import DistanceAccuracy.AccuracyAssembly

namespace DistanceAccuracy

lemma missed_root_coefficient : F (V 6+7.002)+3.55 < (36:ℝ) := by
  have hj : J 3.60 6 ≤ (15.494:ℝ) := by
    have hh : hypot (6+3.60) 7.02 ≤ (11.894:ℝ) := hypot_le (by norm_num) (by norm_num)
    dsimp [J]; linarith
  have hv : V 6 ≤ (17.094:ℝ) :=
    hypot_le_of_le (J_nonneg (by norm_num)) hj (by norm_num) (by norm_num)
  have hj' : J 3.17 (V 6+7.002) ≤ (31.326:ℝ) := by
    have hh : hypot (V 6+7.002+3.17) 7.02 ≤ (28.156:ℝ) :=
      hypot_le_of_le (by have := V_nonneg (6:ℝ); linarith)
        (show V 6+7.002+3.17 ≤ (27.266:ℝ) by linarith) (by norm_num) (by norm_num)
    dsimp [J]; linarith
  have hf : F (V 6+7.002) ≤ (32.428:ℝ) :=
    hypot_le_of_le (J_nonneg (by norm_num)) hj' (by norm_num) (by norm_num)
  linarith

lemma crossing_final_coefficient : F (V 8.4+5.022)+3.55 < (36:ℝ) := by
  have hb := revised_crossing_coefficient
  have he := F_add_le (z := V 8.4+5.02) (t := (0.002:ℝ))
    (by have := V_nonneg (8.4:ℝ); linarith) (by norm_num)
  have hid : V 8.4+5.022 = (V 8.4+5.02)+0.002 := by ring
  rw [← hid] at he
  linarith

lemma thin_final_coefficient : F 23+3.55 < (36:ℝ) := by
  have hb := revised_thin_coefficient
  have hm := F_mono (show (0:ℝ) ≤ 23 by norm_num) (show (23:ℝ) ≤ 3.02+16+4.02 by norm_num)
  linarith

/-- Scaling a one-sided Lipschitz envelope retains an additive absolute error. -/
lemma scaled_F_bound {S d b e : ℝ} (hS : 0 < S) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (he : 0 ≤ e) (hbound : d ≤ S*b+e) : S*F (d/S) ≤ S*F b+e := by
  have hn : d/S ≤ b+e/S := by
    apply (div_le_iff₀ hS).mpr
    rw [add_mul, div_mul_cancel₀ e (ne_of_gt hS), mul_comm b S]
    exact hbound
  have hm := F_mono (div_nonneg hd hS.le) hn
  have ha := F_add_le hb (div_nonneg he hS.le)
  have ht := mul_le_mul_of_nonneg_left (hm.trans ha) hS.le
  have hid : S*(e/S)=e := mul_div_cancel₀ e (ne_of_gt hS)
  nlinarith only [ht,hid]

lemma scaled_V_bound {S d b e : ℝ} (hS : 0 < S) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (he : 0 ≤ e) (hbound : d ≤ S*b+e) : S*V (d/S) ≤ S*V b+e := by
  have hn : d/S ≤ b+e/S := by
    apply (div_le_iff₀ hS).mpr
    rw [add_mul, div_mul_cancel₀ e (ne_of_gt hS), mul_comm b S]
    exact hbound
  have hm := V_mono (div_nonneg hd hS.le) hn
  have ha := V_add_le hb (div_nonneg he hS.le)
  have ht := mul_le_mul_of_nonneg_left (hm.trans ha) hS.le
  have hid : S*(e/S)=e := mul_div_cancel₀ e (ne_of_gt hS)
  nlinarith only [ht,hid]

lemma crossing_V_bound : V 8.4 ≤ (18.935:ℝ) := by
  have hj : J 3.60 8.4 ≤ (17.504:ℝ) := by
    have hh : hypot (8.4+3.60) 7.02 ≤ (13.904:ℝ) := hypot_le (by norm_num) (by norm_num)
    dsimp [J]; linarith
  exact hypot_le_of_le (J_nonneg (by norm_num)) hj (by norm_num) (by norm_num)

lemma endpoint_V_bound : V 6 ≤ (17.094:ℝ) := by
  have hj : J 3.60 6 ≤ (15.494:ℝ) := by
    have hh : hypot (6+3.60) 7.02 ≤ (11.894:ℝ) := hypot_le (by norm_num) (by norm_num)
    dsimp [J]; linarith
  exact hypot_le_of_le (J_nonneg (by norm_num)) hj (by norm_num) (by norm_num)

lemma crossing_boundary_coefficient : V 8.4+1.01 < (20.2:ℝ) := by linarith [crossing_V_bound]
lemma endpoint_boundary_coefficient : V 6+3.002 < (20.2:ℝ) := by linarith [endpoint_V_bound]
lemma crossing_face_coefficient : V 8.4+4.54 < (24:ℝ) := by linarith [crossing_V_bound]
lemma endpoint_face_coefficient : V 6+4.54 < (24:ℝ) := by linarith [endpoint_V_bound]
lemma crossing_edge_coefficient : F 24.2+3.55 < (36.4:ℝ) := by
  have hj : J 3.17 24.2 ≤ (31.427:ℝ) := by
    have hh : hypot (24.2+3.17) 7.02 ≤ (28.257:ℝ) := hypot_le (by norm_num) (by norm_num)
    dsimp [J]; linarith
  have hf : F 24.2 ≤ (32.526:ℝ) :=
    hypot_le_of_le (J_nonneg (by norm_num)) hj (by norm_num) (by norm_num)
  linarith

end DistanceAccuracy

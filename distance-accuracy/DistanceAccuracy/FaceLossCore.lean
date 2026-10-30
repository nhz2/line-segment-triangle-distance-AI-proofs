import DistanceAccuracy.FaceProjectionRounding
import DistanceAccuracy.ReducedProjection

namespace DistanceAccuracy.ProjectionRounding
open Determinant

/-- Composition of the face coefficient estimates into the physical squared
residual loss. The word-level wrapper derives the mixed coefficient bounds. -/
theorem face_squared_loss {E F R : E3} {D rho eta ah bh dh di dc dm dq zm zc zq u v ustar : ℝ}
    (hE : E ≠ 0) (hD : 0 < D) (hED : ‖E‖ ≤ D) (hFD : ‖F‖ ≤ D) (hRD : ‖R‖ ≤ D)
    (hr : 0 ≤ rho) (hrmax : rho ≤ 1 / 16777216) (heta : 0 ≤ eta)
    (hAh : 0 ≤ ah) (hAerr : |ah - ‖E‖ ^ 2| ≤ ‖E‖ ^ 2)
    (hA : |ah - ‖E‖ ^ 2| ≤ (2042 / 1000) * rho * (‖E‖ * D) * (1 + rho) ^ 2 + 2 * eta)
    (hB : |bh - inner ℝ E F| ≤ (2161 / 1000) * rho * (‖E‖ * D) * (1 + rho) ^ 2 + 2 * eta)
    (hDdot : |dh - inner ℝ E R| ≤ (2161 / 1000) * rho * (‖E‖ * D) * (1 + rho) ^ 2 + 2 * eta)
    (hdi : |di| ≤ rho) (hdc : |dc| ≤ rho) (hdm : |dm| ≤ rho) (hdq : |dq| ≤ rho)
    (hzm : |zm| ≤ eta / 2) (hzc : |zc| ≤ eta / 2) (hzq : |zq| ≤ eta / 2)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1)
    (hstar0 : 0 ≤ ustar) (hstar1 : ustar + v ≤ 1)
    (hKKT : let ae := ah / ((1 + di) * (1 + dq))
      let be := dh * (1 + dm) + v * bh * (1 + dc) - ae * ((zm - v * zc) * (1 + dq) + zq)
      0 ≤ (ae * u + be) * (ustar - u)) :
    ‖(R + v • F) + u • E‖ ^ 2 ≤ ‖(R + v • F) + ustar • E‖ ^ 2 +
      ((361 / 50) * rho * D) ^ 2 + 64 * eta * (1 + ‖E‖ ^ 2) := by
  have hnorm := norm_nonneg E
  have hS : 0 ≤ ‖E‖ * D := mul_nonneg hnorm hD.le
  obtain ⟨daR, daA, haSplit, hdaR, hdaA⟩ := split_mixed_error (by positivity) (by positivity) hA
  obtain ⟨dbR, dbA, hbSplit, hdbR, hdbA⟩ := split_mixed_error (by positivity) (by positivity) hB
  obtain ⟨ddR, ddA, hdSplit, hddR, hddA⟩ := split_mixed_error (by positivity) (by positivity) hDdot
  let ae := ah / ((1 + di) * (1 + dq))
  let be := dh * (1 + dm) + v * bh * (1 + dc) - ae * ((zm - v * zc) * (1 + dq) + zq)
  let er := ((‖E‖ ^ 2 + daR) / ((1 + di) * (1 + dq)) - ‖E‖ ^ 2) * u +
    ((inner ℝ E R + ddR) * (1 + dm) + v * (inner ℝ E F + dbR) * (1 + dc) -
      (inner ℝ E R + v * inner ℝ E F))
  let ea := (daA / ((1 + di) * (1 + dq))) * u + ddA * (1 + dm) + v * dbA * (1 + dc) -
    ae * ((zm - v * zc) * (1 + dq) + zq)
  have hsplit : (ae - ‖E‖ ^ 2) * u + (be - inner ℝ E (R + v • F)) = er + ea := by
    have h := face_gradient_split (u := u) (v := v) (di := di) (dc := dc) (dm := dm) (dq := dq)
      (zm := zm) (zc := zc) (zq := zq) haSplit hbSplit hdSplit
    simpa [ae, be, er, ea, inner_add_right, inner_smul_right] using h
  have hbS : |inner ℝ E F| ≤ ‖E‖ * D :=
    (abs_real_inner_le_norm E F).trans (mul_le_mul_of_nonneg_left hFD hnorm)
  have hdS : |inner ℝ E R| ≤ ‖E‖ * D :=
    (abs_real_inner_le_norm E R).trans (mul_le_mul_of_nonneg_left hRD hnorm)
  have haS : ‖E‖ ^ 2 ≤ ‖E‖ * D := by nlinarith
  have her : |er| ≤ ‖E‖ * ((361 / 50) * rho * D) := by
    have h := face_relative_gradient (sq_nonneg ‖E‖) haS hS hbS hdS hr hrmax
      (by norm_num) (le_refl _) (by norm_num) (le_refl _) hdaR hdbR hddR hdi hdc hdm hdq hu hv huv
    dsimp [er]
    convert h using 1 <;> ring
  obtain ⟨hprod, hinv, hfm, hfc, hfq⟩ := face_factor_bounds hr (by linarith) hdi hdq hdm hdc
  obtain ⟨hae0, hae4⟩ := face_effective_a_bound (sq_nonneg ‖E‖) hAh hAerr hprod hinv
  have hea : |ea| ≤ 32 * eta * (1 + ‖E‖ ^ 2) :=
    face_absolute_gradient (sq_nonneg ‖E‖) hae0 hae4 heta hinv hfm hfc hfq
      hdaA hdbA hddA hzm hzc hzq hu (by linarith) hv (by linarith)
  have hspan : |u - ustar| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hresult := ReducedProjection.projected_residual_sq_le (k := R + v • F) hE
    hKKT hsplit hspan (show 0 ≤ (361 / 50) * rho * D by positivity)
    (show 0 ≤ 32 * eta * (1 + ‖E‖ ^ 2) by positivity) her hea
  nlinarith only [hresult]

end DistanceAccuracy.ProjectionRounding

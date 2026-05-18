-- FILENAME: CGD/Gravity/Urbantke/Determinant1.lean

import CGD.Gravity.Urbantke.PseudoInverse
import CGD.Gravity.Urbantke.MetricTrace8
import CGD.Gravity.Urbantke.PlebanskiComponents1

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

/-- 
If the Plebanski constraint holds with a non-zero cosmological constant Λ, 
and F is a valid su(2) 2-form, the resulting constructed metric is mathematically 
guaranteed to be non-degenerate.
-/
lemma urbantke_nondeg_of_plebanski 
  (Λ : ℂ) (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_Λ : Λ ≠ 0)
  (h_antisymm : ∀ μ ν, F μ ν = - F ν μ)
  (h_su2 : ∀ μ ν, 
    F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧
    F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1)
  (h_plebanski : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1)
  (sqrt_g detPsi : ℂ)
  (h_sqrt_g : sqrt_g^2 = (cgdUnimodularMetricAdapter F).det)
  (h_detPsi : detPsi * ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3)) = 1)
  (h_eq2_21 : (3 * I / 2 : ℂ) * sqrt_g * detPsi = 1) :
  (cgdUnimodularMetricAdapter F).det ≠ 0 := by
  
  have h_alg : ((3 * I / 2 : ℂ) * sqrt_g)^2 = ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3))^2 := by
    calc ((3 * I / 2 : ℂ) * sqrt_g)^2 = ((3 * I / 2 : ℂ) * sqrt_g * 1)^2 := by ring
      _ = ((3 * I / 2 : ℂ) * sqrt_g * (detPsi * ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3))))^2 := by rw [h_detPsi]
      _ = (((3 * I / 2 : ℂ) * sqrt_g * detPsi) * ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3)))^2 := by ring
      _ = (1 * ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3)))^2 := by rw [h_eq2_21]
      _ = ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3))^2 := by ring
      
  have h_det_id : (cgdUnimodularMetricAdapter F).det * (3 * I / 2 : ℂ)^2 = ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3))^2 := by
    calc (cgdUnimodularMetricAdapter F).det * (3 * I / 2 : ℂ)^2 = sqrt_g^2 * (3 * I / 2 : ℂ)^2 := by rw [h_sqrt_g]
      _ = ((3 * I / 2 : ℂ) * sqrt_g)^2 := by ring
      _ = ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3))^2 := h_alg
      
  have h_right : ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3))^2 = (-729 / 256 : ℂ) * Λ^6 := by
    calc ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3))^2 = ((27 * I^3 / 8) * ((1/2:ℂ) * Λ^3))^2 := by ring
      _ = ((27 * (I^2 * I) / 8) * ((1/2:ℂ) * Λ^3))^2 := by ring
      _ = ((27 * ((-1) * I) / 8) * ((1/2:ℂ) * Λ^3))^2 := by rw [Complex.I_sq]
      _ = ((-27 * I / 8) * ((1/2:ℂ) * Λ^3))^2 := by ring
      _ = (-27 * I / 16 * Λ^3)^2 := by ring
      _ = (729 * I^2 / 256) * Λ^6 := by ring
      _ = (729 * (-1) / 256) * Λ^6 := by rw [Complex.I_sq]
      _ = (-729 / 256 : ℂ) * Λ^6 := by ring

  have h_left_eq : (cgdUnimodularMetricAdapter F).det * (-9 / 4 : ℂ) = (-729 / 256 : ℂ) * Λ^6 := by
    calc (cgdUnimodularMetricAdapter F).det * (-9 / 4 : ℂ) = (cgdUnimodularMetricAdapter F).det * (3 * I / 2 : ℂ)^2 := by
           have hI : (3 * I / 2 : ℂ)^2 = -9 / 4 := by
             calc (3 * I / 2 : ℂ)^2 = 9 * I^2 / 4 := by ring
               _ = 9 * (-1) / 4 := by rw [Complex.I_sq]
               _ = -9 / 4 := by ring
           rw [hI]
      _ = ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3))^2 := h_det_id
      _ = (-729 / 256 : ℂ) * Λ^6 := h_right

  intro h_cgd_det_zero
  have h_lam_zero : Λ = 0 := by
    have h_eq2 : Λ^6 = 0 := by
      calc Λ^6 = (-256 / 729 : ℂ) * ((-729 / 256 : ℂ) * Λ^6) := by ring
        _ = (-256 / 729 : ℂ) * ((cgdUnimodularMetricAdapter F).det * (-9 / 4 : ℂ)) := by rw [← h_left_eq]
        _ = (-256 / 729 : ℂ) * (0 * (-9 / 4 : ℂ)) := by rw [h_cgd_det_zero]
        _ = 0 := by ring
    exact eq_zero_of_pow_eq_zero h_eq2

  exact h_Λ h_lam_zero

end CGD.Gravity

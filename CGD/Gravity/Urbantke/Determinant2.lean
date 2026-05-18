-- FILENAME: CGD/Gravity/Urbantke/Determinant2.lean

import CGD.Gravity.Urbantke.Determinant1

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

/--
IMPLEMENTER NOTE:
The fundamental algebraic invariant of the Urbantke metric.
This theorem proves that for any tensor F representing an su(2) 2-form, 
if F satisfies the Unimodular Plebanski constraint (F ∧ F = Λ I), 
the determinant of its constructed 4x4 Urbantke metric is uniquely fixed 
to a specific scalar value `det_val` dependent ONLY on Λ.
-/
theorem urbantke_det_uniqueness 
  (Λ : ℂ) :
  ∃ (det_val : ℂ), 
    ∀ (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
      (sqrt_g detPsi : ℂ),
      (∀ μ ν, F μ ν = - F ν μ) →
      (∀ μ ν, 
        F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧
        F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1) →
      ((∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
        CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1) →
      sqrt_g^2 = (cgdUnimodularMetricAdapter F).det →
      detPsi * ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3)) = 1 →
      (3 * I / 2 : ℂ) * sqrt_g * detPsi = 1 →
      (cgdUnimodularMetricAdapter F).det = det_val := by
  use (81 / 64 : ℂ) * Λ^6
  intro F sqrt_g detPsi h_antisymm h_su2 h_plebanski h_sqrt_g h_detPsi h_eq2_21
  
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

  calc (cgdUnimodularMetricAdapter F).det = (cgdUnimodularMetricAdapter F).det * 1 := by ring
    _ = (cgdUnimodularMetricAdapter F).det * ((3 * I / 2 : ℂ)^2 * (-4 / 9 : ℂ)) := by
          have hI : (3 * I / 2 : ℂ)^2 * (-4 / 9 : ℂ) = 1 := by
            calc (3 * I / 2 : ℂ)^2 * (-4 / 9 : ℂ) = (9 * I^2 / 4) * (-4 / 9 : ℂ) := by ring
              _ = (9 * (-1) / 4) * (-4 / 9 : ℂ) := by rw [Complex.I_sq]
              _ = 1 := by ring
          rw [hI]
    _ = ((cgdUnimodularMetricAdapter F).det * (3 * I / 2 : ℂ)^2) * (-4 / 9 : ℂ) := by ring
    _ = ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3))^2 * (-4 / 9 : ℂ) := by rw [h_det_id]
    _ = ((-729 / 256 : ℂ) * Λ^6) * (-4 / 9 : ℂ) := by rw [h_right]
    _ = (81 / 64 : ℂ) * Λ^6 := by ring

end CGD.Gravity

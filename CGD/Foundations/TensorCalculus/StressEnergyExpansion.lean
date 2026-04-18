-- FILENAME: CGD/Foundations/TensorCalculus/StressEnergyExpansion.lean

import CGD.Foundations.TensorCalculus.StressEnergyExpansion0
import CGD.Foundations.TensorCalculus.StressEnergyExpansion1
import CGD.Foundations.TensorCalculus.StressEnergyExpansion2
import CGD.Foundations.TensorCalculus.StressEnergyExpansion3

set_option linter.unusedVariables false

open Matrix Complex BigOperators CGD.Axioms Litlib.Y2003.nakahara2003geometry
namespace CGD.Foundations

theorem stressEnergyDivergenceExpansion (A : Fin 4 → SpacetimePoint → SL2C) 
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (ν : Fin 4) (x : SpacetimePoint) :
  (∑ μ : Fin 4, ∑ ρ : Fin 4, eta μ ρ * partialDeriv ρ (fun p =>
    (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) -
    (1 / 4 : Complex) * eta μ ν * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val))
  ) x) =
  ∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace (
    (∑ μ : Fin 4, ∑ ρ : Fin 4, (eta μ ρ : ℂ) • (covariantDeriv A μ ρ α x).val) * (curvatureSl2c A ν β x).val
  ) -
  (1 / 2 : Complex) * ∑ μ : Fin 4, ∑ α : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, eta μ ρ * eta α σ * Matrix.trace (
    (curvatureSl2c A μ α x).val *
    (covariantDeriv A ρ σ ν x + covariantDeriv A σ ν ρ x + covariantDeriv A ν ρ σ x).val
  ) := by
  fin_cases ν
  · exact stressEnergyDivergenceExpansion_0 A h_smooth x
  · exact stressEnergyDivergenceExpansion_1 A h_smooth x
  · exact stressEnergyDivergenceExpansion_2 A h_smooth x
  · exact stressEnergyDivergenceExpansion_3 A h_smooth x

end CGD.Foundations

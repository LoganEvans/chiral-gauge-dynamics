-- FILENAME: CGD/Foundations/StressEnergy.lean

import CGD.Foundations.GaugeGroup
import CGD.Axioms.Spacetime
import CGD.Foundations.Calculus
import CGD.Foundations.Action
import CGD.Foundations.Lagrangian
import CGD.Foundations.TensorCalculus
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CGD.Axioms.Ontology

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open Complex Matrix CGD.Foundations BigOperators
open CGD.Axioms

namespace CGD.Foundations

noncomputable def stressEnergyTensor (F : Fin 4 → Fin 4 → SpacetimePoint → SL2C) (μ ν : Fin 4) (x : SpacetimePoint) : Complex :=
  (∑ α, ∑ β, eta α β * Matrix.trace ((F μ α x).val * (F ν β x).val)) -
  (1 / 4 : Complex) * eta μ ν * (∑ ρ, ∑ σ, ∑ κ, ∑ γ, eta ρ κ * eta σ γ * Matrix.trace ((F ρ σ x).val * (F κ γ x).val))

/-- 🟢 DYNAMIC: Spacetime Translation Invariance yields a Conserved Stress-Energy Tensor (∂_μ T^μν = 0). -/
theorem dynamicStressEnergyConservation (u : Universe)
  (h_smooth : (∀ mu i j, ContDiff ℝ ⊤ (fun x => (u.sd_sector mu x).val i j)) ∧ 
              (∀ mu i j, ContDiff ℝ ⊤ (fun x => (u.asd_sector mu x).val i j))) :
  eulerLagrangePDEs u →
  ∀ ν x, (∑ μ, ∑ ρ, eta μ ρ * partialDeriv ρ (fun p => stressEnergyTensor (fun m n p' => curvatureSl2c u.sd_sector m n p') μ ν p) x) = 0 := by
  intros h_eom ν x
  have h_expand := stressEnergyDivergenceExpansion u.sd_sector h_smooth.1 ν x
  
  unfold stressEnergyTensor
  rw [h_expand]

  have h_self_dual_eom := h_eom.1
  
  have h_step1 : (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace (
      (∑ μ : Fin 4, ∑ ρ : Fin 4, (eta μ ρ : ℂ) • (covariantDeriv u.sd_sector μ ρ α x).val) * (curvatureSl2c u.sd_sector ν β x).val
    )) = 0 := by
    simp_rw [h_self_dual_eom]
    simp [Matrix.trace_zero, mul_zero]

  have h_step2 : ((1 / 2 : Complex) * ∑ μ : Fin 4, ∑ α : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, eta μ ρ * eta α σ * Matrix.trace (
      (curvatureSl2c u.sd_sector μ α x).val *
      (covariantDeriv u.sd_sector ρ σ ν x + covariantDeriv u.sd_sector σ ν ρ x + covariantDeriv u.sd_sector ν ρ σ x).val
    )) = 0 := by
    have hb : ∀ ρ σ, (covariantDeriv u.sd_sector ρ σ ν x + covariantDeriv u.sd_sector σ ν ρ x + covariantDeriv u.sd_sector ν ρ σ x).val = 0 := by
      intros ρ σ
      have hbi := bianchiIdentity u.sd_sector h_smooth.1 ρ σ ν x
      rw [hbi]
      rfl
    simp_rw [hb]
    simp [Matrix.trace_zero, mul_zero]

  rw [h_step1, h_step2, sub_zero]

end CGD.Foundations

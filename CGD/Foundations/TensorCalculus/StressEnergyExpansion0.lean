-- FILENAME: CGD/Foundations/TensorCalculus/StressEnergyExpansion0.lean

import CGD.Foundations.TensorCalculus.StressEnergyExpansionBase

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Matrix Complex BigOperators CGD.Axioms Litlib.Y2003.nakahara2003geometry
namespace CGD.Foundations

theorem stressEnergyDivergenceExpansion_0 (A : Fin 4 → SpacetimePoint → SL2C) 
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (x : SpacetimePoint) :
  (∑ μ : Fin 4, ∑ ρ : Fin 4, eta μ ρ * partialDeriv ρ (fun p =>
    (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A 0 β p).val)) -
    (1 / 4 : Complex) * eta μ 0 * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val))
  ) x) =
  ∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace (
    (∑ μ : Fin 4, ∑ ρ : Fin 4, (eta μ ρ : ℂ) • (covariantDeriv A μ ρ α x).val) * (curvatureSl2c A 0 β x).val
  ) -
  (1 / 2 : Complex) * ∑ μ : Fin 4, ∑ α : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, eta μ ρ * eta α σ * Matrix.trace (
    (curvatureSl2c A μ α x).val *
    (covariantDeriv A ρ σ 0 x + covariantDeriv A σ 0 ρ x + covariantDeriv A 0 ρ σ x).val
  ) := by

  have h_lhs : (∑ μ : Fin 4, ∑ ρ : Fin 4, eta μ ρ * partialDeriv ρ (fun p =>
    (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A 0 β p).val)) -
    (1 / 4 : Complex) * eta μ 0 * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val))
  ) x) =
  (∑ μ : Fin 4, ∑ ρ : Fin 4, eta μ ρ * (
    (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A μ α p) x).val * (curvatureSl2c A 0 β x).val + (curvatureSl2c A μ α x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 0 β p) x).val)) -
    (1 / 4 : Complex) * eta μ 0 * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A ρ' σ p) x).val * (curvatureSl2c A κ γ x).val + (curvatureSl2c A ρ' σ x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A κ γ p) x).val))
  )) := by
    apply Finset.sum_congr rfl; intro μ _
    apply Finset.sum_congr rfl; intro ρ _
    rw [LHS_stress_energy_deriv A h_smooth μ 0 ρ x]
  rw [h_lhs]

  rw [LHS_outer_contract_exact A 0 x]
  repeat rw [LHS_inner_2F_contract_exact]
  repeat rw [LHS_inner_4F_contract_exact]
  rw [RHS_stress_energy_contract_1_exact A 0 x]
  repeat rw [RHS_inner_contract_exact]
  rw [RHS_stress_energy_contract_2_exact A 0 x]

  have sl2c_add_val : ∀ (X Y : SL2C), (X + Y).val = X.val + Y.val := fun _ _ => rfl
  repeat rw [sl2c_add_val]
  repeat rw [covariantDeriv_val]
  repeat rw [dF_val A h_smooth]
  repeat rw [curvature_val]
  
  -- Execute the purely syntactic AST unrolling using explicitly curated assembly hooks.
  -- The presence of neg_mat_** finally permits negative matrix structures to fully shatter.
  simp only [
    trace_exact,
    add_mat_00, add_mat_01, add_mat_10, add_mat_11,
    sub_mat_00, sub_mat_01, sub_mat_10, sub_mat_11,
    neg_mat_00, neg_mat_01, neg_mat_10, neg_mat_11,
    mul_mat_00, mul_mat_01, mul_mat_10, mul_mat_11,
    smul_mat_00, smul_mat_01, smul_mat_10, smul_mat_11
  ]

  have hd2A_symm : ∀ ρ μ β a b, (partialDerivSl2c ρ (fun p => partialDerivSl2c μ (A β) p) x).val a b = (partialDerivSl2c μ (fun p => partialDerivSl2c ρ (A β) p) x).val a b := by
    intro ρ μ β a b
    rw [partialDerivSl2c_commutes A β ρ μ x (h_smooth β)]
  have hd2A_10 : ∀ β a b, (partialDerivSl2c 1 (fun p => partialDerivSl2c 0 (A β) p) x).val a b = (partialDerivSl2c 0 (fun p => partialDerivSl2c 1 (A β) p) x).val a b := fun β a b => hd2A_symm 1 0 β a b
  have hd2A_20 : ∀ β a b, (partialDerivSl2c 2 (fun p => partialDerivSl2c 0 (A β) p) x).val a b = (partialDerivSl2c 0 (fun p => partialDerivSl2c 2 (A β) p) x).val a b := fun β a b => hd2A_symm 2 0 β a b
  have hd2A_30 : ∀ β a b, (partialDerivSl2c 3 (fun p => partialDerivSl2c 0 (A β) p) x).val a b = (partialDerivSl2c 0 (fun p => partialDerivSl2c 3 (A β) p) x).val a b := fun β a b => hd2A_symm 3 0 β a b
  have hd2A_21 : ∀ β a b, (partialDerivSl2c 2 (fun p => partialDerivSl2c 1 (A β) p) x).val a b = (partialDerivSl2c 1 (fun p => partialDerivSl2c 2 (A β) p) x).val a b := fun β a b => hd2A_symm 2 1 β a b
  have hd2A_31 : ∀ β a b, (partialDerivSl2c 3 (fun p => partialDerivSl2c 1 (A β) p) x).val a b = (partialDerivSl2c 1 (fun p => partialDerivSl2c 3 (A β) p) x).val a b := fun β a b => hd2A_symm 3 1 β a b
  have hd2A_32 : ∀ β a b, (partialDerivSl2c 3 (fun p => partialDerivSl2c 2 (A β) p) x).val a b = (partialDerivSl2c 2 (fun p => partialDerivSl2c 3 (A β) p) x).val a b := fun β a b => hd2A_symm 3 2 β a b

  simp only [hd2A_10, hd2A_20, hd2A_30, hd2A_21, hd2A_31, hd2A_32]
  simp only [eta_00, eta_01, eta_02, eta_03, eta_10, eta_11, eta_12, eta_13, eta_20, eta_21, eta_22, eta_23, eta_30, eta_31, eta_32, eta_33]
  ring

end CGD.Foundations

-- FILENAME: CGD/Foundations/TensorCalculus/StressEnergyExpansionBase.lean

import CGD.Foundations.TensorCalculus.NoetherExpansion

set_option linter.unusedVariables false

open Matrix Complex BigOperators CGD.Axioms Litlib.Y2003.nakahara2003geometry
namespace CGD.Foundations

lemma contract_metric_scalar (f : Fin 4 → Fin 4 → ℂ) :
  (∑ μ : Fin 4, ∑ ρ : Fin 4, eta μ ρ * f μ ρ) = 
  - f 0 0 + f 1 1 + f 2 2 + f 3 3 := by
  simp [sum_fin_4, eta_00, eta_11, eta_22, eta_33,
        eta_01, eta_02, eta_03, eta_10,
        eta_12, eta_13, eta_20, eta_21,
        eta_23, eta_30, eta_31, eta_32]

lemma contract_metric_cast_smul (f : Fin 4 → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) :
  (∑ μ : Fin 4, ∑ ρ : Fin 4, (eta μ ρ : ℂ) • f μ ρ) = 
  - f 0 0 + f 1 1 + f 2 2 + f 3 3 := by
  simp [sum_fin_4, eta_00, eta_11, eta_22, eta_33,
        eta_01, eta_02, eta_03, eta_10,
        eta_12, eta_13, eta_20, eta_21,
        eta_23, eta_30, eta_31, eta_32]

lemma contract_4_metric_scalar (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, eta μ ρ * eta ν σ * f μ ν ρ σ) = 
    f 0 0 0 0 - f 0 1 0 1 - f 0 2 0 2 - f 0 3 0 3
  - f 1 0 1 0 + f 1 1 1 1 + f 1 2 1 2 + f 1 3 1 3
  - f 2 0 2 0 + f 2 1 2 1 + f 2 2 2 2 + f 2 3 2 3
  - f 3 0 3 0 + f 3 1 3 1 + f 3 2 3 2 + f 3 3 3 3 := by
  simp [sum_fin_4, eta_00, eta_11, eta_22, eta_33,
        eta_01, eta_02, eta_03, eta_10,
        eta_12, eta_13, eta_20, eta_21,
        eta_23, eta_30, eta_31, eta_32]
  ring

lemma partialDeriv_sub_c_local (f g : SpacetimePoint → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
  partialDeriv μ (fun p => f p - g p) x = partialDeriv μ f x - partialDeriv μ g x := by
  unfold partialDeriv
  have h_eq : (fun p => f p - g p) = f - g := rfl
  rw [h_eq, fderiv_sub hf hg]
  rfl

lemma diff_trace_F_F (A : Fin 4 → SpacetimePoint → SL2C) 
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (μ α ν β : Fin 4) (x : SpacetimePoint) :
  DifferentiableAt ℝ (fun p => Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) x := by
  have h_tr_eq : (fun p => Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) = ∑ i : Fin 2, fun p => ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val) i i := rfl
  rw [h_tr_eq]
  apply DifferentiableAt.sum; intro i _
  exact diff_matrix_mul _ _ x (diff_curvature_val A h_smooth μ α x) (diff_curvature_val A h_smooth ν β x) i i

lemma deriv_trace_F_F (A : Fin 4 → SpacetimePoint → SL2C) 
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (μ α ν β ρ : Fin 4) (x : SpacetimePoint) :
  partialDeriv ρ (fun p => Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) x =
  Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A μ α p) x).val * (curvatureSl2c A ν β x).val + 
                (curvatureSl2c A μ α x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A ν β p) x).val) := by
  have h_diff_F1 : ∀ i j, DifferentiableAt ℝ (fun p => (curvatureSl2c A μ α p).val i j) x := fun i j => diff_curvature_val A h_smooth μ α x i j
  have h_diff_F2 : ∀ i j, DifferentiableAt ℝ (fun p => (curvatureSl2c A ν β p).val i j) x := fun i j => diff_curvature_val A h_smooth ν β x i j
  have h_deriv_tr := partialDeriv_trace_c (fun p => (curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val) ρ x (diff_matrix_mul _ _ x h_diff_F1 h_diff_F2)
  rw [h_deriv_tr]
  have h_deriv_mul := partialDerivMat_mul (fun p => (curvatureSl2c A μ α p).val) (fun p => (curvatureSl2c A ν β p).val) ρ x h_diff_F1 h_diff_F2
  rw [h_deriv_mul]
  have h_mat1 : partialDerivMat ρ (fun p => (curvatureSl2c A μ α p).val) x = (partialDerivSl2c ρ (fun p => curvatureSl2c A μ α p) x).val := by
    symm; apply partialDerivSl2c_eq_mat; intro i j; exact h_diff_F1 i j
  have h_mat2 : partialDerivMat ρ (fun p => (curvatureSl2c A ν β p).val) x = (partialDerivSl2c ρ (fun p => curvatureSl2c A ν β p) x).val := by
    symm; apply partialDerivSl2c_eq_mat; intro i j; exact h_diff_F2 i j
  rw [h_mat1, h_mat2]

lemma diff_sum_F_F (A : Fin 4 → SpacetimePoint → SL2C) 
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (μ ν : Fin 4) (x : SpacetimePoint) :
  DifferentiableAt ℝ (fun p => ∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) x := by
  have h_sum1 : (fun p => ∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) = ∑ α : Fin 4, fun p => ∑ β : Fin 4, eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val) := rfl
  rw [h_sum1]
  apply DifferentiableAt.sum; intro α _
  have h_sum2 : (fun p => ∑ β : Fin 4, eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) = ∑ β : Fin 4, fun p => eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val) := rfl
  rw [h_sum2]
  apply DifferentiableAt.sum; intro β _
  have h_eq : (fun p => eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) = fun p => eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val) := rfl
  rw [h_eq]
  exact DifferentiableAt.mul (differentiable_const _).differentiableAt (diff_trace_F_F A h_smooth μ α ν β x)

lemma deriv_sum_F_F (A : Fin 4 → SpacetimePoint → SL2C) 
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (μ ν ρ : Fin 4) (x : SpacetimePoint) :
  partialDeriv ρ (fun p => ∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) x =
  ∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A μ α p) x).val * (curvatureSl2c A ν β x).val + (curvatureSl2c A μ α x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A ν β p) x).val) := by
  have hs1 : partialDeriv ρ (fun p => ∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) x =
             ∑ α : Fin 4, partialDeriv ρ (fun p => ∑ β : Fin 4, eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) x := by
    apply partialDeriv_sum; intro α _
    have h_sum2 : (fun p => ∑ β : Fin 4, eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) = ∑ β : Fin 4, fun p => eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val) := rfl
    rw [h_sum2]
    apply DifferentiableAt.sum; intro β _
    exact DifferentiableAt.mul (differentiable_const _).differentiableAt (diff_trace_F_F A h_smooth μ α ν β x)
  rw [hs1]
  apply Finset.sum_congr rfl; intro α _
  have hs2 : partialDeriv ρ (fun p => ∑ β : Fin 4, eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) x =
             ∑ β : Fin 4, partialDeriv ρ (fun p => eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) x := by
    apply partialDeriv_sum; intro β _
    exact DifferentiableAt.mul (differentiable_const _).differentiableAt (diff_trace_F_F A h_smooth μ α ν β x)
  rw [hs2]
  apply Finset.sum_congr rfl; intro β _
  rw [partialDeriv_smul_c_local _ _ _ _ (diff_trace_F_F A h_smooth μ α ν β x)]
  rw [deriv_trace_F_F A h_smooth μ α ν β ρ x]

lemma diff_sum_4F (A : Fin 4 → SpacetimePoint → SL2C) 
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (x : SpacetimePoint) :
  DifferentiableAt ℝ (fun p => ∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) x := by
  have h_sum1 : (fun p => ∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = ∑ ρ' : Fin 4, fun p => ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := rfl
  rw [h_sum1]
  apply DifferentiableAt.sum; intro ρ' _
  have h_sum2 : (fun p => ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = ∑ σ : Fin 4, fun p => ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := rfl
  rw [h_sum2]
  apply DifferentiableAt.sum; intro σ _
  have h_sum3 : (fun p => ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = ∑ κ : Fin 4, fun p => ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := rfl
  rw [h_sum3]
  apply DifferentiableAt.sum; intro κ _
  have h_sum4 : (fun p => ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = ∑ γ : Fin 4, fun p => eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := rfl
  rw [h_sum4]
  apply DifferentiableAt.sum; intro γ _
  have h_eq : (fun p => eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = fun p => (eta ρ' κ * eta σ γ) * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := by ext p; ring
  rw [h_eq]
  exact DifferentiableAt.mul (differentiable_const _).differentiableAt (diff_trace_F_F A h_smooth ρ' σ κ γ x)

lemma deriv_sum_4F (A : Fin 4 → SpacetimePoint → SL2C) 
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (ρ : Fin 4) (x : SpacetimePoint) :
  partialDeriv ρ (fun p => ∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) x =
  ∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A ρ' σ p) x).val * (curvatureSl2c A κ γ x).val + (curvatureSl2c A ρ' σ x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A κ γ p) x).val) := by
  have hs1 : partialDeriv ρ (fun p => ∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) x =
             ∑ ρ' : Fin 4, partialDeriv ρ (fun p => ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) x := by
    apply partialDeriv_sum; intro ρ' _
    have hs_2 : (fun p => ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = ∑ σ : Fin 4, fun p => ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := rfl
    rw [hs_2]
    apply DifferentiableAt.sum; intro σ _
    have hs_3 : (fun p => ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = ∑ κ : Fin 4, fun p => ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := rfl
    rw [hs_3]
    apply DifferentiableAt.sum; intro κ _
    have hs_4 : (fun p => ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = ∑ γ : Fin 4, fun p => eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := rfl
    rw [hs_4]
    apply DifferentiableAt.sum; intro γ _
    have h_eq : (fun p => eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = fun p => (eta ρ' κ * eta σ γ) * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := by ext p; ring
    rw [h_eq]
    exact DifferentiableAt.mul (differentiable_const _).differentiableAt (diff_trace_F_F A h_smooth ρ' σ κ γ x)
  rw [hs1]
  apply Finset.sum_congr rfl; intro ρ' _
  have hs2 : partialDeriv ρ (fun p => ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) x =
             ∑ σ : Fin 4, partialDeriv ρ (fun p => ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) x := by
    apply partialDeriv_sum; intro σ _
    have hs_3 : (fun p => ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = ∑ κ : Fin 4, fun p => ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := rfl
    rw [hs_3]
    apply DifferentiableAt.sum; intro κ _
    have hs_4 : (fun p => ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = ∑ γ : Fin 4, fun p => eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := rfl
    rw [hs_4]
    apply DifferentiableAt.sum; intro γ _
    have h_eq : (fun p => eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = fun p => (eta ρ' κ * eta σ γ) * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := by ext p; ring
    rw [h_eq]
    exact DifferentiableAt.mul (differentiable_const _).differentiableAt (diff_trace_F_F A h_smooth ρ' σ κ γ x)
  rw [hs2]
  apply Finset.sum_congr rfl; intro σ _
  have hs3 : partialDeriv ρ (fun p => ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) x =
             ∑ κ : Fin 4, partialDeriv ρ (fun p => ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) x := by
    apply partialDeriv_sum; intro κ _
    have hs_4 : (fun p => ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = ∑ γ : Fin 4, fun p => eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := rfl
    rw [hs_4]
    apply DifferentiableAt.sum; intro γ _
    have h_eq : (fun p => eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = fun p => (eta ρ' κ * eta σ γ) * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := by ext p; ring
    rw [h_eq]
    exact DifferentiableAt.mul (differentiable_const _).differentiableAt (diff_trace_F_F A h_smooth ρ' σ κ γ x)
  rw [hs3]
  apply Finset.sum_congr rfl; intro κ _
  have hs4 : partialDeriv ρ (fun p => ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) x =
             ∑ γ : Fin 4, partialDeriv ρ (fun p => eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) x := by
    apply partialDeriv_sum; intro γ _
    have h_eq : (fun p => eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = fun p => (eta ρ' κ * eta σ γ) * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := by ext p; ring
    rw [h_eq]
    exact DifferentiableAt.mul (differentiable_const _).differentiableAt (diff_trace_F_F A h_smooth ρ' σ κ γ x)
  rw [hs4]
  apply Finset.sum_congr rfl; intro γ _
  have h_eq : (fun p => eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) = fun p => (eta ρ' κ * eta σ γ) * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val) := by ext p; ring
  rw [h_eq]
  rw [partialDeriv_smul_c_local _ _ _ _ (diff_trace_F_F A h_smooth ρ' σ κ γ x)]
  rw [deriv_trace_F_F A h_smooth ρ' σ κ γ ρ x]

lemma LHS_stress_energy_deriv (A : Fin 4 → SpacetimePoint → SL2C) 
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (μ ν ρ : Fin 4) (x : SpacetimePoint) :
  partialDeriv ρ (fun p =>
    (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((curvatureSl2c A μ α p).val * (curvatureSl2c A ν β p).val)) -
    (1 / 4 : Complex) * eta μ ν * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val))
  ) x =
  (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A μ α p) x).val * (curvatureSl2c A ν β x).val + (curvatureSl2c A μ α x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A ν β p) x).val)) -
  (1 / 4 : Complex) * eta μ ν * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A ρ' σ p) x).val * (curvatureSl2c A κ γ x).val + (curvatureSl2c A ρ' σ x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A κ γ p) x).val)) := by
  
  have hd_left := diff_sum_F_F A h_smooth μ ν x
  have hd_right_sum := diff_sum_4F A h_smooth x
  have hd_right : DifferentiableAt ℝ (fun p => (1 / 4 : Complex) * eta μ ν * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val))) x := by
    have h_eq : (fun p => (1 / 4 : Complex) * eta μ ν * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val))) = 
                fun p => ((1 / 4 : Complex) * eta μ ν) * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) := by ext p; ring
    rw [h_eq]
    exact DifferentiableAt.mul (differentiable_const _).differentiableAt hd_right_sum

  rw [partialDeriv_sub_c_local _ _ ρ x hd_left hd_right]
  rw [deriv_sum_F_F A h_smooth μ ν ρ x]
  
  have h_eq : (fun p => (1 / 4 : Complex) * eta μ ν * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val))) = 
              fun p => ((1 / 4 : Complex) * eta μ ν) * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((curvatureSl2c A ρ' σ p).val * (curvatureSl2c A κ γ p).val)) := by ext p; ring
  rw [h_eq]
  rw [partialDeriv_smul_c_local _ _ _ _ hd_right_sum]
  rw [deriv_sum_4F A h_smooth ρ x]

lemma trace_exact (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace M = M 0 0 + M 1 1 := by
  unfold Matrix.trace
  rw [sum_fin_2]
  rfl

lemma add_mat_00 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A + B) 0 0 = A 0 0 + B 0 0 := rfl
lemma add_mat_01 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A + B) 0 1 = A 0 1 + B 0 1 := rfl
lemma add_mat_10 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A + B) 1 0 = A 1 0 + B 1 0 := rfl
lemma add_mat_11 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A + B) 1 1 = A 1 1 + B 1 1 := rfl

lemma sub_mat_00 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A - B) 0 0 = A 0 0 - B 0 0 := rfl
lemma sub_mat_01 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A - B) 0 1 = A 0 1 - B 0 1 := rfl
lemma sub_mat_10 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A - B) 1 0 = A 1 0 - B 1 0 := rfl
lemma sub_mat_11 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A - B) 1 1 = A 1 1 - B 1 1 := rfl

lemma smul_mat_00 (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : (c • A) 0 0 = c * A 0 0 := rfl
lemma smul_mat_01 (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : (c • A) 0 1 = c * A 0 1 := rfl
lemma smul_mat_10 (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : (c • A) 1 0 = c * A 1 0 := rfl
lemma smul_mat_11 (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : (c • A) 1 1 = c * A 1 1 := rfl

lemma mul_mat_00 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 := by rw [Matrix.mul_apply, sum_fin_2]
lemma mul_mat_01 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 := by rw [Matrix.mul_apply, sum_fin_2]
lemma mul_mat_10 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 := by rw [Matrix.mul_apply, sum_fin_2]
lemma mul_mat_11 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 := by rw [Matrix.mul_apply, sum_fin_2]

lemma neg_mat_00 (A : Matrix (Fin 2) (Fin 2) ℂ) : (-A) 0 0 = - A 0 0 := rfl
lemma neg_mat_01 (A : Matrix (Fin 2) (Fin 2) ℂ) : (-A) 0 1 = - A 0 1 := rfl
lemma neg_mat_10 (A : Matrix (Fin 2) (Fin 2) ℂ) : (-A) 1 0 = - A 1 0 := rfl
lemma neg_mat_11 (A : Matrix (Fin 2) (Fin 2) ℂ) : (-A) 1 1 = - A 1 1 := rfl

lemma LHS_outer_contract_exact (A : Fin 4 → SpacetimePoint → SL2C) (ν : Fin 4) (x : SpacetimePoint) :
  (∑ μ : Fin 4, ∑ ρ : Fin 4, eta μ ρ * (
    (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A μ α p) x).val * (curvatureSl2c A ν β x).val + (curvatureSl2c A μ α x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A ν β p) x).val)) -
    (1 / 4 : Complex) * eta μ ν * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A ρ' σ p) x).val * (curvatureSl2c A κ γ x).val + (curvatureSl2c A ρ' σ x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A κ γ p) x).val))
  )) = 
  - ( (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((partialDerivSl2c 0 (fun p => curvatureSl2c A 0 α p) x).val * (curvatureSl2c A ν β x).val + (curvatureSl2c A 0 α x).val * (partialDerivSl2c 0 (fun p => curvatureSl2c A ν β p) x).val)) -
      (1 / 4 : Complex) * eta 0 ν * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((partialDerivSl2c 0 (fun p => curvatureSl2c A ρ' σ p) x).val * (curvatureSl2c A κ γ x).val + (curvatureSl2c A ρ' σ x).val * (partialDerivSl2c 0 (fun p => curvatureSl2c A κ γ p) x).val)) )
  + ( (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((partialDerivSl2c 1 (fun p => curvatureSl2c A 1 α p) x).val * (curvatureSl2c A ν β x).val + (curvatureSl2c A 1 α x).val * (partialDerivSl2c 1 (fun p => curvatureSl2c A ν β p) x).val)) -
      (1 / 4 : Complex) * eta 1 ν * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((partialDerivSl2c 1 (fun p => curvatureSl2c A ρ' σ p) x).val * (curvatureSl2c A κ γ x).val + (curvatureSl2c A ρ' σ x).val * (partialDerivSl2c 1 (fun p => curvatureSl2c A κ γ p) x).val)) )
  + ( (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((partialDerivSl2c 2 (fun p => curvatureSl2c A 2 α p) x).val * (curvatureSl2c A ν β x).val + (curvatureSl2c A 2 α x).val * (partialDerivSl2c 2 (fun p => curvatureSl2c A ν β p) x).val)) -
      (1 / 4 : Complex) * eta 2 ν * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((partialDerivSl2c 2 (fun p => curvatureSl2c A ρ' σ p) x).val * (curvatureSl2c A κ γ x).val + (curvatureSl2c A ρ' σ x).val * (partialDerivSl2c 2 (fun p => curvatureSl2c A κ γ p) x).val)) )
  + ( (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((partialDerivSl2c 3 (fun p => curvatureSl2c A 3 α p) x).val * (curvatureSl2c A ν β x).val + (curvatureSl2c A 3 α x).val * (partialDerivSl2c 3 (fun p => curvatureSl2c A ν β p) x).val)) -
      (1 / 4 : Complex) * eta 3 ν * (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((partialDerivSl2c 3 (fun p => curvatureSl2c A ρ' σ p) x).val * (curvatureSl2c A κ γ x).val + (curvatureSl2c A ρ' σ x).val * (partialDerivSl2c 3 (fun p => curvatureSl2c A κ γ p) x).val)) ) := by
  exact contract_metric_scalar _

lemma LHS_inner_2F_contract_exact (A : Fin 4 → SpacetimePoint → SL2C) (μ ρ ν : Fin 4) (x : SpacetimePoint) :
  (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A μ α p) x).val * (curvatureSl2c A ν β x).val + (curvatureSl2c A μ α x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A ν β p) x).val)) =
  - Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A μ 0 p) x).val * (curvatureSl2c A ν 0 x).val + (curvatureSl2c A μ 0 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A ν 0 p) x).val)
  + Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A μ 1 p) x).val * (curvatureSl2c A ν 1 x).val + (curvatureSl2c A μ 1 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A ν 1 p) x).val)
  + Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A μ 2 p) x).val * (curvatureSl2c A ν 2 x).val + (curvatureSl2c A μ 2 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A ν 2 p) x).val)
  + Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A μ 3 p) x).val * (curvatureSl2c A ν 3 x).val + (curvatureSl2c A μ 3 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A ν 3 p) x).val) := by
  exact contract_metric_scalar _

lemma LHS_inner_4F_contract_exact (A : Fin 4 → SpacetimePoint → SL2C) (ρ : Fin 4) (x : SpacetimePoint) :
  (∑ ρ' : Fin 4, ∑ σ : Fin 4, ∑ κ : Fin 4, ∑ γ : Fin 4, eta ρ' κ * eta σ γ * Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A ρ' σ p) x).val * (curvatureSl2c A κ γ x).val + (curvatureSl2c A ρ' σ x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A κ γ p) x).val)) =
    Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 0 0 p) x).val * (curvatureSl2c A 0 0 x).val + (curvatureSl2c A 0 0 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 0 0 p) x).val)
  - Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 0 1 p) x).val * (curvatureSl2c A 0 1 x).val + (curvatureSl2c A 0 1 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 0 1 p) x).val)
  - Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 0 2 p) x).val * (curvatureSl2c A 0 2 x).val + (curvatureSl2c A 0 2 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 0 2 p) x).val)
  - Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 0 3 p) x).val * (curvatureSl2c A 0 3 x).val + (curvatureSl2c A 0 3 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 0 3 p) x).val)
  - Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 1 0 p) x).val * (curvatureSl2c A 1 0 x).val + (curvatureSl2c A 1 0 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 1 0 p) x).val)
  + Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 1 1 p) x).val * (curvatureSl2c A 1 1 x).val + (curvatureSl2c A 1 1 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 1 1 p) x).val)
  + Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 1 2 p) x).val * (curvatureSl2c A 1 2 x).val + (curvatureSl2c A 1 2 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 1 2 p) x).val)
  + Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 1 3 p) x).val * (curvatureSl2c A 1 3 x).val + (curvatureSl2c A 1 3 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 1 3 p) x).val)
  - Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 2 0 p) x).val * (curvatureSl2c A 2 0 x).val + (curvatureSl2c A 2 0 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 2 0 p) x).val)
  + Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 2 1 p) x).val * (curvatureSl2c A 2 1 x).val + (curvatureSl2c A 2 1 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 2 1 p) x).val)
  + Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 2 2 p) x).val * (curvatureSl2c A 2 2 x).val + (curvatureSl2c A 2 2 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 2 2 p) x).val)
  + Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 2 3 p) x).val * (curvatureSl2c A 2 3 x).val + (curvatureSl2c A 2 3 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 2 3 p) x).val)
  - Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 3 0 p) x).val * (curvatureSl2c A 3 0 x).val + (curvatureSl2c A 3 0 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 3 0 p) x).val)
  + Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 3 1 p) x).val * (curvatureSl2c A 3 1 x).val + (curvatureSl2c A 3 1 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 3 1 p) x).val)
  + Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 3 2 p) x).val * (curvatureSl2c A 3 2 x).val + (curvatureSl2c A 3 2 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 3 2 p) x).val)
  + Matrix.trace ((partialDerivSl2c ρ (fun p => curvatureSl2c A 3 3 p) x).val * (curvatureSl2c A 3 3 x).val + (curvatureSl2c A 3 3 x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A 3 3 p) x).val) := by
  exact contract_4_metric_scalar _

lemma RHS_stress_energy_contract_1_exact (A : Fin 4 → SpacetimePoint → SL2C) (ν : Fin 4) (x : SpacetimePoint) :
  (∑ α : Fin 4, ∑ β : Fin 4, eta α β * Matrix.trace (
    (∑ μ : Fin 4, ∑ ρ : Fin 4, (eta μ ρ : ℂ) • (covariantDeriv A μ ρ α x).val) * (curvatureSl2c A ν β x).val
  )) =
  - Matrix.trace ((∑ μ : Fin 4, ∑ ρ : Fin 4, (eta μ ρ : ℂ) • (covariantDeriv A μ ρ 0 x).val) * (curvatureSl2c A ν 0 x).val)
  + Matrix.trace ((∑ μ : Fin 4, ∑ ρ : Fin 4, (eta μ ρ : ℂ) • (covariantDeriv A μ ρ 1 x).val) * (curvatureSl2c A ν 1 x).val)
  + Matrix.trace ((∑ μ : Fin 4, ∑ ρ : Fin 4, (eta μ ρ : ℂ) • (covariantDeriv A μ ρ 2 x).val) * (curvatureSl2c A ν 2 x).val)
  + Matrix.trace ((∑ μ : Fin 4, ∑ ρ : Fin 4, (eta μ ρ : ℂ) • (covariantDeriv A μ ρ 3 x).val) * (curvatureSl2c A ν 3 x).val) := by
  exact contract_metric_scalar _

lemma RHS_inner_contract_exact (A : Fin 4 → SpacetimePoint → SL2C) (α : Fin 4) (x : SpacetimePoint) :
  (∑ μ : Fin 4, ∑ ρ : Fin 4, (eta μ ρ : ℂ) • (covariantDeriv A μ ρ α x).val) =
  - (covariantDeriv A 0 0 α x).val
  + (covariantDeriv A 1 1 α x).val
  + (covariantDeriv A 2 2 α x).val
  + (covariantDeriv A 3 3 α x).val := by
  exact contract_metric_cast_smul _

lemma RHS_stress_energy_contract_2_exact (A : Fin 4 → SpacetimePoint → SL2C) (ν : Fin 4) (x : SpacetimePoint) :
  (∑ μ : Fin 4, ∑ α : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, eta μ ρ * eta α σ * Matrix.trace (
    (curvatureSl2c A μ α x).val *
    (covariantDeriv A ρ σ ν x + covariantDeriv A σ ν ρ x + covariantDeriv A ν ρ σ x).val
  )) =
    Matrix.trace ((curvatureSl2c A 0 0 x).val * (covariantDeriv A 0 0 ν x + covariantDeriv A 0 ν 0 x + covariantDeriv A ν 0 0 x).val)
  - Matrix.trace ((curvatureSl2c A 0 1 x).val * (covariantDeriv A 0 1 ν x + covariantDeriv A 1 ν 0 x + covariantDeriv A ν 0 1 x).val)
  - Matrix.trace ((curvatureSl2c A 0 2 x).val * (covariantDeriv A 0 2 ν x + covariantDeriv A 2 ν 0 x + covariantDeriv A ν 0 2 x).val)
  - Matrix.trace ((curvatureSl2c A 0 3 x).val * (covariantDeriv A 0 3 ν x + covariantDeriv A 3 ν 0 x + covariantDeriv A ν 0 3 x).val)
  - Matrix.trace ((curvatureSl2c A 1 0 x).val * (covariantDeriv A 1 0 ν x + covariantDeriv A 0 ν 1 x + covariantDeriv A ν 1 0 x).val)
  + Matrix.trace ((curvatureSl2c A 1 1 x).val * (covariantDeriv A 1 1 ν x + covariantDeriv A 1 ν 1 x + covariantDeriv A ν 1 1 x).val)
  + Matrix.trace ((curvatureSl2c A 1 2 x).val * (covariantDeriv A 1 2 ν x + covariantDeriv A 2 ν 1 x + covariantDeriv A ν 1 2 x).val)
  + Matrix.trace ((curvatureSl2c A 1 3 x).val * (covariantDeriv A 1 3 ν x + covariantDeriv A 3 ν 1 x + covariantDeriv A ν 1 3 x).val)
  - Matrix.trace ((curvatureSl2c A 2 0 x).val * (covariantDeriv A 2 0 ν x + covariantDeriv A 0 ν 2 x + covariantDeriv A ν 2 0 x).val)
  + Matrix.trace ((curvatureSl2c A 2 1 x).val * (covariantDeriv A 2 1 ν x + covariantDeriv A 1 ν 2 x + covariantDeriv A ν 2 1 x).val)
  + Matrix.trace ((curvatureSl2c A 2 2 x).val * (covariantDeriv A 2 2 ν x + covariantDeriv A 2 ν 2 x + covariantDeriv A ν 2 2 x).val)
  + Matrix.trace ((curvatureSl2c A 2 3 x).val * (covariantDeriv A 2 3 ν x + covariantDeriv A 3 ν 2 x + covariantDeriv A ν 2 3 x).val)
  - Matrix.trace ((curvatureSl2c A 3 0 x).val * (covariantDeriv A 3 0 ν x + covariantDeriv A 0 ν 3 x + covariantDeriv A ν 3 0 x).val)
  + Matrix.trace ((curvatureSl2c A 3 1 x).val * (covariantDeriv A 3 1 ν x + covariantDeriv A 1 ν 3 x + covariantDeriv A ν 3 1 x).val)
  + Matrix.trace ((curvatureSl2c A 3 2 x).val * (covariantDeriv A 3 2 ν x + covariantDeriv A 2 ν 3 x + covariantDeriv A ν 3 2 x).val)
  + Matrix.trace ((curvatureSl2c A 3 3 x).val * (covariantDeriv A 3 3 ν x + covariantDeriv A 3 ν 3 x + covariantDeriv A ν 3 3 x).val) := by
  exact contract_4_metric_scalar _

end CGD.Foundations

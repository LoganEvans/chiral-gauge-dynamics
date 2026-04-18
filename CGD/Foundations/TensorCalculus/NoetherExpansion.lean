-- FILENAME: CGD/Foundations/TensorCalculus/NoetherExpansion.lean

import CGD.Foundations.TensorCalculus.DifferentialRules
import CGD.Foundations.TensorCalculus.LieAlgebra
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Matrix Complex BigOperators CGD.Axioms Litlib.Y2003.nakahara2003geometry
namespace CGD.Foundations

lemma eta_symm (μ ν : Fin 4) : CGD.Axioms.eta μ ν = CGD.Axioms.eta ν μ := by
  fin_cases μ <;> fin_cases ν <;> rfl

lemma eta_00 : CGD.Axioms.eta 0 0 = -1 := rfl
lemma eta_11 : CGD.Axioms.eta 1 1 = 1 := rfl
lemma eta_22 : CGD.Axioms.eta 2 2 = 1 := rfl
lemma eta_33 : CGD.Axioms.eta 3 3 = 1 := rfl
lemma eta_01 : CGD.Axioms.eta 0 1 = 0 := rfl
lemma eta_02 : CGD.Axioms.eta 0 2 = 0 := rfl
lemma eta_03 : CGD.Axioms.eta 0 3 = 0 := rfl
lemma eta_10 : CGD.Axioms.eta 1 0 = 0 := rfl
lemma eta_12 : CGD.Axioms.eta 1 2 = 0 := rfl
lemma eta_13 : CGD.Axioms.eta 1 3 = 0 := rfl
lemma eta_20 : CGD.Axioms.eta 2 0 = 0 := rfl
lemma eta_21 : CGD.Axioms.eta 2 1 = 0 := rfl
lemma eta_23 : CGD.Axioms.eta 2 3 = 0 := rfl
lemma eta_30 : CGD.Axioms.eta 3 0 = 0 := rfl
lemma eta_31 : CGD.Axioms.eta 3 1 = 0 := rfl
lemma eta_32 : CGD.Axioms.eta 3 2 = 0 := rfl

lemma sl2c_bracket_val (A B : SL2C) : ⁅A, B⁆.val = A.val * B.val - B.val * A.val := rfl

lemma sum_fin_4 {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) : 
  (∑ i : Fin 4, f i) = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_four]

lemma sum_fin_2 {M : Type*} [AddCommMonoid M] (f : Fin 2 → M) : 
  (∑ i : Fin 2, f i) = f 0 + f 1 := by
  rw [Fin.sum_univ_two]

lemma diff_curvature_val (A : Fin 4 → SpacetimePoint → SL2C) (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j)) 
  (α β : Fin 4) (x : SpacetimePoint) :
  ∀ i j, DifferentiableAt ℝ (fun p => (curvatureSl2c A α β p).val i j) x :=
  fun i j => diff_curvature A h_smooth α β i j x

lemma diff_A_val (A : Fin 4 → SpacetimePoint → SL2C) (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j)) 
  (α : Fin 4) (x : SpacetimePoint) :
  ∀ i j, DifferentiableAt ℝ (fun p => (A α p).val i j) x :=
  fun i j => diff_A A h_smooth α i j x

lemma partialDeriv_trace_c (f : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => f p i j) x) :
  partialDeriv μ (fun p => Matrix.trace (f p)) x = Matrix.trace (partialDerivMat μ f x) := by
  unfold partialDerivMat Matrix.trace
  exact (partialDeriv_sum _ _ μ x (fun i _ => hf i i))

lemma covariantDeriv_val (A : Fin 4 → SpacetimePoint → SL2C) (μ ρ β : Fin 4) (x : SpacetimePoint) :
  (covariantDeriv A μ ρ β x).val = 
    (partialDerivSl2c μ (fun p => curvatureSl2c A ρ β p) x).val + 
    (A μ x).val * (curvatureSl2c A ρ β x).val - (curvatureSl2c A ρ β x).val * (A μ x).val := by
  unfold covariantDeriv
  have sl2c_add_val : ∀ (X Y : SL2C), (X + Y).val = X.val + Y.val := fun _ _ => rfl
  ext i j
  simp only [sl2c_add_val, sl2c_bracket_val, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
  ring

lemma curvature_val (A : Fin 4 → SpacetimePoint → SL2C) (μ β : Fin 4) (x : SpacetimePoint) :
  (curvatureSl2c A μ β x).val = 
    (partialDerivSl2c μ (A β) x).val - (partialDerivSl2c β (A μ) x).val + 
    (A μ x).val * (A β x).val - (A β x).val * (A μ x).val := by
  unfold curvatureSl2c
  have sl2c_add_val : ∀ (X Y : SL2C), (X + Y).val = X.val + Y.val := fun _ _ => rfl
  have sl2c_sub_val : ∀ (X Y : SL2C), (X - Y).val = X.val - Y.val := fun _ _ => rfl
  ext i j
  simp only [sl2c_add_val, sl2c_sub_val, sl2c_bracket_val, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
  ring
  
lemma dF_val (A : Fin 4 → SpacetimePoint → SL2C) 
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (ρ μ β : Fin 4) (x : SpacetimePoint) :
  (partialDerivSl2c ρ (fun p => curvatureSl2c A μ β p) x).val =
    (partialDerivSl2c ρ (fun p => partialDerivSl2c μ (A β) p) x).val -
    (partialDerivSl2c ρ (fun p => partialDerivSl2c β (A μ) p) x).val +
    (partialDerivSl2c ρ (A μ) x).val * (A β x).val - (A β x).val * (partialDerivSl2c ρ (A μ) x).val +
    (A μ x).val * (partialDerivSl2c ρ (A β) x).val - (partialDerivSl2c ρ (A β) x).val * (A μ x).val := by
  have hdA_mu : ∀ i j, DifferentiableAt ℝ (fun p => (A μ p).val i j) x := fun i j => diff_A_val A h_smooth μ x i j
  have hdA_beta : ∀ i j, DifferentiableAt ℝ (fun p => (A β p).val i j) x := fun i j => diff_A_val A h_smooth β x i j
  have hd_dA_mu_beta : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c μ (A β) p).val i j) x := fun i j => diff_dA A h_smooth μ β i j x
  have hd_dA_beta_mu : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c β (A μ) p).val i j) x := fun i j => diff_dA A h_smooth β μ i j x
  have hdSub : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c μ (A β) p - partialDerivSl2c β (A μ) p).val i j) x := fun i j => DifferentiableAt.sub (hd_dA_mu_beta i j) (hd_dA_beta_mu i j)
  have hdComm : ∀ i j, DifferentiableAt ℝ (fun p => (⁅A μ p, A β p⁆).val i j) x := fun i j => diff_comm A h_smooth μ β i j x

  have h_expand_func : (fun p => curvatureSl2c A μ β p) = fun p => (partialDerivSl2c μ (A β) p - partialDerivSl2c β (A μ) p) + ⁅A μ p, A β p⁆ := by
    funext p
    exact curvatureSl2c_def A μ β p
  rw [h_expand_func]
  rw [partialDerivSl2c_add _ _ ρ x hdSub hdComm]
  rw [partialDerivSl2c_sub _ _ ρ x hd_dA_mu_beta hd_dA_beta_mu]
  rw [partialDerivSl2c_bracket _ _ ρ x hdA_mu hdA_beta]
  
  have sl2c_add_val : ∀ (X Y : SL2C), (X + Y).val = X.val + Y.val := fun _ _ => rfl
  have sl2c_sub_val : ∀ (X Y : SL2C), (X - Y).val = X.val - Y.val := fun _ _ => rfl
  
  ext i j
  simp only [sl2c_add_val, sl2c_sub_val, sl2c_bracket_val, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
  ring
  
lemma LHS_inner_val (A : Fin 4 → SpacetimePoint → SL2C) 
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (μ ρ ν β : Fin 4) (x : SpacetimePoint) :
  partialDerivMat ρ (fun p => (eta ν β : ℂ) • ⁅curvatureSl2c A μ β p, A ν p⁆.val) x =
  (eta ν β : ℂ) • (
    (partialDerivSl2c ρ (fun p => curvatureSl2c A μ β p) x).val * (A ν x).val -
    (A ν x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A μ β p) x).val +
    (curvatureSl2c A μ β x).val * (partialDerivSl2c ρ (A ν) x).val -
    (partialDerivSl2c ρ (A ν) x).val * (curvatureSl2c A μ β x).val
  ) := by
  have hd_diff : ∀ a b, DifferentiableAt ℝ (fun p => ⁅curvatureSl2c A μ β p, A ν p⁆.val a b) x := by
    intro a b
    have hm1 := diff_matrix_mul (fun p => (curvatureSl2c A μ β p).val) (fun p => (A ν p).val) x (diff_curvature_val A h_smooth μ β x) (diff_A_val A h_smooth ν x)
    have hm2 := diff_matrix_mul (fun p => (A ν p).val) (fun p => (curvatureSl2c A μ β p).val) x (diff_A_val A h_smooth ν x) (diff_curvature_val A h_smooth μ β x)
    exact diff_matrix_sub _ _ x hm1 hm2 a b
  rw [partialDerivMat_smul_c (eta ν β : ℂ) _ ρ x hd_diff]
  congr 1
  have h_mat_lhs : partialDerivMat ρ (fun p => ⁅curvatureSl2c A μ β p, A ν p⁆.val) x = (partialDerivSl2c ρ (fun p => ⁅curvatureSl2c A μ β p, A ν p⁆) x).val := by
    symm; apply partialDerivSl2c_eq_mat
    intro a b
    exact hd_diff a b
  rw [h_mat_lhs, partialDerivSl2c_bracket _ _ ρ x (diff_curvature_val A h_smooth μ β x) (diff_A_val A h_smooth ν x)]
  have sl2c_add_val : ∀ (X Y : SL2C), (X + Y).val = X.val + Y.val := fun _ _ => rfl
  ext i j
  simp only [sl2c_add_val, sl2c_bracket_val, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
  ring

lemma LHS_sum_val (A : Fin 4 → SpacetimePoint → SL2C) 
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (μ ρ : Fin 4) (x : SpacetimePoint) :
  partialDerivMat ρ (fun p => ∑ ν : Fin 4, ∑ β : Fin 4, (eta ν β : ℂ) • ⁅curvatureSl2c A μ β p, A ν p⁆.val) x =
  ∑ ν : Fin 4, ∑ β : Fin 4, partialDerivMat ρ (fun p => (eta ν β : ℂ) • ⁅curvatureSl2c A μ β p, A ν p⁆.val) x := by
  have hs1 : partialDerivMat ρ (fun p => ∑ ν : Fin 4, ∑ β : Fin 4, (eta ν β : ℂ) • ⁅curvatureSl2c A μ β p, A ν p⁆.val) x =
             ∑ ν : Fin 4, partialDerivMat ρ (fun p => ∑ β : Fin 4, (eta ν β : ℂ) • ⁅curvatureSl2c A μ β p, A ν p⁆.val) x := by
    apply partialDerivMat_sum_c
    intro ν _ a b
    have h_sum : (fun p => (∑ β : Fin 4, (eta ν β : ℂ) • ⁅curvatureSl2c A μ β p, A ν p⁆.val) a b) = ∑ β : Fin 4, fun p => ((eta ν β : ℂ) • ⁅curvatureSl2c A μ β p, A ν p⁆.val) a b := by
      ext p
      simp only [Matrix.sum_apply, Finset.sum_apply]
    rw [h_sum]
    apply DifferentiableAt.sum
    intro β _
    have hm1 := diff_matrix_mul (fun p => (curvatureSl2c A μ β p).val) (fun p => (A ν p).val) x (diff_curvature_val A h_smooth μ β x) (diff_A_val A h_smooth ν x)
    have hm2 := diff_matrix_mul (fun p => (A ν p).val) (fun p => (curvatureSl2c A μ β p).val) x (diff_A_val A h_smooth ν x) (diff_curvature_val A h_smooth μ β x)
    have hm3 := diff_matrix_sub _ _ x hm1 hm2 a b
    have h_eq : (fun p => ((eta ν β : ℂ) • ⁅curvatureSl2c A μ β p, A ν p⁆.val) a b) = fun p => (eta ν β : ℂ) * ⁅curvatureSl2c A μ β p, A ν p⁆.val a b := rfl
    rw [h_eq]
    exact DifferentiableAt.mul (differentiable_const _).differentiableAt hm3
  rw [hs1]
  apply Finset.sum_congr rfl; intro ν _
  apply partialDerivMat_sum_c
  intro β _ a b
  have hm1 := diff_matrix_mul (fun p => (curvatureSl2c A μ β p).val) (fun p => (A ν p).val) x (diff_curvature_val A h_smooth μ β x) (diff_A_val A h_smooth ν x)
  have hm2 := diff_matrix_mul (fun p => (A ν p).val) (fun p => (curvatureSl2c A μ β p).val) x (diff_A_val A h_smooth ν x) (diff_curvature_val A h_smooth μ β x)
  have hm3 := diff_matrix_sub _ _ x hm1 hm2 a b
  have h_eq : (fun p => ((eta ν β : ℂ) • ⁅curvatureSl2c A μ β p, A ν p⁆.val) a b) = fun p => (eta ν β : ℂ) * ⁅curvatureSl2c A μ β p, A ν p⁆.val a b := rfl
  rw [h_eq]
  exact DifferentiableAt.mul (differentiable_const _).differentiableAt hm3

lemma contract_metric_mat (f : Fin 4 → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) :
  (∑ μ : Fin 4, ∑ ρ : Fin 4, eta μ ρ • f μ ρ) = 
  - f 0 0 + f 1 1 + f 2 2 + f 3 3 := by
  simp [sum_fin_4, eta_00, eta_11, eta_22, eta_33,
        eta_01, eta_02, eta_03, eta_10,
        eta_12, eta_13, eta_20, eta_21,
        eta_23, eta_30, eta_31, eta_32]

lemma contract_metric_mat_cast (f : Fin 4 → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) :
  (∑ μ : Fin 4, ∑ ρ : Fin 4, (eta μ ρ : ℂ) • f μ ρ) = 
  - f 0 0 + f 1 1 + f 2 2 + f 3 3 := by
  simp [sum_fin_4, eta_00, eta_11, eta_22, eta_33,
        eta_01, eta_02, eta_03, eta_10,
        eta_12, eta_13, eta_20, eta_21,
        eta_23, eta_30, eta_31, eta_32]

theorem noetherDivergenceExpansion (A : Fin 4 → SpacetimePoint → SL2C) 
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (x : SpacetimePoint) :
  (∑ μ : Fin 4, ∑ ρ : Fin 4, eta μ ρ • partialDerivMat ρ (fun p => ∑ ν : Fin 4, ∑ β : Fin 4, (eta ν β : ℂ) • ⁅curvatureSl2c A μ β p, A ν p⁆.val) x) =
  ∑ ν : Fin 4, ∑ β : Fin 4, eta ν β • (
    (∑ μ : Fin 4, ∑ ρ : Fin 4, (eta μ ρ : ℂ) • (covariantDeriv A μ ρ β x).val) * (A ν x).val -
    (A ν x).val * (∑ μ : Fin 4, ∑ ρ : Fin 4, (eta μ ρ : ℂ) • (covariantDeriv A μ ρ β x).val)
  ) := by
  
  have h_lhs : (∑ μ : Fin 4, ∑ ρ : Fin 4, eta μ ρ • partialDerivMat ρ (fun p => ∑ ν : Fin 4, ∑ β : Fin 4, (eta ν β : ℂ) • ⁅curvatureSl2c A μ β p, A ν p⁆.val) x) =
    ∑ μ : Fin 4, ∑ ρ : Fin 4, eta μ ρ • (∑ ν : Fin 4, ∑ β : Fin 4, (eta ν β : ℂ) • (
      (partialDerivSl2c ρ (fun p => curvatureSl2c A μ β p) x).val * (A ν x).val -
      (A ν x).val * (partialDerivSl2c ρ (fun p => curvatureSl2c A μ β p) x).val +
      (curvatureSl2c A μ β x).val * (partialDerivSl2c ρ (A ν) x).val -
      (partialDerivSl2c ρ (A ν) x).val * (curvatureSl2c A μ β x).val
    )) := by
    apply Finset.sum_congr rfl; intro μ _
    apply Finset.sum_congr rfl; intro ρ _
    rw [LHS_sum_val A h_smooth μ ρ x]
    congr 1
    apply Finset.sum_congr rfl; intro ν _
    apply Finset.sum_congr rfl; intro β _
    rw [LHS_inner_val A h_smooth μ ρ ν β x]
    
  rw [h_lhs]

  simp only [contract_metric_mat, contract_metric_mat_cast]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [covariantDeriv_val A, curvature_val A, dF_val A h_smooth]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.neg_apply, sum_fin_2]

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
  ring

end CGD.Foundations

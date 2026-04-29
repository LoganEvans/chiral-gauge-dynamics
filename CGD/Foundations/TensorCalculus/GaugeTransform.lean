-- FILENAME: CGD/Foundations/TensorCalculus/GaugeTransform.lean

import Litlib.Core
import CGD.Foundations.TensorCalculus.DifferentialRules
import CGD.Foundations.Calculus
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Algebra.Lie.Classical

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Matrix Complex BigOperators CGD.Axioms Litlib.Y2003.nakahara2003geometry

namespace CGD.Foundations

lemma partialDerivMat_mul3 (μ : Fin 4) (f g h : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (x : SpacetimePoint)
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => f p i j) x)
  (hg : ∀ i j, DifferentiableAt ℝ (fun p => g p i j) x)
  (hh : ∀ i j, DifferentiableAt ℝ (fun p => h p i j) x) :
  partialDerivMat μ (fun p => f p * g p * h p) x = 
    partialDerivMat μ f x * g x * h x + 
    f x * partialDerivMat μ g x * h x + 
    f x * g x * partialDerivMat μ h x := by
  have hd_fg := diff_matrix_mul f g x hf hg
  rw [partialDerivMat_mul (fun p => f p * g p) h μ x hd_fg hh]
  rw [partialDerivMat_mul f g μ x hf hg]
  calc
    (partialDerivMat μ f x * g x + f x * partialDerivMat μ g x) * h x + (f x * g x) * partialDerivMat μ h x
      = partialDerivMat μ f x * g x * h x + f x * partialDerivMat μ g x * h x + f x * g x * partialDerivMat μ h x := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]

lemma diff_inv_identity (μ : Fin 4) (U U_inv : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (x : SpacetimePoint)
  (hU_smooth : ∀ i j, DifferentiableAt ℝ (fun p => U p i j) x)
  (hUinv_smooth : ∀ i j, DifferentiableAt ℝ (fun p => U_inv p i j) x)
  (h_inv : ∀ p, U p * U_inv p = 1) :
  U x * partialDerivMat μ U_inv x = - partialDerivMat μ U x * U_inv x := by
  have hd_mul := partialDerivMat_mul U U_inv μ x hU_smooth hUinv_smooth
  have h_const : partialDerivMat μ (fun p => U p * U_inv p) x = 0 := by
    have h_eq : (fun p => U p * U_inv p) = fun _ => 1 := by ext p; rw [h_inv p]
    rw [h_eq]
    exact partialDerivMat_const 1 μ x
  rw [h_const] at hd_mul
  have h_zero : partialDerivMat μ U x * U_inv x + U x * partialDerivMat μ U_inv x = 0 := hd_mul.symm
  calc U x * partialDerivMat μ U_inv x = (partialDerivMat μ U x * U_inv x + U x * partialDerivMat μ U_inv x) - partialDerivMat μ U x * U_inv x := by abel
    _ = 0 - partialDerivMat μ U x * U_inv x := by rw [h_zero]
    _ = - partialDerivMat μ U x * U_inv x := by simp only [zero_sub, neg_mul]

lemma diff_partial (f : SpacetimePoint → ℂ) (h : ContDiff ℝ ⊤ f) (μ : Fin 4) (x : SpacetimePoint) :
  DifferentiableAt ℝ (fun p => partialDeriv μ f p) x := by
  have h_deriv_smooth : ContDiff ℝ 1 (fderiv ℝ f) := h.fderiv_right (by decide)
  have hd_deriv : DifferentiableAt ℝ (fderiv ℝ f) x := (h_deriv_smooth.differentiable (by decide)) x
  have h_apply : (fun p => partialDeriv μ f p) = (ContinuousLinearMap.apply ℝ ℂ ((Pi.single μ (1 : ℝ)) : Fin 4 → ℝ)) ∘ (fderiv ℝ f) := rfl
  rw [h_apply]
  exact DifferentiableAt.comp x (ContinuousLinearMap.apply ℝ ℂ ((Pi.single μ (1 : ℝ)) : Fin 4 → ℝ)).differentiableAt hd_deriv

lemma diff_partial_mat (f : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (h : ∀ i j, ContDiff ℝ ⊤ (fun p => f p i j)) (μ : Fin 4) (x : SpacetimePoint) :
  ∀ i j, DifferentiableAt ℝ (fun p => partialDerivMat μ f p i j) x := by
  intro i j
  have h_eq : (fun p => partialDerivMat μ f p i j) = fun p => partialDeriv μ (fun p2 => f p2 i j) p := rfl
  rw [h_eq]
  exact diff_partial (fun p => f p i j) (h i j) μ x

lemma matrix_linear_sub (U A B V : Matrix (Fin 2) (Fin 2) ℂ) :
  U * A * V - U * B * V = U * (A - B) * V := by
  calc U * A * V - U * B * V
    _ = (U * A) * V - (U * B) * V := rfl
    _ = (U * A - U * B) * V := by rw [sub_mul]
    _ = (U * (A - B)) * V := by rw [mul_sub]
    _ = U * (A - B) * V := rfl

lemma matrix_linear_add (U A B V : Matrix (Fin 2) (Fin 2) ℂ) :
  U * A * V + U * B * V = U * (A + B) * V := by
  calc U * A * V + U * B * V
    _ = (U * A) * V + (U * B) * V := rfl
    _ = (U * A + U * B) * V := by rw [add_mul]
    _ = (U * (A + B)) * V := by rw [mul_add]
    _ = U * (A + B) * V := rfl

lemma matrix_gauge_mul (U V A_mu A_nu dV_mu dV_nu dU_mu : Matrix (Fin 2) (Fin 2) ℂ)
  (hVU : V * U = 1) (hdV : U * dV_mu = - dU_mu * V) :
  (U * A_mu * V + U * dV_mu) * (U * A_nu * V + U * dV_nu) =
  U * (A_mu * A_nu) * V + U * A_mu * dV_nu - dU_mu * A_nu * V - dU_mu * dV_nu := by
  simp only [add_mul, mul_add]
  have h1 : U * A_mu * V * (U * A_nu * V) = U * (A_mu * A_nu) * V := by
    calc U * A_mu * V * (U * A_nu * V)
      _ = U * A_mu * (V * U) * A_nu * V := by simp only [Matrix.mul_assoc]
      _ = U * A_mu * 1 * A_nu * V := by rw [hVU]
      _ = U * (A_mu * A_nu) * V := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  have h2 : U * A_mu * V * (U * dV_nu) = U * A_mu * dV_nu := by
    calc U * A_mu * V * (U * dV_nu)
      _ = U * A_mu * (V * U) * dV_nu := by simp only [Matrix.mul_assoc]
      _ = U * A_mu * 1 * dV_nu := by rw [hVU]
      _ = U * A_mu * dV_nu := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  have h3 : U * dV_mu * (U * A_nu * V) = - (dU_mu * A_nu * V) := by
    calc U * dV_mu * (U * A_nu * V)
      _ = (U * dV_mu) * U * A_nu * V := by simp only [Matrix.mul_assoc]
      _ = (- dU_mu * V) * U * A_nu * V := by rw [hdV]
      _ = - (dU_mu * V) * U * A_nu * V := by simp only [neg_mul]
      _ = - (dU_mu * (V * U) * A_nu * V) := by simp only [neg_mul, Matrix.mul_assoc]
      _ = - (dU_mu * 1 * A_nu * V) := by rw [hVU]
      _ = - (dU_mu * A_nu * V) := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  have h4 : U * dV_mu * (U * dV_nu) = - (dU_mu * dV_nu) := by
    calc U * dV_mu * (U * dV_nu)
      _ = (U * dV_mu) * U * dV_nu := by simp only [Matrix.mul_assoc]
      _ = (- dU_mu * V) * U * dV_nu := by rw [hdV]
      _ = - (dU_mu * V) * U * dV_nu := by simp only [neg_mul]
      _ = - (dU_mu * (V * U) * dV_nu) := by simp only [neg_mul, Matrix.mul_assoc]
      _ = - (dU_mu * 1 * dV_nu) := by rw [hVU]
      _ = - (dU_mu * dV_nu) := by simp only [Matrix.mul_one]
  rw [h1, h2, h3, h4]
  simp only [sub_eq_add_neg, neg_mul]
  abel

lemma gauge_algebra_simplify (U V A_mu A_nu dA_nu dU_mu dV_mu dV_nu ddV : Matrix (Fin 2) (Fin 2) ℂ) :
  (dU_mu * A_nu * V + U * dA_nu * V + U * A_nu * dV_mu + (dU_mu * dV_nu + U * ddV)) +
  (U * (A_mu * A_nu) * V + U * A_mu * dV_nu - dU_mu * A_nu * V - dU_mu * dV_nu)
  =
  U * dA_nu * V + U * A_nu * dV_mu + U * ddV + U * (A_mu * A_nu) * V + U * A_mu * dV_nu := by
  abel

lemma gauge_algebra_antisymm (U V dA_nu dA_mu dV_mu dV_nu ddV A_mu A_nu : Matrix (Fin 2) (Fin 2) ℂ) :
  (U * dA_nu * V + U * A_nu * dV_mu + U * ddV + U * (A_mu * A_nu) * V + U * A_mu * dV_nu) -
  (U * dA_mu * V + U * A_mu * dV_nu + U * ddV + U * (A_nu * A_mu) * V + U * A_nu * dV_mu)
  =
  U * (dA_nu - dA_mu + (A_mu * A_nu - A_nu * A_mu)) * V := by
  simp only [mul_add, add_mul, mul_sub, sub_mul]
  abel

/-- 
A mathematically rigorous definition of a gauge transformation, requiring invertible and globally smooth mappings to preserve the integrity of the differential calculus.
-/
def isGaugeTransform (A B : Fin 4 → SpacetimePoint → SL2C) : Prop :=
  (∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j)) ∧
  ∃ U U_inv : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ, 
    (∀ i j, ContDiff ℝ ⊤ (fun x => (U x) i j)) ∧
    (∀ i j, ContDiff ℝ ⊤ (fun x => (U_inv x) i j)) ∧
    (∀ x, U x * U_inv x = 1) ∧
    (∀ x, U_inv x * U x = 1) ∧
    ∀ x mu, (B mu x).val = U x * (A mu x).val * U_inv x + U x * partialDerivMat mu U_inv x

lemma diff_UAV (U A V : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (x : SpacetimePoint)
  (hU : ∀ i j, DifferentiableAt ℝ (fun p => U p i j) x)
  (hA : ∀ i j, DifferentiableAt ℝ (fun p => A p i j) x)
  (hV : ∀ i j, DifferentiableAt ℝ (fun p => V p i j) x) :
  ∀ i j, DifferentiableAt ℝ (fun p => (U p * A p * V p) i j) x := by
  intro i j
  exact diff_matrix_mul (fun p => U p * A p) V x (diff_matrix_mul U A x hU hA) hV i j

lemma diff_UdV (U dV : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (x : SpacetimePoint)
  (hU : ∀ i j, DifferentiableAt ℝ (fun p => U p i j) x)
  (hdV : ∀ i j, DifferentiableAt ℝ (fun p => dV p i j) x) :
  ∀ i j, DifferentiableAt ℝ (fun p => (U p * dV p) i j) x := by
  intro i j
  exact diff_matrix_mul U dV x hU hdV i j

lemma d_mu_B_nu_expansion (mu nu : Fin 4) (x : SpacetimePoint)
  (A_nu : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ)
  (U U_inv : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ)
  (hdU : ∀ i j, DifferentiableAt ℝ (fun p => U p i j) x)
  (hdA_nu : ∀ i j, DifferentiableAt ℝ (fun p => A_nu p i j) x)
  (hdUinv : ∀ i j, DifferentiableAt ℝ (fun p => U_inv p i j) x)
  (hddUinv_nu : ∀ i j, DifferentiableAt ℝ (fun p => partialDerivMat nu U_inv p i j) x) :
  partialDerivMat mu (fun p => U p * A_nu p * U_inv p + U p * partialDerivMat nu U_inv p) x =
  partialDerivMat mu U x * A_nu x * U_inv x + 
  U x * partialDerivMat mu A_nu x * U_inv x + 
  U x * A_nu x * partialDerivMat mu U_inv x + 
  (partialDerivMat mu U x * partialDerivMat nu U_inv x + U x * partialDerivMat mu (fun p => partialDerivMat nu U_inv p) x) := by
  have h_left_diff := diff_UAV U A_nu U_inv x hdU hdA_nu hdUinv
  have h_right_diff := diff_UdV U (fun p => partialDerivMat nu U_inv p) x hdU hddUinv_nu
  rw [partialDerivMat_add (fun p => U p * A_nu p * U_inv p) (fun p => U p * partialDerivMat nu U_inv p) mu x h_left_diff h_right_diff]
  rw [partialDerivMat_mul3 mu U A_nu U_inv x hdU hdA_nu hdUinv]
  rw [partialDerivMat_mul U (fun p => partialDerivMat nu U_inv p) mu x hdU hddUinv_nu]

lemma partialDeriv_add (μ : Fin 4) (f g : SpacetimePoint → ℂ) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
  partialDeriv μ (fun p => f p + g p) x = partialDeriv μ f x + partialDeriv μ g x := by
  unfold partialDeriv
  have h_add_def : (fun p => f p + g p) = f + g := rfl
  rw [h_add_def]
  rw [fderiv_add hf hg]
  exact ContinuousLinearMap.add_apply (fderiv ℝ f x) (fderiv ℝ g x) ((Pi.single μ (1 : ℝ)) : Fin 4 → ℝ)

lemma trace_partialDerivMat (μ : Fin 4) (F : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (x : SpacetimePoint)
  (hF00 : DifferentiableAt ℝ (fun p => F p 0 0) x)
  (hF11 : DifferentiableAt ℝ (fun p => F p 1 1) x) :
  Matrix.trace (partialDerivMat μ F x) = partialDeriv μ (fun p => Matrix.trace (F p)) x := by
  have h_tr_d : Matrix.trace (partialDerivMat μ F x) = partialDerivMat μ F x 0 0 + partialDerivMat μ F x 1 1 := by rw [Matrix.trace_fin_two]
  have h_tr_f : (fun p => Matrix.trace (F p)) = fun p => F p 0 0 + F p 1 1 := by funext p; rw [Matrix.trace_fin_two]
  rw [h_tr_d, h_tr_f]
  unfold partialDerivMat
  rw [partialDeriv_add μ (fun p => F p 0 0) (fun p => F p 1 1) x hF00 hF11]

lemma toSl2c_val (M : Matrix (Fin 2) (Fin 2) ℂ) :
  (toSl2c M).val = M - (Matrix.trace M / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl

lemma partialDerivSl2c_val_eq (μ : Fin 4) (A : SpacetimePoint → SL2C) (x : SpacetimePoint)
  (hA00 : DifferentiableAt ℝ (fun p => (A p).val 0 0) x)
  (hA11 : DifferentiableAt ℝ (fun p => (A p).val 1 1) x) :
  (partialDerivSl2c μ A x).val = partialDerivMat μ (fun p => (A p).val) x := by
  unfold partialDerivSl2c
  rw [toSl2c_val]
  have h_trace : Matrix.trace (partialDerivMat μ (fun p => (A p).val) x) = 0 := by
    rw [trace_partialDerivMat μ (fun p => (A p).val) x hA00 hA11]
    have hA_trace_zero : ∀ p, Matrix.trace ((A p).val) = 0 := by
      intro p
      have hp : (A p).val ∈ sl2cAlgebra := (A p).property
      rw [mem_sl_iff] at hp
      exact hp
    have h_trace_f : (fun p => Matrix.trace ((A p).val)) = fun p => 0 := by funext p; rw [hA_trace_zero p]
    rw [h_trace_f]
    exact partialDeriv_const 0 μ x
  rw [h_trace]
  have h_zero_div : (0 : ℂ) / 2 = 0 := by ring
  rw [h_zero_div]
  have h_zero_smul : (0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := zero_smul ℂ 1
  rw [h_zero_smul]
  exact sub_zero (partialDerivMat μ (fun p => (A p).val) x)

lemma curvature_val_expansion (A : Fin 4 → SpacetimePoint → SL2C) (mu nu : Fin 4) (x : SpacetimePoint)
  (hA_smooth_mu : ∀ i j, DifferentiableAt ℝ (fun p => (A mu p).val i j) x)
  (hA_smooth_nu : ∀ i j, DifferentiableAt ℝ (fun p => (A nu p).val i j) x) :
  (curvatureSl2c A mu nu x).val = 
    partialDerivMat mu (fun p => (A nu p).val) x - 
    partialDerivMat nu (fun p => (A mu p).val) x + 
    ((A mu x).val * (A nu x).val - (A nu x).val * (A mu x).val) := by
  rw [curvatureSl2c_def]
  have h2 : (partialDerivSl2c mu (A nu) x - partialDerivSl2c nu (A mu) x + ⁅A mu x, A nu x⁆).val = 
    (partialDerivSl2c mu (A nu) x).val - (partialDerivSl2c nu (A mu) x).val + ⁅A mu x, A nu x⁆.val := rfl
  rw [h2]
  have hd_mu_eq := partialDerivSl2c_val_eq mu (A nu) x (hA_smooth_nu 0 0) (hA_smooth_nu 1 1)
  have hd_nu_eq := partialDerivSl2c_val_eq nu (A mu) x (hA_smooth_mu 0 0) (hA_smooth_mu 1 1)
  rw [hd_mu_eq, hd_nu_eq]
  have h3 : ⁅A mu x, A nu x⁆.val = (A mu x).val * (A nu x).val - (A nu x).val * (A mu x).val := by
    change ⁅(A mu x).val, (A nu x).val⁆ = (A mu x).val * (A nu x).val - (A nu x).val * (A mu x).val
    exact Ring.lie_def ((A mu x).val) ((A nu x).val)
  rw [h3]

lemma gauge_curvature_covariance (A B : Fin 4 → SpacetimePoint → SL2C)
  (hA_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (U U_inv : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ)
  (hU_smooth : ∀ i j, ContDiff ℝ ⊤ (fun x => (U x) i j))
  (hUinv_smooth : ∀ i j, ContDiff ℝ ⊤ (fun x => (U_inv x) i j))
  (h_inv1 : ∀ x, U x * U_inv x = 1)
  (h_inv2 : ∀ x, U_inv x * U x = 1)
  (h_B : ∀ x mu, (B mu x).val = U x * (A mu x).val * U_inv x + U x * partialDerivMat mu U_inv x) :
  ∀ x mu nu, (curvatureSl2c B mu nu x).val = U x * (curvatureSl2c A mu nu x).val * U_inv x := by
  intro x mu nu
  
  have hdU : ∀ i j, DifferentiableAt ℝ (fun p => (U p) i j) x := fun i j => (hU_smooth i j).differentiable (by decide) x
  have hdUinv : ∀ i j, DifferentiableAt ℝ (fun p => (U_inv p) i j) x := fun i j => (hUinv_smooth i j).differentiable (by decide) x
  have hdA_mu : ∀ i j, DifferentiableAt ℝ (fun p => (A mu p).val i j) x := fun i j => (hA_smooth mu i j).differentiable (by decide) x
  have hdA_nu : ∀ i j, DifferentiableAt ℝ (fun p => (A nu p).val i j) x := fun i j => (hA_smooth nu i j).differentiable (by decide) x
  have hddUinv_mu : ∀ i j, DifferentiableAt ℝ (fun p => partialDerivMat mu U_inv p i j) x := diff_partial_mat U_inv hUinv_smooth mu x
  have hddUinv_nu : ∀ i j, DifferentiableAt ℝ (fun p => partialDerivMat nu U_inv p i j) x := diff_partial_mat U_inv hUinv_smooth nu x
  
  let U_x := U x
  let V_x := U_inv x
  let A_mu := (A mu x).val
  let A_nu := (A nu x).val
  let d_mu_A_nu := partialDerivMat mu (fun p => (A nu p).val) x
  let d_nu_A_mu := partialDerivMat nu (fun p => (A mu p).val) x
  let d_mu_U := partialDerivMat mu U x
  let d_nu_U := partialDerivMat nu U x
  let d_mu_V := partialDerivMat mu U_inv x
  let d_nu_V := partialDerivMat nu U_inv x
  let d_mu_d_nu_V := partialDerivMat mu (fun p => partialDerivMat nu U_inv p) x
  let d_nu_d_mu_V := partialDerivMat nu (fun p => partialDerivMat mu U_inv p) x
  
  have hdB_nu : partialDerivMat mu (fun p => (B nu p).val) x = d_mu_U * A_nu * V_x + U_x * d_mu_A_nu * V_x + U_x * A_nu * d_mu_V + (d_mu_U * d_nu_V + U_x * d_mu_d_nu_V) := by
    have h_B_nu_eq : (fun p => (B nu p).val) = fun p => U p * (A nu p).val * U_inv p + U p * partialDerivMat nu U_inv p := funext (fun p => h_B p nu)
    rw [h_B_nu_eq]
    exact d_mu_B_nu_expansion mu nu x (fun p => (A nu p).val) U U_inv hdU hdA_nu hdUinv hddUinv_nu
      
  have hdB_mu : partialDerivMat nu (fun p => (B mu p).val) x = d_nu_U * A_mu * V_x + U_x * d_nu_A_mu * V_x + U_x * A_mu * d_nu_V + (d_nu_U * d_mu_V + U_x * d_nu_d_mu_V) := by
    have h_B_mu_eq : (fun p => (B mu p).val) = fun p => U p * (A mu p).val * U_inv p + U p * partialDerivMat mu U_inv p := funext (fun p => h_B p mu)
    rw [h_B_mu_eq]
    exact d_mu_B_nu_expansion nu mu x (fun p => (A mu p).val) U U_inv hdU hdA_mu hdUinv hddUinv_mu
      
  have h_B_mu_B_nu : (B mu x).val * (B nu x).val = U_x * (A_mu * A_nu) * V_x + U_x * A_mu * d_nu_V - d_mu_U * A_nu * V_x - d_mu_U * d_nu_V := by
    have h1 : (B mu x).val = U_x * A_mu * V_x + U_x * d_mu_V := h_B x mu
    have h2 : (B nu x).val = U_x * A_nu * V_x + U_x * d_nu_V := h_B x nu
    rw [h1, h2]
    exact matrix_gauge_mul U_x V_x A_mu A_nu d_mu_V d_nu_V d_mu_U (h_inv2 x) (diff_inv_identity mu U U_inv x hdU hdUinv h_inv1)
    
  have h_B_nu_B_mu : (B nu x).val * (B mu x).val = U_x * (A_nu * A_mu) * V_x + U_x * A_nu * d_mu_V - d_nu_U * A_mu * V_x - d_nu_U * d_mu_V := by
    have h1 : (B nu x).val = U_x * A_nu * V_x + U_x * d_nu_V := h_B x nu
    have h2 : (B mu x).val = U_x * A_mu * V_x + U_x * d_mu_V := h_B x mu
    rw [h1, h2]
    exact matrix_gauge_mul U_x V_x A_nu A_mu d_nu_V d_mu_V d_nu_U (h_inv2 x) (diff_inv_identity nu U U_inv x hdU hdUinv h_inv1)

  have h_sum_nu : partialDerivMat mu (fun p => (B nu p).val) x + (B mu x).val * (B nu x).val = U_x * d_mu_A_nu * V_x + U_x * A_nu * d_mu_V + U_x * d_mu_d_nu_V + U_x * (A_mu * A_nu) * V_x + U_x * A_mu * d_nu_V := by
    rw [hdB_nu, h_B_mu_B_nu]
    exact gauge_algebra_simplify U_x V_x A_mu A_nu d_mu_A_nu d_mu_U d_mu_V d_nu_V d_mu_d_nu_V
    
  have h_sum_mu : partialDerivMat nu (fun p => (B mu p).val) x + (B nu x).val * (B mu x).val = U_x * d_nu_A_mu * V_x + U_x * A_mu * d_nu_V + U_x * d_nu_d_mu_V + U_x * (A_nu * A_mu) * V_x + U_x * A_nu * d_mu_V := by
    rw [hdB_mu, h_B_nu_B_mu]
    exact gauge_algebra_simplify U_x V_x A_nu A_mu d_nu_A_mu d_nu_U d_nu_V d_mu_V d_nu_d_mu_V
    
  have h_schwarz : d_mu_d_nu_V = d_nu_d_mu_V := partialDerivMat_commutes U_inv mu nu x hUinv_smooth

  have h_eval : U_x * d_mu_A_nu * V_x + U_x * A_nu * d_mu_V + U_x * d_mu_d_nu_V + U_x * (A_mu * A_nu) * V_x + U_x * A_mu * d_nu_V - (U_x * d_nu_A_mu * V_x + U_x * A_mu * d_nu_V + U_x * d_nu_d_mu_V + U_x * (A_nu * A_mu) * V_x + U_x * A_nu * d_mu_V) = U_x * (d_mu_A_nu - d_nu_A_mu + (A_mu * A_nu - A_nu * A_mu)) * V_x := by
    rw [h_schwarz]
    exact gauge_algebra_antisymm U_x V_x d_mu_A_nu d_nu_A_mu d_mu_V d_nu_V d_nu_d_mu_V A_mu A_nu

  have hdB_mu_smooth : ∀ i j, DifferentiableAt ℝ (fun p => (B mu p).val i j) x := by
    intro i j
    have h_B_mu_eq : (fun p => (B mu p).val i j) = fun p => (U p * (A mu p).val * U_inv p + U p * partialDerivMat mu U_inv p) i j := by funext p; rw [h_B p mu]
    rw [h_B_mu_eq]
    have hleft := diff_UAV U (fun p => (A mu p).val) U_inv x hdU hdA_mu hdUinv
    have hright := diff_UdV U (fun p => partialDerivMat mu U_inv p) x hdU hddUinv_mu
    exact DifferentiableAt.add (hleft i j) (hright i j)

  have hdB_nu_smooth : ∀ i j, DifferentiableAt ℝ (fun p => (B nu p).val i j) x := by
    intro i j
    have h_B_nu_eq : (fun p => (B nu p).val i j) = fun p => (U p * (A nu p).val * U_inv p + U p * partialDerivMat nu U_inv p) i j := by funext p; rw [h_B p nu]
    rw [h_B_nu_eq]
    have hleft := diff_UAV U (fun p => (A nu p).val) U_inv x hdU hdA_nu hdUinv
    have hright := diff_UdV U (fun p => partialDerivMat nu U_inv p) x hdU hddUinv_nu
    exact DifferentiableAt.add (hleft i j) (hright i j)

  calc (curvatureSl2c B mu nu x).val 
    _ = partialDerivMat mu (fun p => (B nu p).val) x - partialDerivMat nu (fun p => (B mu p).val) x + ((B mu x).val * (B nu x).val - (B nu x).val * (B mu x).val) := curvature_val_expansion B mu nu x hdB_mu_smooth hdB_nu_smooth
    _ = (partialDerivMat mu (fun p => (B nu p).val) x + (B mu x).val * (B nu x).val) - (partialDerivMat nu (fun p => (B mu p).val) x + (B nu x).val * (B mu x).val) := by abel
    _ = U_x * d_mu_A_nu * V_x + U_x * A_nu * d_mu_V + U_x * d_mu_d_nu_V + U_x * (A_mu * A_nu) * V_x + U_x * A_mu * d_nu_V - (U_x * d_nu_A_mu * V_x + U_x * A_mu * d_nu_V + U_x * d_nu_d_mu_V + U_x * (A_nu * A_mu) * V_x + U_x * A_nu * d_mu_V) := by rw [h_sum_nu, h_sum_mu]
    _ = U_x * (d_mu_A_nu - d_nu_A_mu + (A_mu * A_nu - A_nu * A_mu)) * V_x := h_eval
    _ = U_x * (partialDerivMat mu (fun p => (A nu p).val) x - partialDerivMat nu (fun p => (A mu p).val) x + ((A mu x).val * (A nu x).val - (A nu x).val * (A mu x).val)) * V_x := by rfl
    _ = U_x * (curvatureSl2c A mu nu x).val * V_x := by rw [← curvature_val_expansion A mu nu x hdA_mu hdA_nu]

Litlib.theorem
  description "Gauge Invariance of the Curvature Trace"
/--
The trace of the square of the curvature tensor is invariant under gauge transformations.
-/
theorem gauge_transform_curvature_trace (A B : Fin 4 → SpacetimePoint → SL2C) :
  isGaugeTransform A B →
  ∀ x mu nu, Matrix.trace ((curvatureSl2c A mu nu x).val * (curvatureSl2c A mu nu x).val) =
             Matrix.trace ((curvatureSl2c B mu nu x).val * (curvatureSl2c B mu nu x).val) := by
  intro h x mu nu
  rcases h with ⟨hA_smooth, U, U_inv, hU_smooth, hUinv_smooth, h_inv1, h_inv2, h_B⟩
  have hcov := gauge_curvature_covariance A B hA_smooth U U_inv hU_smooth hUinv_smooth h_inv1 h_inv2 h_B x mu nu
  
  let A_x := (curvatureSl2c A mu nu x).val
  let B_x := (curvatureSl2c B mu nu x).val
  let U_x := U x
  let Uinv_x := U_inv x
  
  have h_B_eq : B_x = U_x * A_x * Uinv_x := hcov
  
  have h_B_B : B_x * B_x = U_x * (A_x * A_x) * Uinv_x := by
    calc B_x * B_x = (U_x * A_x * Uinv_x) * (U_x * A_x * Uinv_x) := by rw [h_B_eq]
      _ = U_x * A_x * (Uinv_x * U_x) * A_x * Uinv_x := by simp only [Matrix.mul_assoc]
      _ = U_x * A_x * 1 * A_x * Uinv_x := by rw [h_inv2 x]
      _ = U_x * (A_x * A_x) * Uinv_x := by simp only [Matrix.mul_one, Matrix.mul_assoc]
      
  symm
  calc Matrix.trace (B_x * B_x) = Matrix.trace (U_x * (A_x * A_x) * Uinv_x) := by rw [h_B_B]
    _ = Matrix.trace (U_x * ((A_x * A_x) * Uinv_x)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (((A_x * A_x) * Uinv_x) * U_x) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((A_x * A_x) * (Uinv_x * U_x)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace ((A_x * A_x) * 1) := by rw [h_inv2 x]
    _ = Matrix.trace (A_x * A_x) := by rw [Matrix.mul_one]

end CGD.Foundations

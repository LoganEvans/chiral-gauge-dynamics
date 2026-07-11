-- FILENAME: CGD/Foundations/TensorCalculus/GaugeTransform/CalculusHelpers.lean

import Litlib.Core
import CGD.Foundations.TensorCalculus.DifferentialRules
import CGD.Foundations.Calculus
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Algebra.Lie.Classical

set_option linter.unusedSimpArgs false

open Matrix Complex BigOperators Litlib.Y2003.nakahara2003geometry

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
      have hp : (A p).val ∈ LieAlgebra.SpecialLinear.sl (Fin 2) Complex := (A p).property
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

end CGD.Foundations

-- FILENAME: CGD/Gravity/MacroscopicVacuum/WMatrix.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology
import CGD.Gravity.MacroscopicVacuum.Basic
import Litlib.Y1989.capovilla1989general.Signature

set_option autoImplicit false
set_option linter.unusedVariables false

open Complex Matrix BigOperators
open CGD.Axioms CGD.Foundations Litlib Classical
open Litlib.Y1989.capovilla1989general

namespace CGD.Gravity

lemma cgdAdjointCurvature_mul_00 (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 0 0 = - F_CGD u x 2 μ ν * F_CGD u x 2 ρ σ - F_CGD u x 1 μ ν * F_CGD u x 1 ρ σ := by
  rw [Matrix.mul_apply, fin3_sum]
  rw [cgd_eval_00, cgd_eval_01, cgd_eval_02, cgd_eval_10, cgd_eval_20]
  ring

lemma cgdAdjointCurvature_mul_01 (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 0 1 = F_CGD u x 1 μ ν * F_CGD u x 0 ρ σ := by
  rw [Matrix.mul_apply, fin3_sum]
  rw [cgd_eval_00, cgd_eval_01, cgd_eval_02, cgd_eval_11, cgd_eval_21]
  ring

lemma cgdAdjointCurvature_mul_02 (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 0 2 = F_CGD u x 2 μ ν * F_CGD u x 0 ρ σ := by
  rw [Matrix.mul_apply, fin3_sum]
  rw [cgd_eval_00, cgd_eval_01, cgd_eval_02, cgd_eval_12, cgd_eval_22]
  ring

lemma cgdAdjointCurvature_mul_10 (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 1 0 = F_CGD u x 0 μ ν * F_CGD u x 1 ρ σ := by
  rw [Matrix.mul_apply, fin3_sum]
  rw [cgd_eval_10, cgd_eval_11, cgd_eval_12, cgd_eval_00, cgd_eval_20]
  ring

lemma cgdAdjointCurvature_mul_11 (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 1 1 = - F_CGD u x 2 μ ν * F_CGD u x 2 ρ σ - F_CGD u x 0 μ ν * F_CGD u x 0 ρ σ := by
  rw [Matrix.mul_apply, fin3_sum]
  rw [cgd_eval_10, cgd_eval_11, cgd_eval_12, cgd_eval_01, cgd_eval_21]
  ring

lemma cgdAdjointCurvature_mul_12 (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 1 2 = F_CGD u x 2 μ ν * F_CGD u x 1 ρ σ := by
  rw [Matrix.mul_apply, fin3_sum]
  rw [cgd_eval_10, cgd_eval_11, cgd_eval_12, cgd_eval_02, cgd_eval_22]
  ring

lemma cgdAdjointCurvature_mul_20 (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 2 0 = F_CGD u x 0 μ ν * F_CGD u x 2 ρ σ := by
  rw [Matrix.mul_apply, fin3_sum]
  rw [cgd_eval_20, cgd_eval_21, cgd_eval_22, cgd_eval_00, cgd_eval_10]
  ring

lemma cgdAdjointCurvature_mul_21 (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 2 1 = F_CGD u x 1 μ ν * F_CGD u x 2 ρ σ := by
  rw [Matrix.mul_apply, fin3_sum]
  rw [cgd_eval_20, cgd_eval_21, cgd_eval_22, cgd_eval_01, cgd_eval_11]
  ring

lemma cgdAdjointCurvature_mul_22 (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 2 2 = - F_CGD u x 1 μ ν * F_CGD u x 1 ρ σ - F_CGD u x 0 μ ν * F_CGD u x 0 ρ σ := by
  rw [Matrix.mul_apply, fin3_sum]
  rw [cgd_eval_20, cgd_eval_21, cgd_eval_22, cgd_eval_02, cgd_eval_12]
  ring

noncomputable def W (u : Universe) (x : SpacetimePoint) (a b : Fin 3) : ℂ :=
  wedgeContract (F_CGD u x a) (F_CGD u x b) epsilon4

lemma sum_quad_congr (f g : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) (h : ∀ μ ν ρ σ, f μ ν ρ σ = g μ ν ρ σ) :
  (∑ μ, ∑ ν, ∑ ρ, ∑ σ, f μ ν ρ σ) = (∑ μ, ∑ ν, ∑ ρ, ∑ σ, g μ ν ρ σ) := by
  apply Finset.sum_congr rfl; intro μ _
  apply Finset.sum_congr rfl; intro ν _
  apply Finset.sum_congr rfl; intro ρ _
  apply Finset.sum_congr rfl; intro σ _
  exact h μ ν ρ σ

lemma h_comp_lemma (u : Universe) (x : SpacetimePoint) 
  (h_cdj : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = 0) (i j : Fin 3) :
  (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) i j) = 0 := by
  have h1 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) i j = 0 := by rw [h_cdj]; rfl
  exact h1

lemma W_10_kernel_eq (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 0 1 = epsilon4 μ ν ρ σ * F_CGD u x 1 μ ν * F_CGD u x 0 ρ σ := by
  rw [cgdAdjointCurvature_mul_01]; ring

lemma W_10_eq_zero (u : Universe) (x : SpacetimePoint) (h_cdj : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = 0) : W u x 1 0 = 0 := by
  have h := h_comp_lemma u x h_cdj 0 1
  have h_eq : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 0 1) = W u x 1 0 := by
    unfold W wedgeContract
    apply sum_quad_congr; intro μ ν ρ σ
    exact W_10_kernel_eq u x μ ν ρ σ
  rwa [h_eq] at h

lemma W_01_kernel_eq (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 1 0 = epsilon4 μ ν ρ σ * F_CGD u x 0 μ ν * F_CGD u x 1 ρ σ := by
  rw [cgdAdjointCurvature_mul_10]; ring

lemma W_01_eq_zero (u : Universe) (x : SpacetimePoint) (h_cdj : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = 0) : W u x 0 1 = 0 := by
  have h := h_comp_lemma u x h_cdj 1 0
  have h_eq : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 1 0) = W u x 0 1 := by
    unfold W wedgeContract
    apply sum_quad_congr; intro μ ν ρ σ
    exact W_01_kernel_eq u x μ ν ρ σ
  rwa [h_eq] at h

lemma W_20_kernel_eq (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 0 2 = epsilon4 μ ν ρ σ * F_CGD u x 2 μ ν * F_CGD u x 0 ρ σ := by
  rw [cgdAdjointCurvature_mul_02]; ring

lemma W_20_eq_zero (u : Universe) (x : SpacetimePoint) (h_cdj : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = 0) : W u x 2 0 = 0 := by
  have h := h_comp_lemma u x h_cdj 0 2
  have h_eq : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 0 2) = W u x 2 0 := by
    unfold W wedgeContract
    apply sum_quad_congr; intro μ ν ρ σ
    exact W_20_kernel_eq u x μ ν ρ σ
  rwa [h_eq] at h

lemma W_02_kernel_eq (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 2 0 = epsilon4 μ ν ρ σ * F_CGD u x 0 μ ν * F_CGD u x 2 ρ σ := by
  rw [cgdAdjointCurvature_mul_20]; ring

lemma W_02_eq_zero (u : Universe) (x : SpacetimePoint) (h_cdj : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = 0) : W u x 0 2 = 0 := by
  have h := h_comp_lemma u x h_cdj 2 0
  have h_eq : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 2 0) = W u x 0 2 := by
    unfold W wedgeContract
    apply sum_quad_congr; intro μ ν ρ σ
    exact W_02_kernel_eq u x μ ν ρ σ
  rwa [h_eq] at h

lemma W_21_kernel_eq (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 1 2 = epsilon4 μ ν ρ σ * F_CGD u x 2 μ ν * F_CGD u x 1 ρ σ := by
  rw [cgdAdjointCurvature_mul_12]; ring

lemma W_21_eq_zero (u : Universe) (x : SpacetimePoint) (h_cdj : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = 0) : W u x 2 1 = 0 := by
  have h := h_comp_lemma u x h_cdj 1 2
  have h_eq : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 1 2) = W u x 2 1 := by
    unfold W wedgeContract
    apply sum_quad_congr; intro μ ν ρ σ
    exact W_21_kernel_eq u x μ ν ρ σ
  rwa [h_eq] at h

lemma W_12_kernel_eq (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 2 1 = epsilon4 μ ν ρ σ * F_CGD u x 1 μ ν * F_CGD u x 2 ρ σ := by
  rw [cgdAdjointCurvature_mul_21]; ring

lemma W_12_eq_zero (u : Universe) (x : SpacetimePoint) (h_cdj : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = 0) : W u x 1 2 = 0 := by
  have h := h_comp_lemma u x h_cdj 2 1
  have h_eq : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 2 1) = W u x 1 2 := by
    unfold W wedgeContract
    apply sum_quad_congr; intro μ ν ρ σ
    exact W_12_kernel_eq u x μ ν ρ σ
  rwa [h_eq] at h

lemma h_diag0_kernel_eq (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 0 0 = 
  - (epsilon4 μ ν ρ σ * F_CGD u x 2 μ ν * F_CGD u x 2 ρ σ) - (epsilon4 μ ν ρ σ * F_CGD u x 1 μ ν * F_CGD u x 1 ρ σ) := by
  rw [cgdAdjointCurvature_mul_00]; ring

lemma h_diag0_eq (u : Universe) (x : SpacetimePoint) :
  (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 0 0) = - W u x 2 2 - W u x 1 1 := by
  have h_kernel := sum_quad_congr 
    (fun μ ν ρ σ => epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 0 0)
    (fun μ ν ρ σ => - (epsilon4 μ ν ρ σ * F_CGD u x 2 μ ν * F_CGD u x 2 ρ σ) - (epsilon4 μ ν ρ σ * F_CGD u x 1 μ ν * F_CGD u x 1 ρ σ))
    (h_diag0_kernel_eq u x)
  rw [h_kernel]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hw2 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * F_CGD u x 2 μ ν * F_CGD u x 2 ρ σ) = W u x 2 2 := rfl
  have hw1 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * F_CGD u x 1 μ ν * F_CGD u x 1 ρ σ) = W u x 1 1 := rfl
  rw [hw2, hw1]

lemma h_diag1_kernel_eq (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 1 1 = 
  - (epsilon4 μ ν ρ σ * F_CGD u x 2 μ ν * F_CGD u x 2 ρ σ) - (epsilon4 μ ν ρ σ * F_CGD u x 0 μ ν * F_CGD u x 0 ρ σ) := by
  rw [cgdAdjointCurvature_mul_11]; ring

lemma h_diag1_eq (u : Universe) (x : SpacetimePoint) :
  (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 1 1) = - W u x 2 2 - W u x 0 0 := by
  have h_kernel := sum_quad_congr 
    (fun μ ν ρ σ => epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 1 1)
    (fun μ ν ρ σ => - (epsilon4 μ ν ρ σ * F_CGD u x 2 μ ν * F_CGD u x 2 ρ σ) - (epsilon4 μ ν ρ σ * F_CGD u x 0 μ ν * F_CGD u x 0 ρ σ))
    (h_diag1_kernel_eq u x)
  rw [h_kernel]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hw2 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * F_CGD u x 2 μ ν * F_CGD u x 2 ρ σ) = W u x 2 2 := rfl
  have hw0 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * F_CGD u x 0 μ ν * F_CGD u x 0 ρ σ) = W u x 0 0 := rfl
  rw [hw2, hw0]

lemma h_diag2_kernel_eq (u : Universe) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 2 2 = 
  - (epsilon4 μ ν ρ σ * F_CGD u x 1 μ ν * F_CGD u x 1 ρ σ) - (epsilon4 μ ν ρ σ * F_CGD u x 0 μ ν * F_CGD u x 0 ρ σ) := by
  rw [cgdAdjointCurvature_mul_22]; ring

lemma h_diag2_eq (u : Universe) (x : SpacetimePoint) :
  (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 2 2) = - W u x 1 1 - W u x 0 0 := by
  have h_kernel := sum_quad_congr 
    (fun μ ν ρ σ => epsilon4 μ ν ρ σ * (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x) 2 2)
    (fun μ ν ρ σ => - (epsilon4 μ ν ρ σ * F_CGD u x 1 μ ν * F_CGD u x 1 ρ σ) - (epsilon4 μ ν ρ σ * F_CGD u x 0 μ ν * F_CGD u x 0 ρ σ))
    (h_diag2_kernel_eq u x)
  rw [h_kernel]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hw1 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * F_CGD u x 1 μ ν * F_CGD u x 1 ρ σ) = W u x 1 1 := rfl
  have hw0 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * F_CGD u x 0 μ ν * F_CGD u x 0 ρ σ) = W u x 0 0 := rfl
  rw [hw1, hw0]

lemma W_22_eq_zero (u : Universe) (x : SpacetimePoint) (h_cdj : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = 0) : W u x 2 2 = 0 := by
  have h0 := h_comp_lemma u x h_cdj 0 0
  have h1 := h_comp_lemma u x h_cdj 1 1
  have h2 := h_comp_lemma u x h_cdj 2 2
  rw [h_diag0_eq] at h0
  rw [h_diag1_eq] at h1
  rw [h_diag2_eq] at h2
  have hs : (- W u x 2 2 - W u x 1 1) + (- W u x 2 2 - W u x 0 0) - (- W u x 1 1 - W u x 0 0) = 0 := by rw [h0, h1, h2]; ring
  have h_eq : (- W u x 2 2 - W u x 1 1) + (- W u x 2 2 - W u x 0 0) - (- W u x 1 1 - W u x 0 0) = - 2 * W u x 2 2 := by ring
  rw [h_eq] at hs
  cases mul_eq_zero.mp hs with
  | inl h => norm_num at h
  | inr h => exact h

lemma W_11_eq_zero (u : Universe) (x : SpacetimePoint) (h_cdj : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = 0) : W u x 1 1 = 0 := by
  have h0 := h_comp_lemma u x h_cdj 0 0
  have h1 := h_comp_lemma u x h_cdj 1 1
  have h2 := h_comp_lemma u x h_cdj 2 2
  rw [h_diag0_eq] at h0
  rw [h_diag1_eq] at h1
  rw [h_diag2_eq] at h2
  have hs : (- W u x 2 2 - W u x 1 1) + (- W u x 1 1 - W u x 0 0) - (- W u x 2 2 - W u x 0 0) = 0 := by rw [h0, h2, h1]; ring
  have h_eq : (- W u x 2 2 - W u x 1 1) + (- W u x 1 1 - W u x 0 0) - (- W u x 2 2 - W u x 0 0) = - 2 * W u x 1 1 := by ring
  rw [h_eq] at hs
  cases mul_eq_zero.mp hs with
  | inl h => norm_num at h
  | inr h => exact h

lemma W_00_eq_zero (u : Universe) (x : SpacetimePoint) (h_cdj : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = 0) : W u x 0 0 = 0 := by
  have h0 := h_comp_lemma u x h_cdj 0 0
  have h1 := h_comp_lemma u x h_cdj 1 1
  have h2 := h_comp_lemma u x h_cdj 2 2
  rw [h_diag0_eq] at h0
  rw [h_diag1_eq] at h1
  rw [h_diag2_eq] at h2
  have hs : (- W u x 2 2 - W u x 0 0) + (- W u x 1 1 - W u x 0 0) - (- W u x 2 2 - W u x 1 1) = 0 := by rw [h1, h2, h0]; ring
  have h_eq : (- W u x 2 2 - W u x 0 0) + (- W u x 1 1 - W u x 0 0) - (- W u x 2 2 - W u x 1 1) = - 2 * W u x 0 0 := by ring
  rw [h_eq] at hs
  cases mul_eq_zero.mp hs with
  | inl h => norm_num at h
  | inr h => exact h

lemma W_eq_zero (u : Universe) (x : SpacetimePoint)
  (h_cdj : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = 0) :
  ∀ a b : Fin 3, W u x a b = 0 := by
  intros a b
  fin_cases a <;> fin_cases b
  · exact W_00_eq_zero u x h_cdj
  · exact W_01_eq_zero u x h_cdj
  · exact W_02_eq_zero u x h_cdj
  · exact W_10_eq_zero u x h_cdj
  · exact W_11_eq_zero u x h_cdj
  · exact W_12_eq_zero u x h_cdj
  · exact W_20_eq_zero u x h_cdj
  · exact W_21_eq_zero u x h_cdj
  · exact W_22_eq_zero u x h_cdj

end CGD.Gravity

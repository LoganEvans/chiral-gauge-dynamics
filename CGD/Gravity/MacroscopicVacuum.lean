-- FILENAME: CGD/Gravity/MacroscopicVacuum.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology
import CGD.Gravity.Urbantke
import Litlib.Y1989.capovilla1989general.Signature
import Litlib.Y1991.capovilla1991pure.Signature
import Litlib.Y2024.gielen2024unimodular.Signature

set_option autoImplicit false
set_option linter.unusedVariables false

open Complex Matrix BigOperators
open CGD.Axioms CGD.Foundations Litlib Classical
open Litlib.Y1989.capovilla1989general
open Litlib.Y1991.capovilla1991pure
open Litlib.Y2024.gielen2024unimodular

namespace CGD.Gravity

noncomputable def metricFromTetrad (e : TetradField) : SpacetimeIndex → SpacetimeIndex → SpacetimePoint → ℂ :=
  fun μ ν x => ∑ I : InternalIndex, e I μ x * e I ν x

noncomputable def cgdAdjointCurvature (u : Universe) (μ ν : Fin 4) (x : SpacetimePoint) : Matrix (Fin 3) (Fin 3) ℂ :=
  extractAdjoint (curvatureSl2c u.sd_sector μ ν x).val

def satisfiesPureCdjConstraint (F_adj : SpacetimePoint → Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  ∀ x : SpacetimePoint,
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      epsilon4 μ ν ρ σ • (F_adj x μ ν * F_adj x ρ σ)) = 0

noncomputable def F_CGD (u : Universe) (x : SpacetimePoint) (a : Fin 3) (μ ν : Fin 4) : ℂ :=
  if a = 0 then cgdAdjointCurvature u μ ν x 1 2
  else if a = 1 then cgdAdjointCurvature u μ ν x 2 0
  else cgdAdjointCurvature u μ ν x 0 1

lemma extractAdjoint_neg (M : Matrix (Fin 2) (Fin 2) ℂ) :
  extractAdjoint (-M) = - extractAdjoint M := by
  unfold extractAdjoint
  ext i j
  have h1 : Matrix.trace (-M * sigma1.val) = - Matrix.trace (M * sigma1.val) := by
    rw [Matrix.neg_mul, Matrix.trace_neg]
  have h2 : Matrix.trace (-M * sigma2.val) = - Matrix.trace (M * sigma2.val) := by
    rw [Matrix.neg_mul, Matrix.trace_neg]
  have h3 : Matrix.trace (-M * sigma3.val) = - Matrix.trace (M * sigma3.val) := by
    rw [Matrix.neg_mul, Matrix.trace_neg]
  fin_cases i <;> fin_cases j
  · change (0 : ℂ) = -0; ring
  · change (1 / 2 : ℂ) * Matrix.trace (-M * sigma3.val) = - ((1 / 2 : ℂ) * Matrix.trace (M * sigma3.val))
    rw [h3]; ring
  · change -((1 / 2 : ℂ) * Matrix.trace (-M * sigma2.val)) = - (-((1 / 2 : ℂ) * Matrix.trace (M * sigma2.val)))
    rw [h2]; ring
  · change -((1 / 2 : ℂ) * Matrix.trace (-M * sigma3.val)) = - (-((1 / 2 : ℂ) * Matrix.trace (M * sigma3.val)))
    rw [h3]; ring
  · change (0 : ℂ) = -0; ring
  · change (1 / 2 : ℂ) * Matrix.trace (-M * sigma1.val) = - ((1 / 2 : ℂ) * Matrix.trace (M * sigma1.val))
    rw [h1]; ring
  · change (1 / 2 : ℂ) * Matrix.trace (-M * sigma2.val) = - ((1 / 2 : ℂ) * Matrix.trace (M * sigma2.val))
    rw [h2]; ring
  · change -((1 / 2 : ℂ) * Matrix.trace (-M * sigma1.val)) = - (-((1 / 2 : ℂ) * Matrix.trace (M * sigma1.val)))
    rw [h1]; ring
  · change (0 : ℂ) = -0; ring

lemma adjoint_curvature_antisymm (u : Universe) : 
  ∀ x μ ν, cgdAdjointCurvature u μ ν x = - cgdAdjointCurvature u ν μ x := by
  intros x μ ν
  unfold cgdAdjointCurvature
  have h_antisymm := curvatureSl2c_antisymm u.sd_sector μ ν x
  have h_val_eq : (- curvatureSl2c u.sd_sector ν μ x).val = - (curvatureSl2c u.sd_sector ν μ x).val := rfl
  rw [h_antisymm, h_val_eq, extractAdjoint_neg]

lemma adjoint_curvature_su2 (u : Universe) :
  ∀ x μ ν, 
    cgdAdjointCurvature u μ ν x 0 0 = 0 ∧ 
    cgdAdjointCurvature u μ ν x 1 1 = 0 ∧ 
    cgdAdjointCurvature u μ ν x 2 2 = 0 ∧
    cgdAdjointCurvature u μ ν x 2 1 = - cgdAdjointCurvature u μ ν x 1 2 ∧ 
    cgdAdjointCurvature u μ ν x 2 0 = - cgdAdjointCurvature u μ ν x 0 2 ∧ 
    cgdAdjointCurvature u μ ν x 1 0 = - cgdAdjointCurvature u μ ν x 0 1 := by
  intros x μ ν
  unfold cgdAdjointCurvature extractAdjoint
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · change -((1 / 2 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma1.val)) = - ((1 / 2 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma1.val))
    rfl
  · change (1 / 2 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma2.val) = - (-((1 / 2 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma2.val)))
    ring
  · change -((1 / 2 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma3.val)) = - ((1 / 2 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma3.val))
    rfl

lemma fin2_sum (f : Fin 2 → ℂ) : ∑ i : Fin 2, f i = f 0 + f 1 := by
  have eq : (Finset.univ : Finset (Fin 2)) = {0, 1} := rfl
  rw [eq]
  simp [Finset.sum_insert, Finset.sum_singleton]

lemma fin3_sum (f : Fin 3 → ℂ) : ∑ i : Fin 3, f i = f 0 + f 1 + f 2 := by
  have eq : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := rfl
  rw [eq]
  simp [Finset.sum_insert, Finset.sum_singleton]
  ring

lemma sum_neg_4 (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
  (∑ μ, ∑ ν, ∑ ρ, ∑ σ, - f μ ν ρ σ) = - (∑ μ, ∑ ν, ∑ ρ, ∑ σ, f μ ν ρ σ) := by
  simp [← Finset.sum_neg_distrib]

lemma trace_M_sigma1 (M : Matrix (Fin 2) (Fin 2) ℂ) :
  Matrix.trace (M * sigma1.val) = M 0 1 + M 1 0 := by
  unfold Matrix.trace Matrix.diag
  rw [fin2_sum]
  have hs00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  
  have h0 : (M * sigma1.val) 0 0 = M 0 1 := by
    rw [Matrix.mul_apply]
    rw [fin2_sum]
    rw [hs00, hs10]
    ring
  have h1 : (M * sigma1.val) 1 1 = M 1 0 := by
    rw [Matrix.mul_apply]
    rw [fin2_sum]
    rw [hs01, hs11]
    ring
  rw [h0, h1]

lemma trace_M_sigma2 (M : Matrix (Fin 2) (Fin 2) ℂ) :
  Matrix.trace (M * sigma2.val) = Complex.I * M 0 1 - Complex.I * M 1 0 := by
  unfold Matrix.trace Matrix.diag
  rw [fin2_sum]
  have hs00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  
  have h0 : (M * sigma2.val) 0 0 = Complex.I * M 0 1 := by
    rw [Matrix.mul_apply]
    rw [fin2_sum]
    rw [hs00, hs10]
    ring
  have h1 : (M * sigma2.val) 1 1 = -Complex.I * M 1 0 := by
    rw [Matrix.mul_apply]
    rw [fin2_sum]
    rw [hs01, hs11]
    ring
  rw [h0, h1]
  ring

lemma trace_M_sigma3 (M : Matrix (Fin 2) (Fin 2) ℂ) :
  Matrix.trace (M * sigma3.val) = M 0 0 - M 1 1 := by
  unfold Matrix.trace Matrix.diag
  rw [fin2_sum]
  have hs00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
  
  have h0 : (M * sigma3.val) 0 0 = M 0 0 := by
    rw [Matrix.mul_apply]
    rw [fin2_sum]
    rw [hs00, hs10]
    ring
  have h1 : (M * sigma3.val) 1 1 = - M 1 1 := by
    rw [Matrix.mul_apply]
    rw [fin2_sum]
    rw [hs01, hs11]
    ring
  rw [h0, h1]
  ring

lemma trace_zero_eq_sum_pauli (M : Matrix (Fin 2) (Fin 2) ℂ) (h_tr : Matrix.trace M = 0) :
  let c1 := (1 / 2 : ℂ) * Matrix.trace (M * sigma1.val)
  let c2 := (1 / 2 : ℂ) * Matrix.trace (M * sigma2.val)
  let c3 := (1 / 2 : ℂ) * Matrix.trace (M * sigma3.val)
  c1 • sigma1.val + c2 • sigma2.val + c3 • sigma3.val = M := by
  intros c1 c2 c3
  ext i j
  have h_sum : M 0 0 + M 1 1 = 0 := by
    have h : Matrix.trace M = M 0 0 + M 1 1 := by
      unfold Matrix.trace Matrix.diag
      exact fin2_sum (fun i => M i i)
    rw [← h, h_tr]
  have h11 : M 1 1 = - M 0 0 := by
    have h_add : M 1 1 + M 0 0 = 0 := by rw [add_comm, h_sum]
    exact eq_neg_of_add_eq_zero_left h_add
  
  have hi : Complex.I * Complex.I = -1 := Complex.I_mul_I
  
  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl

  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl

  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl

  fin_cases i <;> fin_cases j
  · change c1 * sigma1.val 0 0 + c2 * sigma2.val 0 0 + c3 * sigma3.val 0 0 = M 0 0
    dsimp [c1, c2, c3]
    rw [trace_M_sigma3]
    rw [hs1_00, hs2_00, hs3_00]
    rw [h11]
    ring
  · change c1 * sigma1.val 0 1 + c2 * sigma2.val 0 1 + c3 * sigma3.val 0 1 = M 0 1
    dsimp [c1, c2, c3]
    rw [trace_M_sigma1, trace_M_sigma2, trace_M_sigma3]
    rw [hs1_01, hs2_01, hs3_01]
    calc
      (1 / 2 : ℂ) * (M 0 1 + M 1 0) * 1 + (1 / 2 : ℂ) * (Complex.I * M 0 1 - Complex.I * M 1 0) * -Complex.I + (1 / 2 : ℂ) * (M 0 0 - M 1 1) * 0
      _ = (1 / 2 : ℂ) * (M 0 1 + M 1 0) + (1 / 2 : ℂ) * (M 0 1 * -(Complex.I * Complex.I) + M 1 0 * (Complex.I * Complex.I)) := by ring
      _ = (1 / 2 : ℂ) * (M 0 1 + M 1 0) + (1 / 2 : ℂ) * (M 0 1 * -(-1) + M 1 0 * (-1)) := by rw [hi]
      _ = M 0 1 := by ring
  · change c1 * sigma1.val 1 0 + c2 * sigma2.val 1 0 + c3 * sigma3.val 1 0 = M 1 0
    dsimp [c1, c2, c3]
    rw [trace_M_sigma1, trace_M_sigma2, trace_M_sigma3]
    rw [hs1_10, hs2_10, hs3_10]
    calc
      (1 / 2 : ℂ) * (M 0 1 + M 1 0) * 1 + (1 / 2 : ℂ) * (Complex.I * M 0 1 - Complex.I * M 1 0) * Complex.I + (1 / 2 : ℂ) * (M 0 0 - M 1 1) * 0
      _ = (1 / 2 : ℂ) * (M 0 1 + M 1 0) + (1 / 2 : ℂ) * (M 0 1 * (Complex.I * Complex.I) - M 1 0 * (Complex.I * Complex.I)) := by ring
      _ = (1 / 2 : ℂ) * (M 0 1 + M 1 0) + (1 / 2 : ℂ) * (M 0 1 * (-1) - M 1 0 * (-1)) := by rw [hi]
      _ = M 1 0 := by ring
  · change c1 * sigma1.val 1 1 + c2 * sigma2.val 1 1 + c3 * sigma3.val 1 1 = M 1 1
    dsimp [c1, c2, c3]
    rw [trace_M_sigma3]
    rw [hs1_11, hs2_11, hs3_11]
    rw [h11]
    ring

lemma F_CGD_reconstruct (u : Universe) (x : SpacetimePoint) (μ ν : Fin 4) :
  F_CGD u x 0 μ ν • sigma1.val + F_CGD u x 1 μ ν • sigma2.val + F_CGD u x 2 μ ν • sigma3.val = (curvatureSl2c u.sd_sector μ ν x).val := by
  have h_tr : Matrix.trace (curvatureSl2c u.sd_sector μ ν x).val = 0 := (curvatureSl2c u.sd_sector μ ν x).property
  have h := trace_zero_eq_sum_pauli (curvatureSl2c u.sd_sector μ ν x).val h_tr
  have h0 : F_CGD u x 0 μ ν = (1 / 2 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma1.val) := rfl
  have h1 : F_CGD u x 1 μ ν = (1 / 2 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma2.val) := rfl
  have h2 : F_CGD u x 2 μ ν = (1 / 2 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma3.val) := rfl
  rw [h0, h1, h2]
  exact h

lemma cgd_eval_00 (u : Universe) (x : SpacetimePoint) (μ ν : Fin 4) : cgdAdjointCurvature u μ ν x 0 0 = 0 := (adjoint_curvature_su2 u x μ ν).1
lemma cgd_eval_11 (u : Universe) (x : SpacetimePoint) (μ ν : Fin 4) : cgdAdjointCurvature u μ ν x 1 1 = 0 := (adjoint_curvature_su2 u x μ ν).2.1
lemma cgd_eval_22 (u : Universe) (x : SpacetimePoint) (μ ν : Fin 4) : cgdAdjointCurvature u μ ν x 2 2 = 0 := (adjoint_curvature_su2 u x μ ν).2.2.1

lemma cgd_eval_12 (u : Universe) (x : SpacetimePoint) (μ ν : Fin 4) : cgdAdjointCurvature u μ ν x 1 2 = F_CGD u x 0 μ ν := rfl
lemma cgd_eval_20 (u : Universe) (x : SpacetimePoint) (μ ν : Fin 4) : cgdAdjointCurvature u μ ν x 2 0 = F_CGD u x 1 μ ν := rfl
lemma cgd_eval_01 (u : Universe) (x : SpacetimePoint) (μ ν : Fin 4) : cgdAdjointCurvature u μ ν x 0 1 = F_CGD u x 2 μ ν := rfl

lemma cgd_eval_21 (u : Universe) (x : SpacetimePoint) (μ ν : Fin 4) : cgdAdjointCurvature u μ ν x 2 1 = - F_CGD u x 0 μ ν := by
  have h := (adjoint_curvature_su2 u x μ ν).2.2.2.1
  have h_def : F_CGD u x 0 μ ν = cgdAdjointCurvature u μ ν x 1 2 := rfl
  rw [h_def]
  exact h

lemma cgd_eval_02 (u : Universe) (x : SpacetimePoint) (μ ν : Fin 4) : cgdAdjointCurvature u μ ν x 0 2 = - F_CGD u x 1 μ ν := by
  have h := (adjoint_curvature_su2 u x μ ν).2.2.2.2.1
  have h_def : F_CGD u x 1 μ ν = cgdAdjointCurvature u μ ν x 2 0 := rfl
  rw [h_def, h]
  ring

lemma cgd_eval_10 (u : Universe) (x : SpacetimePoint) (μ ν : Fin 4) : cgdAdjointCurvature u μ ν x 1 0 = - F_CGD u x 2 μ ν := by
  have h := (adjoint_curvature_su2 u x μ ν).2.2.2.2.2
  have h_def : F_CGD u x 2 μ ν = cgdAdjointCurvature u μ ν x 0 1 := rfl
  rw [h_def]
  exact h

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

Litlib.theorem
  description "Macroscopic Vacuum (General Relativity Limit)"
/-- 
We rigorously prove that the generated complex spacetime metric maps exactly 
to a complex Ricci-flat tensor, as derived from the pure CDJ constraint equation.
-/
theorem macroscopicVacuumGR 
  [eq2_2c : CDJImpliesRicciFlat 
    SpacetimePoint 
    (fun F x μ ν => urbantkeMetric (fun m n => toSl2c (F x 0 m n • sigma1.val + F x 1 m n • sigma2.val + F x 2 m n • sigma3.val)) μ ν) 
    (fun g x μ ν => ricciTensor (fun m n p => g p m n) μ ν x)] 
  (u : Universe)
  (e : TetradField)
  (h_urbantke : ∀ x μ ν, metricFromTetrad e μ ν x = urbantkeMetric (fun m n => toSl2c (curvatureSl2c u.sd_sector m n x).val) μ ν)
  (h_nondeg : ∀ x, (urbantkeMetric (fun m n => toSl2c (curvatureSl2c u.sd_sector m n x).val)).det ≠ 0)
  (h_cdj : satisfiesPureCdjConstraint (fun p m n => cgdAdjointCurvature u m n p)) :
  ∀ x μ ν, ricciTensor (metricFromTetrad e) μ ν x = 0 := by
  have h_6a_proof : ∀ x, (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      capovillaMetric (1:ℂ) (-1:ℂ) a b c d * 
      wedgeContract (F_CGD u x a) (F_CGD u x b) epsilon4 * 
      wedgeContract (F_CGD u x c) (F_CGD u x d) epsilon4) = 0 := by
    intro p
    have hW := W_eq_zero u p (h_cdj p)
    apply Finset.sum_eq_zero; intro a _
    apply Finset.sum_eq_zero; intro b _
    apply Finset.sum_eq_zero; intro c _
    apply Finset.sum_eq_zero; intro d _
    have h_wab : wedgeContract (F_CGD u p a) (F_CGD u p b) epsilon4 = 0 := hW a b
    rw [h_wab]
    ring

  have h_nondeg_proof : ∀ x, Matrix.det (Matrix.of (fun μ ν => urbantkeMetric (fun m n => toSl2c (F_CGD u x 0 m n • sigma1.val + F_CGD u x 1 m n • sigma2.val + F_CGD u x 2 m n • sigma3.val)) μ ν)) ≠ 0 := by
    intro p
    have h_eq_inner : (fun m n => toSl2c (F_CGD u p 0 m n • sigma1.val + F_CGD u p 1 m n • sigma2.val + F_CGD u p 2 m n • sigma3.val)) = 
                      (fun m n => toSl2c (curvatureSl2c u.sd_sector m n p).val) := by
      ext m n
      rw [F_CGD_reconstruct]
    have h_eq : (fun μ ν => urbantkeMetric (fun m n => toSl2c (F_CGD u p 0 m n • sigma1.val + F_CGD u p 1 m n • sigma2.val + F_CGD u p 2 m n • sigma3.val)) μ ν) = 
                (fun μ ν => urbantkeMetric (fun m n => toSl2c (curvatureSl2c u.sd_sector m n p).val) μ ν) := by
      rw [h_eq_inner]
    rw [h_eq]
    exact h_nondeg p

  have he_nz : epsilon4 0 1 2 3 ≠ 0 := by rw [epsilon4_0123]; exact one_ne_zero

  have h_coupling : (1 : ℂ) = -(-1 : ℂ) := by ring
  have h_alpha_nz : (1 : ℂ) ≠ 0 := one_ne_zero

  have ricci_eq_zero := eq2_2c.cdj_implies_ricci_flat (F_CGD u) 1 (-1) epsilon4 epsilon4_alt he_nz h_coupling h_alpha_nz h_nondeg_proof h_6a_proof

  intro x μ ν
  have h_g_eq : (fun m n p => urbantkeMetric (fun k l => toSl2c (F_CGD u p 0 k l • sigma1.val + F_CGD u p 1 k l • sigma2.val + F_CGD u p 2 k l • sigma3.val)) m n) = metricFromTetrad e := by
    ext m n p
    have h_inner : (fun k l => toSl2c (F_CGD u p 0 k l • sigma1.val + F_CGD u p 1 k l • sigma2.val + F_CGD u p 2 k l • sigma3.val)) = 
                   (fun k l => toSl2c (curvatureSl2c u.sd_sector k l p).val) := by
      ext k l
      rw [F_CGD_reconstruct]
    rw [h_inner]
    exact (h_urbantke p m n).symm
  
  have h_r := ricci_eq_zero x μ ν
  rwa [h_g_eq] at h_r

Litlib.theorem
  description "Unimodular Macroscopic Spacetime Volume Emergence"
/-- 
By mapping the continuous Spin(4,C) connections into the 3x3 Adjoint su(2) representation, 
we show that the Unimodular CDJ theorem extracts a strict global volume invariant `c` from the topological CDJ condition.
-/
theorem kinematicUnimodularVacuum 
  [udi : Litlib.Y1991.capovilla1991pure.UrbantkeDeterminantIdentity Unit CGD.Gravity.epsilon4 CGD.Gravity.eps2 CGD.Gravity.eps2_up]
  (bulkVacuum : Set SpacetimePoint)
  (u : Universe)
  (Λ : ℂ)
  (hLambdaNz : Λ ≠ 0)
  (h_cdj : ∀ x ∈ bulkVacuum, (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = Λ • 1) :
  ∀ x y : bulkVacuum, (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det = (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n y.val)).det ∧ 
         (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det ≠ 0 := by
  intro x y
  obtain ⟨det_val, h_det⟩ := urbantke_det_uniqueness Λ
  have hx : (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det = det_val :=
    h_det (fun m n => cgdAdjointCurvature u m n x.val) 
      (adjoint_curvature_antisymm u x.val)
      (adjoint_curvature_su2 u x.val)
      (h_cdj x.val x.property)
  have hy : (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n y.val)).det = det_val :=
    h_det (fun m n => cgdAdjointCurvature u m n y.val) 
      (adjoint_curvature_antisymm u y.val)
      (adjoint_curvature_su2 u y.val)
      (h_cdj y.val y.property)
  have hnz : (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det ≠ 0 :=
    urbantke_nondeg_of_plebanski Λ (fun m n => cgdAdjointCurvature u m n x.val) hLambdaNz 
      (adjoint_curvature_antisymm u x.val)
      (adjoint_curvature_su2 u x.val)
      (h_cdj x.val x.property)
  exact ⟨hx.trans hy.symm, hnz⟩

end CGD.Gravity

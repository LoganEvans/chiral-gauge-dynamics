-- FILENAME: CGD/Gravity/MacroscopicVacuum/Basic.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology

set_option autoImplicit false

open Complex Matrix BigOperators
open CGD.Axioms CGD.Foundations Litlib Classical

namespace CGD.Gravity

noncomputable def metricFromTetrad (e : TetradField) : SpacetimeIndex → SpacetimeIndex → SpacetimePoint → ℂ :=
  fun μ ν x => ∑ I : InternalIndex, e I μ x * e I ν x

noncomputable def cgdAdjointCurvature (u : Universe) (μ ν : Fin 4) (x : SpacetimePoint) : Matrix (Fin 3) (Fin 3) ℂ :=
  extractAdjoint (curvatureSl2c u.sd_sector μ ν x).val

/--
The Pure CDJ Vacuum Constraint (Capovilla, Dell, Jacobson 1991).
Enforces that the symmetric tensor Σ^{ab} = ε^{μνρσ} F^a_{μν} F^b_{ρσ} is purely trace-free.
Σ^{ab} - (1/3) δ^{ab} Tr(Σ) = 0
-/
def satisfiesPureCdjConstraint (F_adj : SpacetimePoint → Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  ∀ x : SpacetimePoint,
    let Sigma := ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      epsilon4 μ ν ρ σ • (F_adj x μ ν * F_adj x ρ σ)
    Sigma = (Matrix.trace Sigma / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ)

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

end CGD.Gravity

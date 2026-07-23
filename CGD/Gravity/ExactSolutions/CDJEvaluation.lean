-- FILENAME: CGD/Gravity/ExactSolutions/CDJEvaluation.lean

import CGD.Gravity.ExactSolutions.LorentzianEval

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations CGD.Math Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def T_CDJ (μ ν ρ σ : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ :=
  adj_F μ ν * adj_F ρ σ

noncomputable def CDJ_sum_matrix : Matrix (Fin 3) (Fin 3) ℂ :=
  (1:ℂ) • T_CDJ 0 1 2 3 + (-1:ℂ) • T_CDJ 0 1 3 2 + (-1:ℂ) • T_CDJ 0 2 1 3 + (1:ℂ) • T_CDJ 0 2 3 1 +
  (1:ℂ) • T_CDJ 0 3 1 2 + (-1:ℂ) • T_CDJ 0 3 2 1 +
  (-1:ℂ) • T_CDJ 1 0 2 3 + (1:ℂ) • T_CDJ 1 0 3 2 + (1:ℂ) • T_CDJ 1 2 0 3 + (-1:ℂ) • T_CDJ 1 2 3 0 +
  (-1:ℂ) • T_CDJ 1 3 0 2 + (1:ℂ) • T_CDJ 1 3 2 0 +
  (1:ℂ) • T_CDJ 2 0 1 3 + (-1:ℂ) • T_CDJ 2 0 3 1 + (-1:ℂ) • T_CDJ 2 1 0 3 + (1:ℂ) • T_CDJ 2 1 3 0 +
  (1:ℂ) • T_CDJ 2 3 0 1 + (-1:ℂ) • T_CDJ 2 3 1 0 +
  (-1:ℂ) • T_CDJ 3 0 1 2 + (1:ℂ) • T_CDJ 3 0 2 1 + (1:ℂ) • T_CDJ 3 1 0 2 + (-1:ℂ) • T_CDJ 3 1 2 0 +
  (-1:ℂ) • T_CDJ 3 2 0 1 + (1:ℂ) • T_CDJ 3 2 1 0

lemma T_CDJ_eval (m n r s : Fin 4) (i j : Fin 3) :
  T_CDJ m n r s i j = adj_F_val m n i 0 * adj_F_val r s 0 j +
                      adj_F_val m n i 1 * adj_F_val r s 1 j +
                      adj_F_val m n i 2 * adj_F_val r s 2 j := by
  unfold T_CDJ; change ∑ k : Fin 3, adj_F m n i k * adj_F r s k j = _; rw [sum_3_eval]
  rw [adj_F_eq_val m n i 0, adj_F_eq_val m n i 1, adj_F_eq_val m n i 2]
  rw [adj_F_eq_val r s 0 j, adj_F_eq_val r s 1 j, adj_F_eq_val r s 2 j]

macro "eval_cdj_cell" : tactic =>
  `(tactic| (
    unfold CDJ_sum_matrix
    simp only [
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      T_CDJ_eval, adj_F_val,
      zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub,
      Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_ofNat,
      Int.cast_zero, Int.cast_one, Int.cast_neg
    ]
    try ring_nf; try simp only [Complex.I_sq, I_pow_3_eq, I_pow_4_eq]; try ring
  ))

lemma CDJ_cell_0_0 : CDJ_sum_matrix 0 0 = 16 * Complex.I := by eval_cdj_cell
lemma CDJ_cell_0_1 : CDJ_sum_matrix 0 1 = 0 := by eval_cdj_cell
lemma CDJ_cell_0_2 : CDJ_sum_matrix 0 2 = 0 := by eval_cdj_cell
lemma CDJ_cell_1_0 : CDJ_sum_matrix 1 0 = 0 := by eval_cdj_cell
lemma CDJ_cell_1_1 : CDJ_sum_matrix 1 1 = 16 * Complex.I := by eval_cdj_cell
lemma CDJ_cell_1_2 : CDJ_sum_matrix 1 2 = 0 := by eval_cdj_cell
lemma CDJ_cell_2_0 : CDJ_sum_matrix 2 0 = 0 := by eval_cdj_cell
lemma CDJ_cell_2_1 : CDJ_sum_matrix 2 1 = 0 := by eval_cdj_cell
lemma CDJ_cell_2_2 : CDJ_sum_matrix 2 2 = 16 * Complex.I := by eval_cdj_cell

lemma CDJ_sum_matrix_eq_diag : CDJ_sum_matrix = Matrix.diagonal ![(16 * Complex.I : ℂ), 16 * Complex.I, 16 * Complex.I] := by
  ext i j; fin_cases i <;> fin_cases j
  · change CDJ_sum_matrix 0 0 = 16 * Complex.I; exact CDJ_cell_0_0
  · change CDJ_sum_matrix 0 1 = 0; exact CDJ_cell_0_1
  · change CDJ_sum_matrix 0 2 = 0; exact CDJ_cell_0_2
  · change CDJ_sum_matrix 1 0 = 0; exact CDJ_cell_1_0
  · change CDJ_sum_matrix 1 1 = 16 * Complex.I; exact CDJ_cell_1_1
  · change CDJ_sum_matrix 1 2 = 0; exact CDJ_cell_1_2
  · change CDJ_sum_matrix 2 0 = 0; exact CDJ_cell_2_0
  · change CDJ_sum_matrix 2 1 = 0; exact CDJ_cell_2_1
  · change CDJ_sum_matrix 2 2 = 16 * Complex.I; exact CDJ_cell_2_2

@[litlib_track "CDJ constraint holds"]
lemma cdjConstraintHolds :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ • (adj_F μ ν * adj_F ρ σ)) =
  ((∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ • (adj_F μ ν * adj_F ρ σ)).trace / 3) • 1 := by
  have h_lhs : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ • (adj_F μ ν * adj_F ρ σ)) = CDJ_sum_matrix := by exact sum_epsilon4_matrices (fun μ ν ρ σ => adj_F μ ν * adj_F ρ σ)
  rw [h_lhs]
  have h_trace : CDJ_sum_matrix.trace = 48 * Complex.I := by rw [CDJ_sum_matrix_eq_diag]; unfold Matrix.trace Matrix.diag; rw [sum_3_eval]; simp; ring
  rw [h_trace, CDJ_sum_matrix_eq_diag]; ext i j; fin_cases i <;> fin_cases j <;> { simp [Matrix.one_apply]; try ring }

end CGD.Gravity

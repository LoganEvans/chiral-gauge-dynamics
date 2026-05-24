-- FILENAME: CGD/Gravity/ExactSolutionsPart25_2.lean

import CGD.Gravity.ExactSolutionsPart25_1
import CGD.Gravity.ExactSolutionsPart0

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma sum_3_eval_2 {E : Type*} [AddCommGroup E] (f : Fin 3 → E) :
  ∑ k : Fin 3, f k = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]; abel

lemma T_CDJ_eval (m n r s : Fin 4) (i j : Fin 3) :
  T_CDJ m n r s i j = adj_F_val m n i 0 * adj_F_val r s 0 j +
                      adj_F_val m n i 1 * adj_F_val r s 1 j +
                      adj_F_val m n i 2 * adj_F_val r s 2 j := by
  unfold T_CDJ
  change ∑ k : Fin 3, adj_F m n i k * adj_F r s k j = _
  rw [sum_3_eval_2]
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
    try ring_nf
    try simp only [Complex.I_sq, I_pow_3_eq, I_pow_4_eq]
    try ring
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
  ext i j
  fin_cases i <;> fin_cases j
  · change CDJ_sum_matrix 0 0 = 16 * Complex.I; exact CDJ_cell_0_0
  · change CDJ_sum_matrix 0 1 = 0; exact CDJ_cell_0_1
  · change CDJ_sum_matrix 0 2 = 0; exact CDJ_cell_0_2
  · change CDJ_sum_matrix 1 0 = 0; exact CDJ_cell_1_0
  · change CDJ_sum_matrix 1 1 = 16 * Complex.I; exact CDJ_cell_1_1
  · change CDJ_sum_matrix 1 2 = 0; exact CDJ_cell_1_2
  · change CDJ_sum_matrix 2 0 = 0; exact CDJ_cell_2_0
  · change CDJ_sum_matrix 2 1 = 0; exact CDJ_cell_2_1
  · change CDJ_sum_matrix 2 2 = 16 * Complex.I; exact CDJ_cell_2_2

end CGD.Gravity

-- FILENAME: CGD/Quantum/Holonomy/Pauli.lean

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import CGD.Foundations.GaugeGroup

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations Matrix Complex BigOperators

namespace CGD.Quantum

lemma sigma1_val_eq_mat : sigma1.val = Matrix.of ![![0, 1], ![1, 0]] := by rw [val_sigma1]; rfl
lemma sigma3_val_eq_mat : sigma3.val = Matrix.of ![![1, 0], ![0, -1]] := by rw [val_sigma3]; rfl

lemma trace_sigma1 : Matrix.trace sigma1.val = 0 := by
  rw [sigma1_val_eq_mat]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.zero_apply]

lemma trace_sigma3 : Matrix.trace sigma3.val = 0 := by
  rw [sigma3_val_eq_mat]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.zero_apply]

lemma trace_sigma3_sigma1 : Matrix.trace (sigma3.val * sigma1.val) = 0 := by
  rw [sigma3_val_eq_mat, sigma1_val_eq_mat]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, Matrix.zero_apply]

lemma trace_sigma1_sigma3 : Matrix.trace (sigma1.val * sigma3.val) = 0 := by
  rw [sigma1_val_eq_mat, sigma3_val_eq_mat]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, Matrix.zero_apply]

lemma pauli_algebra_sigma1_sq : sigma1.val ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  rw [sigma1_val_eq_mat]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

lemma pauli_algebra_sigma3_sq : sigma3.val ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  rw [sigma3_val_eq_mat]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

lemma trace_sigma3_sq : Matrix.trace (sigma3.val * sigma3.val) = 2 := by
  have eq : sigma3.val * sigma3.val = 1 := by
    have h := pauli_algebra_sigma3_sq
    rw [pow_two] at h
    exact h
  rw [eq]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.one_apply]

lemma trace_sigma1_sq : Matrix.trace (sigma1.val * sigma1.val) = 2 := by
  have eq : sigma1.val * sigma1.val = 1 := by
    have h := pauli_algebra_sigma1_sq
    rw [pow_two] at h
    exact h
  rw [eq]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.one_apply]

lemma matrix_mul_2x2_00 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 := by
  have eq : (A * B) 0 0 = ∑ k : Fin 2, A 0 k * B k 0 := rfl
  rw [eq, Fin.sum_univ_two]

lemma matrix_mul_2x2_01 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 := by
  have eq : (A * B) 0 1 = ∑ k : Fin 2, A 0 k * B k 1 := rfl
  rw [eq, Fin.sum_univ_two]

lemma matrix_mul_2x2_10 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 := by
  have eq : (A * B) 1 0 = ∑ k : Fin 2, A 1 k * B k 0 := rfl
  rw [eq, Fin.sum_univ_two]

lemma matrix_mul_2x2_11 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  have eq : (A * B) 1 1 = ∑ k : Fin 2, A 1 k * B k 1 := rfl
  rw [eq, Fin.sum_univ_two]

end CGD.Quantum

-- FILENAME: CGD/Gravity/ExactSolutionsPart25_1.lean

import CGD.Gravity.ExactSolutionsPart24

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma sum_2_eval {E : Type*} [AddCommGroup E] (f : Fin 2 → E) :
  ∑ k : Fin 2, f k = f 0 + f 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_one]
  rfl

@[simp]
lemma trace_2x2_apply (A : Matrix (Fin 2) (Fin 2) ℂ) :
  Matrix.trace A = A 0 0 + A 1 1 := by
  change ∑ k : Fin 2, A k k = _
  exact sum_2_eval _

@[simp]
lemma mul_2x2_apply (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  change ∑ k : Fin 2, A i k * B k j = _
  exact sum_2_eval _

lemma sum_3_eval {E : Type*} [AddCommGroup E] (f : Fin 3 → E) :
  ∑ k : Fin 3, f k = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  abel

lemma sum_4_eval {E : Type*} [AddCommGroup E] (f : Fin 4 → E) :
  ∑ k : Fin 4, f k = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  abel

@[simp]
lemma mul_3x3_apply (A B : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j := by
  change ∑ k : Fin 3, A i k * B k j = _
  exact sum_3_eval _

lemma sum_epsilon4_matrices {E : Type*} [AddCommGroup E] [Module ℂ E]
  (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → E) :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ • T μ ν ρ σ) =
    (1:ℂ) • T 0 1 2 3 + (-1:ℂ) • T 0 1 3 2 + (-1:ℂ) • T 0 2 1 3 + (1:ℂ) • T 0 2 3 1 +
    (1:ℂ) • T 0 3 1 2 + (-1:ℂ) • T 0 3 2 1 +
    (-1:ℂ) • T 1 0 2 3 + (1:ℂ) • T 1 0 3 2 + (1:ℂ) • T 1 2 0 3 + (-1:ℂ) • T 1 2 3 0 +
    (-1:ℂ) • T 1 3 0 2 + (1:ℂ) • T 1 3 2 0 +
    (1:ℂ) • T 2 0 1 3 + (-1:ℂ) • T 2 0 3 1 + (-1:ℂ) • T 2 1 0 3 + (1:ℂ) • T 2 1 3 0 +
    (1:ℂ) • T 2 3 0 1 + (-1:ℂ) • T 2 3 1 0 +
    (-1:ℂ) • T 3 0 1 2 + (1:ℂ) • T 3 0 2 1 + (1:ℂ) • T 3 1 0 2 + (-1:ℂ) • T 3 1 2 0 +
    (-1:ℂ) • T 3 2 0 1 + (1:ℂ) • T 3 2 1 0 := by
  simp only [sum_4_eval, epsilon4, epsilon4_int, Int.cast_zero, Int.cast_one, Int.cast_neg, zero_smul, add_zero, zero_add]
  abel

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

end CGD.Gravity

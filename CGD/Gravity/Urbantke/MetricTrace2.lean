-- FILENAME: CGD/Gravity/Urbantke/MetricTrace2.lean

import CGD.Gravity.Urbantke.MetricTrace1

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

lemma eps3_012 : epsilon3 0 1 2 = 1 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_120 : epsilon3 1 2 0 = 1 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_201 : epsilon3 2 0 1 = 1 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_021 : epsilon3 0 2 1 = -1 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_102 : epsilon3 1 0 2 = -1 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_210 : epsilon3 2 1 0 = -1 := by norm_num [epsilon3, epsilon3_int]

lemma eps3_000 : epsilon3 0 0 0 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_001 : epsilon3 0 0 1 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_002 : epsilon3 0 0 2 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_010 : epsilon3 0 1 0 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_011 : epsilon3 0 1 1 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_020 : epsilon3 0 2 0 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_022 : epsilon3 0 2 2 = 0 := by norm_num [epsilon3, epsilon3_int]

lemma eps3_100 : epsilon3 1 0 0 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_101 : epsilon3 1 0 1 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_110 : epsilon3 1 1 0 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_111 : epsilon3 1 1 1 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_112 : epsilon3 1 1 2 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_121 : epsilon3 1 2 1 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_122 : epsilon3 1 2 2 = 0 := by norm_num [epsilon3, epsilon3_int]

lemma eps3_200 : epsilon3 2 0 0 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_202 : epsilon3 2 0 2 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_211 : epsilon3 2 1 1 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_212 : epsilon3 2 1 2 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_220 : epsilon3 2 2 0 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_221 : epsilon3 2 2 1 = 0 := by norm_num [epsilon3, epsilon3_int]
lemma eps3_222 : epsilon3 2 2 2 = 0 := by norm_num [epsilon3, epsilon3_int]

noncomputable def TE (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of (tau a) * Matrix.of eps2

lemma TE_0_eq : TE 0 = mkMat 0 (-1) (-1) 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  · change TE 0 0 0 = mkMat 0 (-1) (-1) 0 0 0
    dsimp [TE, Matrix.mul_apply, tau, eps2, mkMat]
    simp [Fin.sum_univ_two]
  · change TE 0 0 1 = mkMat 0 (-1) (-1) 0 0 1
    dsimp [TE, Matrix.mul_apply, tau, eps2, mkMat]
    simp [Fin.sum_univ_two]
  · change TE 0 1 0 = mkMat 0 (-1) (-1) 0 1 0
    dsimp [TE, Matrix.mul_apply, tau, eps2, mkMat]
    simp [Fin.sum_univ_two]
  · change TE 0 1 1 = mkMat 0 (-1) (-1) 0 1 1
    dsimp [TE, Matrix.mul_apply, tau, eps2, mkMat]
    simp [Fin.sum_univ_two]

lemma TE_1_eq : TE 1 = mkMat 0 I (-I) 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  · change TE 1 0 0 = mkMat 0 I (-I) 0 0 0
    dsimp [TE, Matrix.mul_apply, tau, eps2, mkMat]
    simp [Fin.sum_univ_two]
  · change TE 1 0 1 = mkMat 0 I (-I) 0 0 1
    dsimp [TE, Matrix.mul_apply, tau, eps2, mkMat]
    simp [Fin.sum_univ_two]
  · change TE 1 1 0 = mkMat 0 I (-I) 0 1 0
    dsimp [TE, Matrix.mul_apply, tau, eps2, mkMat]
    simp [Fin.sum_univ_two]
  · change TE 1 1 1 = mkMat 0 I (-I) 0 1 1
    dsimp [TE, Matrix.mul_apply, tau, eps2, mkMat]
    simp [Fin.sum_univ_two]

lemma TE_2_eq : TE 2 = mkMat (-1) 0 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · change TE 2 0 0 = mkMat (-1) 0 0 1 0 0
    dsimp [TE, Matrix.mul_apply, tau, eps2, mkMat]
    simp [Fin.sum_univ_two]
  · change TE 2 0 1 = mkMat (-1) 0 0 1 0 1
    dsimp [TE, Matrix.mul_apply, tau, eps2, mkMat]
    simp [Fin.sum_univ_two]
  · change TE 2 1 0 = mkMat (-1) 0 0 1 1 0
    dsimp [TE, Matrix.mul_apply, tau, eps2, mkMat]
    simp [Fin.sum_univ_two]
  · change TE 2 1 1 = mkMat (-1) 0 0 1 1 1
    dsimp [TE, Matrix.mul_apply, tau, eps2, mkMat]
    simp [Fin.sum_univ_two]

lemma trace_mul3_fin2 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
  Matrix.trace (A * B * C) = 
    A 0 0 * B 0 0 * C 0 0 + A 0 0 * B 0 1 * C 1 0 + A 0 1 * B 1 0 * C 0 0 + A 0 1 * B 1 1 * C 1 0 +
    A 1 0 * B 0 0 * C 0 1 + A 1 0 * B 0 1 * C 1 1 + A 1 1 * B 1 0 * C 0 1 + A 1 1 * B 1 1 * C 1 1 := by
  dsimp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  repeat rw [Fin.sum_univ_two]
  ring

end CGD.Gravity

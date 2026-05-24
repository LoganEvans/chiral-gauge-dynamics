-- FILENAME: CGD/Gravity/ExactSolutionsPart23.lean

import CGD.Gravity.ExactSolutionsPart22

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def F_origin_val (mu nu : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if mu = 0 ∧ nu = 1 then -sigmaX
  else if mu = 0 ∧ nu = 2 then -sigmaY
  else if mu = 0 ∧ nu = 3 then -sigmaZ
  else if mu = 1 ∧ nu = 0 then sigmaX
  else if mu = 2 ∧ nu = 0 then sigmaY
  else if mu = 3 ∧ nu = 0 then sigmaZ
  else if mu = 1 ∧ nu = 2 then Complex.I • sigmaZ
  else if mu = 2 ∧ nu = 1 then -Complex.I • sigmaZ
  else if mu = 1 ∧ nu = 3 then -Complex.I • sigmaY
  else if mu = 3 ∧ nu = 1 then Complex.I • sigmaY
  else if mu = 2 ∧ nu = 3 then Complex.I • sigmaX
  else if mu = 3 ∧ nu = 2 then -Complex.I • sigmaX
  else 0

lemma c_F_mat_0_1 : c_F_mat 0 1 = -sigmaX := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_0_2 : c_F_mat 0 2 = -sigmaY := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_0_3 : c_F_mat 0 3 = -sigmaZ := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_1_0 : c_F_mat 1 0 = sigmaX := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_2_0 : c_F_mat 2 0 = sigmaY := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_3_0 : c_F_mat 3 0 = sigmaZ := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_1_2 : c_F_mat 1 2 = Complex.I • sigmaZ := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_2_1 : c_F_mat 2 1 = -Complex.I • sigmaZ := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_1_3 : c_F_mat 1 3 = -Complex.I • sigmaY := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_3_1 : c_F_mat 3 1 = Complex.I • sigmaY := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_2_3 : c_F_mat 2 3 = Complex.I • sigmaX := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_3_2 : c_F_mat 3 2 = -Complex.I • sigmaX := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_same (mu : Fin 4) : c_F_mat mu mu = 0 := by
  unfold c_F_mat
  exact sub_self (L_map mu (Pi.single mu 1))

lemma c_F_mat_eval (mu nu : Fin 4) : c_F_mat mu nu = F_origin_val mu nu := by
  fin_cases mu <;> fin_cases nu
  · change c_F_mat 0 0 = F_origin_val 0 0; rw [c_F_mat_same 0]; rfl
  · change c_F_mat 0 1 = F_origin_val 0 1; rw [c_F_mat_0_1]; rfl
  · change c_F_mat 0 2 = F_origin_val 0 2; rw [c_F_mat_0_2]; rfl
  · change c_F_mat 0 3 = F_origin_val 0 3; rw [c_F_mat_0_3]; rfl
  · change c_F_mat 1 0 = F_origin_val 1 0; rw [c_F_mat_1_0]; rfl
  · change c_F_mat 1 1 = F_origin_val 1 1; rw [c_F_mat_same 1]; rfl
  · change c_F_mat 1 2 = F_origin_val 1 2; rw [c_F_mat_1_2]; rfl
  · change c_F_mat 1 3 = F_origin_val 1 3; rw [c_F_mat_1_3]; rfl
  · change c_F_mat 2 0 = F_origin_val 2 0; rw [c_F_mat_2_0]; rfl
  · change c_F_mat 2 1 = F_origin_val 2 1; rw [c_F_mat_2_1]; rfl
  · change c_F_mat 2 2 = F_origin_val 2 2; rw [c_F_mat_same 2]; rfl
  · change c_F_mat 2 3 = F_origin_val 2 3; rw [c_F_mat_2_3]; rfl
  · change c_F_mat 3 0 = F_origin_val 3 0; rw [c_F_mat_3_0]; rfl
  · change c_F_mat 3 1 = F_origin_val 3 1; rw [c_F_mat_3_1]; rfl
  · change c_F_mat 3 2 = F_origin_val 3 2; rw [c_F_mat_3_2]; rfl
  · change c_F_mat 3 3 = F_origin_val 3 3; rw [c_F_mat_same 3]; rfl

end CGD.Gravity

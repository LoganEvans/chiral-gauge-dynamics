-- FILENAME: CGD/Cosmology/TimeEmergence/ProjectComponents.lean

import CGD.Cosmology.TimeEmergence.SymmetricComponents
import CGD.Cosmology.TimeEmergence.PPoly

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Cosmology

noncomputable def bField (F : Fin 4 → Fin 4 → SL2C) (a : Fin 3) (i : Fin 3) : Complex :=
  if i = 0 then project F a 0 1
  else if i = 1 then project F a 0 2
  else project F a 0 3

lemma project_anti (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (c : Fin 3) (i j : Fin 4) :
  project F c i j = - project F c j i := by
  dsimp [project]
  have h1 := math_self_dual_antisymmetric F h_symm i j
  have h2 : (-F j i).val = -(F j i).val := rfl
  rw [h1, h2, Matrix.neg_mul]
  have h_tr : Matrix.trace (-((F j i).val * (getPauli c).val)) = - Matrix.trace ((F j i).val * (getPauli c).val) := by simp
  rw[h_tr]
  ring

lemma proj_00 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) : project F a 0 0 = 0 := by
  dsimp [project]
  have h1 : (F 0 0).val = 0 := by ext x y; exact val_00 F h_symm x y
  rw [h1, Matrix.zero_mul]
  simp

lemma proj_11 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) : project F a 1 1 = 0 := by
  dsimp [project]
  have h1 : (F 1 1).val = 0 := by ext x y; exact val_11 F h_symm x y
  rw [h1, Matrix.zero_mul]
  simp

lemma proj_22 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) : project F a 2 2 = 0 := by
  dsimp [project]
  have h1 : (F 2 2).val = 0 := by ext x y; exact val_22 F h_symm x y
  rw [h1, Matrix.zero_mul]
  simp

lemma proj_33 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) : project F a 3 3 = 0 := by
  dsimp [project]
  have h1 : (F 3 3).val = 0 := by ext x y; exact val_33 F h_symm x y
  rw[h1, Matrix.zero_mul]
  simp

lemma proj_01 (F : Fin 4 → Fin 4 → SL2C) (a : Fin 3) : project F a 0 1 = bField F a 0 := rfl

lemma proj_02 (F : Fin 4 → Fin 4 → SL2C) (a : Fin 3) : project F a 0 2 = bField F a 1 := by
  unfold bField
  have h : ¬ (1 : Fin 3) = 0 := by decide
  simp [h]

lemma proj_03 (F : Fin 4 → Fin 4 → SL2C) (a : Fin 3) : project F a 0 3 = bField F a 2 := by
  unfold bField
  have h1 : ¬ (2 : Fin 3) = 0 := by decide
  have h2 : ¬ (2 : Fin 3) = 1 := by decide
  simp [h1, h2]

lemma proj_10 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) : project F a 1 0 = - bField F a 0 := by
  rw[project_anti F h_symm a 1 0, proj_01]

lemma proj_20 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) : project F a 2 0 = - bField F a 1 := by
  rw[project_anti F h_symm a 2 0, proj_02]

lemma proj_30 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) : project F a 3 0 = - bField F a 2 := by
  rw[project_anti F h_symm a 3 0, proj_03]

lemma proj_23 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) : project F a 2 3 = bField F a 0 := by
  have hc := math_self_dual_components F h_symm
  have h_eq : F 2 3 = F 0 1 := hc.1.symm
  rw [← proj_01 F a]
  dsimp [project]
  rw[h_eq]

lemma proj_31 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) : project F a 3 1 = bField F a 1 := by
  have hc := math_self_dual_components F h_symm
  have h1 : F 0 2 = - F 1 3 := hc.2.1
  have h2 : F 3 1 = - F 1 3 := math_self_dual_antisymmetric F h_symm 3 1
  have h_eq : F 3 1 = F 0 2 := by rw[h2, ← h1]
  rw [← proj_02 F a]
  dsimp [project]
  rw [h_eq]

lemma proj_12 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) : project F a 1 2 = bField F a 2 := by
  have hc := math_self_dual_components F h_symm
  have h_eq : F 1 2 = F 0 3 := hc.2.2.symm
  rw[← proj_03 F a]
  dsimp [project]
  rw [h_eq]

lemma proj_32 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) : project F a 3 2 = - bField F a 0 := by
  rw[project_anti F h_symm a 3 2, proj_23 F h_symm a]

lemma proj_13 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) : project F a 1 3 = - bField F a 1 := by
  rw[project_anti F h_symm a 1 3, proj_31 F h_symm a]

lemma proj_21 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) : project F a 2 1 = - bField F a 2 := by
  rw[project_anti F h_symm a 2 1, proj_12 F h_symm a]

lemma project_eq_P_mat (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a : Fin 3) (i j : Fin 4) :
  project F a i j = pMat (bField F a 0) (bField F a 1) (bField F a 2) i j := by
  have h00 := proj_00 F h_symm a; have h01 := proj_01 F a; have h02 := proj_02 F a; have h03 := proj_03 F a
  have h10 := proj_10 F h_symm a; have h11 := proj_11 F h_symm a; have h12 := proj_12 F h_symm a; have h13 := proj_13 F h_symm a
  have h20 := proj_20 F h_symm a; have h21 := proj_21 F h_symm a; have h22 := proj_22 F h_symm a; have h23 := proj_23 F h_symm a
  have h30 := proj_30 F h_symm a; have h31 := proj_31 F h_symm a; have h32 := proj_32 F h_symm a; have h33 := proj_33 F h_symm a
  unfold pMat
  fin_cases i <;> fin_cases j
  all_goals {
    simp[h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33]
  }

lemma project_is_self_dual (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (c : Fin 3) :
  ∀ (gamma delta : Fin 4), project F c gamma delta = ∑ rho : Fin 4, ∑ sigma : Fin 4, ((1 / 2 : ℂ) * epsilon4 gamma delta rho sigma) * project F c rho sigma := by
  intro gamma delta
  have hp : ∀ i j, project F c i j = pMat (bField F c 0) (bField F c 1) (bField F c 2) i j := project_eq_P_mat F h_symm c
  simp only [hp, sum_fin_4_expand]
  unfold epsilon4 pMat
  fin_cases gamma <;> fin_cases delta <;> (dsimp [epsilon4_int]; ring)

end CGD.Cosmology

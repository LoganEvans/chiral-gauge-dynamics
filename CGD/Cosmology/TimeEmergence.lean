-- FILENAME: CGD/Cosmology/TimeEmergence.lean

import Litlib.Core
import CGD.Cosmology.Definitions
import CGD.Gravity.Geometry
import CGD.Foundations.Math
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import CGD.Axioms.Ontology

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Cosmology

lemma sl2c_zero_val : (0 : SL2C).val = 0 := rfl

lemma math_Time_Spatial_Zero_term (F : Fin 4 → Fin 4 → SL2C)
  (h_time : ∀ j : Fin 4, F 0 j = 0)
  (a b c : Fin 3) (j α β γ δ : Fin 4) :
  epsilon4 α β γ δ * project F a 0 α * project F b j β * project F c γ δ = 0 := by
  have h_proj : project F a 0 α = 0 := by
    dsimp [project]
    have h : F 0 α = 0 := h_time α
    rw [h, sl2c_zero_val]
    simp
  rw [h_proj]
  simp

lemma math_Time_inner_sum_zero (F : Fin 4 → Fin 4 → SL2C)
  (h_time : ∀ j : Fin 4, F 0 j = 0)
  (a b c : Fin 3) (j : Fin 4) :
  (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    epsilon4 α β γ δ * project F a 0 α * project F b j β * project F c γ δ) = 0 := by
  apply Finset.sum_eq_zero; intro α _
  apply Finset.sum_eq_zero; intro β _
  apply Finset.sum_eq_zero; intro γ _
  apply Finset.sum_eq_zero; intro δ _
  exact math_Time_Spatial_Zero_term F h_time a b c j α β γ δ

lemma math_Time_Metric_Zero (F : Fin 4 → Fin 4 → SL2C)
  (h_time : ∀ j : Fin 4, F 0 j = 0) :
  ∀ j : Fin 4, (urbantkeMetric F) 0 j = 0 := by
  intro j
  unfold urbantkeMetric
  apply Finset.sum_eq_zero; intro a _
  apply Finset.sum_eq_zero; intro b _
  apply Finset.sum_eq_zero; intro c _
  have h_inner := math_Time_inner_sum_zero F h_time a b c j
  rw [h_inner, mul_zero]

lemma sl2c_eq_iff_val (A B : SL2C) : A = B ↔ A.val = B.val := Subtype.ext_iff
lemma sl2c_smul_val (c : ℂ) (A : SL2C) : (c • A).val = c • A.val := rfl
lemma sl2c_neg_val (A : SL2C) : (-A).val = -A.val := rfl
lemma sl2c_sum_val_4 (f : Fin 4 → SL2C) : (∑ i : Fin 4, f i).val = ∑ i : Fin 4, (f i).val := by
  simp only[Fin.sum_univ_four]; rfl

lemma sl2c_neg_val_apply (A : SL2C) (i j : Fin 2) : (-A).val i j = -A.val i j := rfl
lemma sl2c_smul_val_apply (c : ℂ) (A : SL2C) (i j : Fin 2) : (c • A).val i j = c * A.val i j := rfl

lemma sl2c_sum_val_4_2 (f : Fin 4 → Fin 4 → SL2C) (x y : Fin 2) :
  (∑ i : Fin 4, ∑ j : Fin 4, f i j).val x y =
  (f 0 0).val x y + (f 0 1).val x y + (f 0 2).val x y + (f 0 3).val x y +
  ((f 1 0).val x y + (f 1 1).val x y + (f 1 2).val x y + (f 1 3).val x y) +
  ((f 2 0).val x y + (f 2 1).val x y + (f 2 2).val x y + (f 2 3).val x y) +
  ((f 3 0).val x y + (f 3 1).val x y + (f 3 2).val x y + (f 3 3).val x y) := by
  simp only [Fin.sum_univ_four]; rfl

lemma val_00 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 0 0).val x y = 0 := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 0 0)) x) y
  rw [sl2c_sum_val_4_2] at h; simp only [sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  exact h

lemma val_01 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 0 1).val x y = (1/2:ℂ) * (F 2 3).val x y - (1/2:ℂ) * (F 3 2).val x y := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 0 1)) x) y
  rw [sl2c_sum_val_4_2] at h; simp only [sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  rw[h]; ring

lemma val_02 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 0 2).val x y = -(1/2:ℂ) * (F 1 3).val x y + (1/2:ℂ) * (F 3 1).val x y := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 0 2)) x) y
  rw[sl2c_sum_val_4_2] at h; simp only [sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  rw [h]; ring

lemma val_03 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 0 3).val x y = (1/2:ℂ) * (F 1 2).val x y - (1/2:ℂ) * (F 2 1).val x y := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 0 3)) x) y
  rw [sl2c_sum_val_4_2] at h; simp only[sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  rw [h]; ring

lemma val_10 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 1 0).val x y = -(1/2:ℂ) * (F 2 3).val x y + (1/2:ℂ) * (F 3 2).val x y := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 1 0)) x) y
  rw [sl2c_sum_val_4_2] at h; simp only [sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  rw [h]; ring

lemma val_11 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 1 1).val x y = 0 := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 1 1)) x) y
  rw [sl2c_sum_val_4_2] at h; simp only[sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  exact h

lemma val_12 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 1 2).val x y = (1/2:ℂ) * (F 0 3).val x y - (1/2:ℂ) * (F 3 0).val x y := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 1 2)) x) y
  rw [sl2c_sum_val_4_2] at h; simp only [sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  rw [h]; ring

lemma val_13 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 1 3).val x y = -(1/2:ℂ) * (F 0 2).val x y + (1/2:ℂ) * (F 2 0).val x y := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 1 3)) x) y
  rw[sl2c_sum_val_4_2] at h; simp only [sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  rw [h]; ring

lemma val_20 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 2 0).val x y = (1/2:ℂ) * (F 1 3).val x y - (1/2:ℂ) * (F 3 1).val x y := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 2 0)) x) y
  rw[sl2c_sum_val_4_2] at h; simp only[sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  rw [h]; ring

lemma val_21 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 2 1).val x y = -(1/2:ℂ) * (F 0 3).val x y + (1/2:ℂ) * (F 3 0).val x y := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 2 1)) x) y
  rw [sl2c_sum_val_4_2] at h; simp only[sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  rw [h]; ring

lemma val_22 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 2 2).val x y = 0 := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 2 2)) x) y
  rw [sl2c_sum_val_4_2] at h; simp only[sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  exact h

lemma val_23 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 2 3).val x y = (1/2:ℂ) * (F 0 1).val x y - (1/2:ℂ) * (F 1 0).val x y := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 2 3)) x) y
  rw [sl2c_sum_val_4_2] at h; simp only[sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  rw [h]; ring

lemma val_30 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 3 0).val x y = -(1/2:ℂ) * (F 1 2).val x y + (1/2:ℂ) * (F 2 1).val x y := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 3 0)) x) y
  rw[sl2c_sum_val_4_2] at h; simp only [sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  rw[h]; ring

lemma val_31 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 3 1).val x y = (1/2:ℂ) * (F 0 2).val x y - (1/2:ℂ) * (F 2 0).val x y := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 3 1)) x) y
  rw[sl2c_sum_val_4_2] at h; simp only[sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  rw [h]; ring

lemma val_32 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 3 2).val x y = -(1/2:ℂ) * (F 0 1).val x y + (1/2:ℂ) * (F 1 0).val x y := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 3 2)) x) y
  rw [sl2c_sum_val_4_2] at h; simp only[sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  rw [h]; ring

lemma val_33 (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (x y : Fin 2) :
  (F 3 3).val x y = 0 := by
  have h := congr_fun (congr_fun (congr_arg Subtype.val (h_symm 3 3)) x) y
  rw[sl2c_sum_val_4_2] at h; simp only[sl2c_smul_val_apply] at h
  simp [epsilon4, epsilon4_int] at h
  exact h

lemma math_self_dual_antisymmetric (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (mu nu : Fin 4) :
  F mu nu = - F nu mu := by
  apply Subtype.ext; ext x y
  have h_neg : (- F nu mu).val x y = - (F nu mu).val x y := rfl
  rw [h_neg]
  have h00 := val_00 F h_symm x y; have h01 := val_01 F h_symm x y; have h02 := val_02 F h_symm x y; have h03 := val_03 F h_symm x y
  have h10 := val_10 F h_symm x y; have h11 := val_11 F h_symm x y; have h12 := val_12 F h_symm x y; have h13 := val_13 F h_symm x y
  have h20 := val_20 F h_symm x y; have h21 := val_21 F h_symm x y; have h22 := val_22 F h_symm x y; have h23 := val_23 F h_symm x y
  have h30 := val_30 F h_symm x y; have h31 := val_31 F h_symm x y; have h32 := val_32 F h_symm x y; have h33 := val_33 F h_symm x y
  fin_cases mu
  · fin_cases nu
    · change (F 0 0).val x y = - (F 0 0).val x y; rw [h00]; ring
    · change (F 0 1).val x y = - (F 1 0).val x y; rw [h01, h10]; ring
    · change (F 0 2).val x y = - (F 2 0).val x y; rw [h02, h20]; ring
    · change (F 0 3).val x y = - (F 3 0).val x y; rw [h03, h30]; ring
  · fin_cases nu
    · change (F 1 0).val x y = - (F 0 1).val x y; rw [h10, h01]; ring
    · change (F 1 1).val x y = - (F 1 1).val x y; rw [h11]; ring
    · change (F 1 2).val x y = - (F 2 1).val x y; rw [h12, h21]; ring
    · change (F 1 3).val x y = - (F 3 1).val x y; rw [h13, h31]; ring
  · fin_cases nu
    · change (F 2 0).val x y = - (F 0 2).val x y; rw[h20, h02]; ring
    · change (F 2 1).val x y = - (F 1 2).val x y; rw [h21, h12]; ring
    · change (F 2 2).val x y = - (F 2 2).val x y; rw [h22]; ring
    · change (F 2 3).val x y = - (F 3 2).val x y; rw [h23, h32]; ring
  · fin_cases nu
    · change (F 3 0).val x y = - (F 0 3).val x y; rw [h30, h03]; ring
    · change (F 3 1).val x y = - (F 1 3).val x y; rw [h31, h13]; ring
    · change (F 3 2).val x y = - (F 2 3).val x y; rw[h32, h23]; ring
    · change (F 3 3).val x y = - (F 3 3).val x y; rw [h33]; ring

lemma math_self_dual_components (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) :
  F 0 1 = F 2 3 ∧ F 0 2 = - F 1 3 ∧ F 0 3 = F 1 2 := by
  have h_anti := math_self_dual_antisymmetric F h_symm
  have h01 : F 0 1 = F 2 3 := by
    apply Subtype.ext; ext x y
    have h1 := val_01 F h_symm x y
    have ha := congr_fun (congr_fun (congr_arg Subtype.val (h_anti 3 2)) x) y
    have hn : (- F 2 3).val x y = - (F 2 3).val x y := rfl
    rw [ha, hn] at h1
    rw [h1]; ring

  have h02 : F 0 2 = - F 1 3 := by
    apply Subtype.ext; ext x y
    have h1 := val_02 F h_symm x y
    have ha := congr_fun (congr_fun (congr_arg Subtype.val (h_anti 3 1)) x) y
    have hn : (- F 1 3).val x y = - (F 1 3).val x y := rfl
    rw [ha, hn] at h1
    rw [hn, h1]; ring

  have h03 : F 0 3 = F 1 2 := by
    apply Subtype.ext; ext x y
    have h1 := val_03 F h_symm x y
    have ha := congr_fun (congr_fun (congr_arg Subtype.val (h_anti 2 1)) x) y
    have hn : (- F 1 2).val x y = - (F 1 2).val x y := rfl
    rw [ha, hn] at h1
    rw [h1]; ring

  exact ⟨h01, h02, h03⟩

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

noncomputable def pMat (x y z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j =>
    if i = 0 ∧ j = 1 then x else if i = 0 ∧ j = 2 then y else if i = 0 ∧ j = 3 then z
    else if i = 1 ∧ j = 0 then -x else if i = 1 ∧ j = 2 then z else if i = 1 ∧ j = 3 then -y
    else if i = 2 ∧ j = 0 then -y else if i = 2 ∧ j = 1 then -z else if i = 2 ∧ j = 3 then x
    else if i = 3 ∧ j = 0 then -z else if i = 3 ∧ j = 1 then y else if i = 3 ∧ j = 2 then -x
    else 0

lemma P_mat_anti (x y z : ℂ) (i j : Fin 4) : pMat x y z i j = - pMat x y z j i := by
  unfold pMat
  fin_cases i <;> fin_cases j <;> simp

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

lemma sd_tensor_collapse (P : Fin 4 → Fin 4 → ℂ)
  (h_sd : ∀ γ δ, P γ δ = ∑ ρ : Fin 4, ∑ σ : Fin 4, ((1 / 2 : ℂ) * epsilon4 γ δ ρ σ) * P ρ σ)
  (α β : Fin 4) :
  (∑ γ : Fin 4, ∑ δ : Fin 4, epsilon4 α β γ δ * P γ δ) = 2 * P α β := by
  calc
    (∑ γ : Fin 4, ∑ δ : Fin 4, epsilon4 α β γ δ * P γ δ)
    _ = ∑ ρ : Fin 4, ∑ σ : Fin 4, 2 * ((1 / 2 : ℂ) * epsilon4 α β ρ σ * P ρ σ) := by
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro σ _
      ring
    _ = 2 * ∑ ρ : Fin 4, ∑ σ : Fin 4, ((1 / 2 : ℂ) * epsilon4 α β ρ σ * P ρ σ) := by simp_rw[Finset.mul_sum]
    _ = 2 * P α β := by rw[← h_sd α β]

lemma urbantke_inner_sum_collapse (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a b c : Fin 3) (mu nu : Fin 4) :
  (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    epsilon4 α β γ δ * project F a mu α * project F b nu β * project F c γ δ) =
  ∑ α : Fin 4, ∑ β : Fin 4, 2 * project F a mu α * project F b nu β * project F c α β := by
  apply Finset.sum_congr rfl; intro α _
  apply Finset.sum_congr rfl; intro β _
  have h_sd := sd_tensor_collapse (fun γ δ => project F c γ δ) (project_is_self_dual F h_symm c) α β
  calc
    (∑ γ : Fin 4, ∑ δ : Fin 4, epsilon4 α β γ δ * project F a mu α * project F b nu β * project F c γ δ)
    _ = ∑ γ : Fin 4, ∑ δ : Fin 4, (project F a mu α * project F b nu β) * (epsilon4 α β γ δ * project F c γ δ) := by
        apply Finset.sum_congr rfl; intro γ _
        apply Finset.sum_congr rfl; intro δ _
        ring
    _ = (project F a mu α * project F b nu β) * ∑ γ : Fin 4, ∑ δ : Fin 4, epsilon4 α β γ δ * project F c γ δ := by
        simp_rw [← Finset.mul_sum]
    _ = (project F a mu α * project F b nu β) * (2 * project F c α β) := by rw [h_sd]
    _ = 2 * project F a mu α * project F b nu β * project F c α β := by ring

lemma urbantke_metric_collapsed (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (mu nu : Fin 4) :
  urbantkeMetric F mu nu = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4,
    epsilon3 a b c * (2 * project F a mu α * project F b nu β * project F c α β) := by
  unfold urbantkeMetric
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  have h := urbantke_inner_sum_collapse F h_symm a b c mu nu
  rw [h]
  simp_rw [Finset.mul_sum]

lemma urbantke_symbolic_collapse (A B C : Matrix (Fin 4) (Fin 4) ℂ) (hB_anti : ∀ i j, B i j = - B j i) (μ ν : Fin 4) :
  (∑ α : Fin 4, ∑ β : Fin 4, 2 * A μ α * B ν β * C α β) = -2 * (A * C * B) μ ν := by
  symm
  calc
    -2 * (A * C * B) μ ν
    _ = -2 * ∑ β : Fin 4, (∑ α : Fin 4, A μ α * C α β) * B β ν := rfl
    _ = ∑ β : Fin 4, -2 * ((∑ α : Fin 4, A μ α * C α β) * B β ν) := by rw[Finset.mul_sum]
    _ = ∑ β : Fin 4, ∑ α : Fin 4, -2 * (A μ α * C α β * B β ν) := by
      apply Finset.sum_congr rfl; intro β _
      rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ α : Fin 4, ∑ β : Fin 4, -2 * (A μ α * C α β * B β ν) := by rw [Finset.sum_comm]
    _ = ∑ α : Fin 4, ∑ β : Fin 4, 2 * A μ α * B ν β * C α β := by
      apply Finset.sum_congr rfl; intro α _
      apply Finset.sum_congr rfl; intro β _
      have hb : B ν β = - B β ν := hB_anti ν β
      rw [hb]
      ring

lemma urbantke_symbolic_collapse_neg (A B C : Matrix (Fin 4) (Fin 4) ℂ) (hB_anti : ∀ i j, B i j = - B j i) (μ ν : Fin 4) :
  (∑ α : Fin 4, ∑ β : Fin 4, -(2 * A μ α * B ν β * C α β)) = 2 * (A * C * B) μ ν := by
  symm
  calc
    2 * (A * C * B) μ ν
    _ = 2 * ∑ β : Fin 4, (∑ α : Fin 4, A μ α * C α β) * B β ν := rfl
    _ = ∑ β : Fin 4, 2 * ((∑ α : Fin 4, A μ α * C α β) * B β ν) := by rw [Finset.mul_sum]
    _ = ∑ β : Fin 4, ∑ α : Fin 4, 2 * (A μ α * C α β * B β ν) := by
      apply Finset.sum_congr rfl; intro β _
      rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ α : Fin 4, ∑ β : Fin 4, 2 * (A μ α * C α β * B β ν) := by rw [Finset.sum_comm]
    _ = ∑ α : Fin 4, ∑ β : Fin 4, -(2 * A μ α * B ν β * C α β) := by
      apply Finset.sum_congr rfl; intro α _
      apply Finset.sum_congr rfl; intro β _
      have hb : B ν β = - B β ν := hB_anti ν β
      rw [hb]
      ring

noncomputable def pPoly (F : Fin 4 → Fin 4 → SL2C) : Matrix (Fin 4) (Fin 4) ℂ :=
  let P0 := pMat (bField F 0 0) (bField F 0 1) (bField F 0 2)
  let P1 := pMat (bField F 1 0) (bField F 1 1) (bField F 1 2)
  let P2 := pMat (bField F 2 0) (bField F 2 1) (bField F 2 2)
  (2 : ℂ) • (P0 * P1 * P2 - P0 * P2 * P1 - P1 * P0 * P2 + P1 * P2 * P0 + P2 * P0 * P1 - P2 * P1 * P0)

lemma eval_eps3_sum (f : Fin 3 → Fin 3 → Fin 3 → ℂ) :
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * f a b c) =
  f 0 1 2 - f 0 2 1 - f 1 0 2 + f 1 2 0 + f 2 0 1 - f 2 1 0 := by
  simp only [sum_fin_3_expand]
  unfold epsilon3
  dsimp [epsilon3_int]
  ring

lemma eval_mul_4x4_3 (A B C : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
  (A * B * C) i j =
    (A i 0 * B 0 0 + A i 1 * B 1 0 + A i 2 * B 2 0 + A i 3 * B 3 0) * C 0 j +
    (A i 0 * B 0 1 + A i 1 * B 1 1 + A i 2 * B 2 1 + A i 3 * B 3 1) * C 1 j +
    (A i 0 * B 0 2 + A i 1 * B 1 2 + A i 2 * B 2 2 + A i 3 * B 3 2) * C 2 j +
    (A i 0 * B 0 3 + A i 1 * B 1 3 + A i 2 * B 2 3 + A i 3 * B 3 3) * C 3 j := by
  simp only [Matrix.mul_apply, sum_fin_4_expand]

lemma P_poly_is_id (x0 x1 x2 y0 y1 y2 z0 z1 z2 : ℂ) :
  ∃ c : ℂ, ((2:ℂ) • (pMat x0 x1 x2 * pMat y0 y1 y2 * pMat z0 z1 z2
                - pMat x0 x1 x2 * pMat z0 z1 z2 * pMat y0 y1 y2
                - pMat y0 y1 y2 * pMat x0 x1 x2 * pMat z0 z1 z2
                + pMat y0 y1 y2 * pMat z0 z1 z2 * pMat x0 x1 x2
                + pMat z0 z1 z2 * pMat x0 x1 x2 * pMat y0 y1 y2
                - pMat z0 z1 z2 * pMat y0 y1 y2 * pMat x0 x1 x2) : Matrix (Fin 4) (Fin 4) ℂ) = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  use 12 * (x0 * y1 * z2 - x0 * y2 * z1 - x1 * y0 * z2 + x1 * y2 * z0 + x2 * y0 * z1 - x2 * y1 * z0)
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp only[Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    simp only [eval_mul_4x4_3]
    simp [pMat, Matrix.one_apply]
    ring
  }

lemma P_poly_prop_id (F : Fin 4 → Fin 4 → SL2C) :
  ∃ (c : Complex), pPoly F = c • (1 : Matrix (Fin 4) (Fin 4) Complex) := by
  unfold pPoly
  apply P_poly_is_id

lemma urbantke_eq_P_poly (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) :
  urbantkeMetric F = pPoly F := by
  ext μ ν
  rw [urbantke_metric_collapsed F h_symm]

  have h_sum_rearrange :
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4,
      epsilon3 a b c * (2 * project F a μ α * project F b ν β * project F c α β)) =
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (∑ α : Fin 4, ∑ β : Fin 4, 2 * project F a μ α * project F b ν β * project F c α β)) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro α _
    rw [Finset.mul_sum]

  rw[h_sum_rearrange]

  have h_eps := eval_eps3_sum (fun a b c => ∑ α : Fin 4, ∑ β : Fin 4, 2 * project F a μ α * project F b ν β * project F c α β)
  rw [h_eps]

  have h_anti0 : ∀ i j, project F 0 i j = - project F 0 j i := project_anti F h_symm 0
  have h_anti1 : ∀ i j, project F 1 i j = - project F 1 j i := project_anti F h_symm 1
  have h_anti2 : ∀ i j, project F 2 i j = - project F 2 j i := project_anti F h_symm 2

  rw[urbantke_symbolic_collapse (project F 0) (project F 1) (project F 2) h_anti1 μ ν]
  rw[urbantke_symbolic_collapse (project F 0) (project F 2) (project F 1) h_anti2 μ ν]
  rw[urbantke_symbolic_collapse (project F 1) (project F 0) (project F 2) h_anti0 μ ν]
  rw[urbantke_symbolic_collapse (project F 1) (project F 2) (project F 0) h_anti2 μ ν]
  rw[urbantke_symbolic_collapse (project F 2) (project F 0) (project F 1) h_anti0 μ ν]
  rw[urbantke_symbolic_collapse (project F 2) (project F 1) (project F 0) h_anti1 μ ν]

  have eq0 : project F 0 = pMat (bField F 0 0) (bField F 0 1) (bField F 0 2) := by ext i j; exact project_eq_P_mat F h_symm 0 i j
  have eq1 : project F 1 = pMat (bField F 1 0) (bField F 1 1) (bField F 1 2) := by ext i j; exact project_eq_P_mat F h_symm 1 i j
  have eq2 : project F 2 = pMat (bField F 2 0) (bField F 2 1) (bField F 2 2) := by ext i j; exact project_eq_P_mat F h_symm 2 i j

  rw [eq0, eq1, eq2]
  unfold pPoly
  simp only[Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Matrix.neg_apply]
  ring

lemma urbantke_eq_smul_id_of_self_dual (F : Fin 4 → Fin 4 → SL2C)
  (h_symm : isFully4DSymmetric F) :
  ∃ (c : Complex), urbantkeMetric F = c • (1 : Matrix (Fin 4) (Fin 4) Complex) := by
  rcases P_poly_prop_id F with ⟨c, hc⟩
  use c
  rw[urbantke_eq_P_poly F h_symm]
  exact hc

lemma math_TimeIsChiralPhase_det (F : Fin 4 → Fin 4 → SL2C)
  (h_symm : isFully4DSymmetric F) :
  ¬ isLorentzian (urbantkeMetric F) := by
  have ⟨c, hc⟩ := urbantke_eq_smul_id_of_self_dual F h_symm
  rw [hc]
  unfold isLorentzian

  intro h_lor
  rcases h_lor with ⟨h_im, h_det_re, h_det_im⟩

  have h_det : (c • (1 : Matrix (Fin 4) (Fin 4) Complex)).det = c^4 := by simp
  rw [h_det] at h_det_re
  rw[h_det] at h_det_im

  have hc_re : c.im = 0 := by
    have h_c_val := h_im 0 0
    simp only[Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h_c_val
    exact h_c_val

  have hc_complex : c = (c.re : ℂ) := Complex.ext rfl hc_re
  rw[hc_complex] at h_det_re

  have h_pow_re : (((c.re : ℂ)^4).re) = c.re^4 := by
    have h_sq : (c.re : ℂ)^4 = ((c.re^4 : ℝ) : ℂ) := by push_cast; ring
    rw [h_sq]
    rfl

  rw [h_pow_re] at h_det_re
  have h_even : Even 4 := by decide
  have h_pos : 0 ≤ c.re^4 := Even.pow_nonneg h_even c.re
  linarith

Litlib.theorem
  description "Time Emergence via Symmetry Breaking"
/--
A fully 4D symmetric field tensor naturally yields a metric with a Euclidean or degenerate signature, forbidding the unique odd-sign axis required for a Lorentzian signature. Therefore, the Lorentzian time dimension emerges geometrically only when the gauge field spontaneously breaks 4D Euclidean (SO(4)) symmetry.
-/
theorem kinematicTimeEmergence (u : Universe)
  (h_tic : ∀ x, x 0 = 0 → isFully4DSymmetric (fun mu nu => curvatureSl2c u.sd_sector mu nu x)) :
  ∀ (x : SpacetimePoint),
    x 0 = 0 →
    ¬ isLorentzian (urbantkeMetric (fun m n => curvatureSl2c u.sd_sector m n x)) := by
  intro x hx
  have h_symm := h_tic x hx
  exact math_TimeIsChiralPhase_det (fun mu nu => curvatureSl2c u.sd_sector mu nu x) h_symm

end CGD.Cosmology

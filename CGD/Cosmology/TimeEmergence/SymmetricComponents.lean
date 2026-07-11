-- FILENAME: CGD/Cosmology/TimeEmergence/SymmetricComponents.lean

import Litlib.Core
import CGD.Cosmology.Definitions
import CGD.Gravity.Geometry
import CGD.Math.Matrix
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open CGD.Math CGD.Foundations CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Cosmology

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

end CGD.Cosmology

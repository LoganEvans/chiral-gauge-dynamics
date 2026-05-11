-- FILENAME: CGD/Gravity/Urbantke.lean

import CGD.Gravity.Geometry
import CGD.Gravity.MacroscopicVacuum
import CGD.Foundations.GaugeGroup
import Litlib.Math.Leverrier
import Litlib.Math.Matrix4
import Litlib.Math.EpsilonDeterminant
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Trace

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations

-- ============================================================================
-- PHASE 1: TRUE PLEBANSKI EXTRACTOR
-- ============================================================================

lemma plebanski_wedge_eval (Λ : ℂ) (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_plebanski : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
      epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1)
  (i j : Fin 3) :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
    epsilon4 μ ν ρ σ * ∑ k : Fin 3, F μ ν i k * F ρ σ k j) = Λ * (if i = j then (1:ℂ) else 0) := by
  have h := congr_fun (congr_fun h_plebanski i) j
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] at h
  exact h

def F_iso (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3) (μ ν : Fin 4) : ℂ :=
  if a = 0 then F μ ν 1 2 else if a = 1 then F μ ν 2 0 else F μ ν 0 1

lemma sum_fin_3_complex (f : Fin 3 → ℂ) :
  (∑ i : Fin 3, f i) = f 0 + f 1 + f 2 := by
  simp [Fin.sum_univ_succ, add_assoc]

lemma F_eq_iso (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_su2 : ∀ μ ν, F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧ 
    F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1)
  (μ ν : Fin 4) :
  F μ ν 0 0 = 0 ∧
  F μ ν 1 1 = 0 ∧
  F μ ν 2 2 = 0 ∧
  F μ ν 1 2 = F_iso F 0 μ ν ∧
  F μ ν 2 1 = - F_iso F 0 μ ν ∧
  F μ ν 2 0 = F_iso F 1 μ ν ∧
  F μ ν 0 2 = - F_iso F 1 μ ν ∧
  F μ ν 0 1 = F_iso F 2 μ ν ∧
  F μ ν 1 0 = - F_iso F 2 μ ν := by
  rcases h_su2 μ ν with ⟨h00, h11, h22, h21, h20, h10⟩
  have hi0 : F_iso F 0 μ ν = F μ ν 1 2 := rfl
  have hi1 : F_iso F 1 μ ν = F μ ν 2 0 := rfl
  have hi2 : F_iso F 2 μ ν = F μ ν 0 1 := rfl
  refine ⟨h00, h11, h22, hi0.symm, ?_, hi1.symm, ?_, hi2.symm, ?_⟩
  · rw [hi0, h21]
  · rw [hi1]
    calc F μ ν 0 2 = - (- F μ ν 0 2) := by ring
    _ = - F μ ν 2 0 := by rw [h20]
  · rw [hi2, h10]

lemma wedge_iso_eval (Λ : ℂ) (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ)
  (h_su2 : ∀ μ ν, F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧ 
    F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1)
  (h_plebanski : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
      epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1)
  (a b : Fin 3) :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
    epsilon4 μ ν ρ σ * F_iso F a μ ν * F_iso F b ρ σ) = (-Λ / 2) * (if a = b then (1:ℂ) else 0) := by
  
  let S := fun a b => ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * F_iso F a μ ν * F_iso F b ρ σ

  have e00 : - S 2 2 - S 1 1 = Λ := by
    have h := plebanski_wedge_eval Λ F h_plebanski 0 0
    have h_rhs : Λ * (if (0:Fin 3) = 0 then (1:ℂ) else 0) = Λ := by simp
    rw [h_rhs] at h
    have h_lhs : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * ∑ k : Fin 3, F μ ν 0 k * F ρ σ k 0) = - S 2 2 - S 1 1 := by
      dsimp [S]
      simp only [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← mul_neg, ← mul_sub]
      apply Finset.sum_congr rfl; intro μ _
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro σ _
      have h1 := F_eq_iso F h_su2 μ ν; have h2 := F_eq_iso F h_su2 ρ σ
      rcases h1 with ⟨i00, i11, i22, i12, i21, i20, i02, i01, i10⟩
      rcases h2 with ⟨j00, j11, j22, j12, j21, j20, j02, j01, j10⟩
      simp only [sum_fin_3_complex]
      rw [i00, j00, i01, j10, i02, j20]
      ring
    rwa [h_lhs] at h

  have e11 : - S 2 2 - S 0 0 = Λ := by
    have h := plebanski_wedge_eval Λ F h_plebanski 1 1
    have h_rhs : Λ * (if (1:Fin 3) = 1 then (1:ℂ) else 0) = Λ := by simp
    rw [h_rhs] at h
    have h_lhs : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * ∑ k : Fin 3, F μ ν 1 k * F ρ σ k 1) = - S 2 2 - S 0 0 := by
      dsimp [S]
      simp only [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← mul_neg, ← mul_sub]
      apply Finset.sum_congr rfl; intro μ _
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro σ _
      have h1 := F_eq_iso F h_su2 μ ν; have h2 := F_eq_iso F h_su2 ρ σ
      rcases h1 with ⟨i00, i11, i22, i12, i21, i20, i02, i01, i10⟩
      rcases h2 with ⟨j00, j11, j22, j12, j21, j20, j02, j01, j10⟩
      simp only [sum_fin_3_complex]
      rw [i10, j01, i11, j11, i12, j21]
      ring
    rwa [h_lhs] at h

  have e22 : - S 1 1 - S 0 0 = Λ := by
    have h := plebanski_wedge_eval Λ F h_plebanski 2 2
    have h_rhs : Λ * (if (2:Fin 3) = 2 then (1:ℂ) else 0) = Λ := by simp
    rw [h_rhs] at h
    have h_lhs : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * ∑ k : Fin 3, F μ ν 2 k * F ρ σ k 2) = - S 1 1 - S 0 0 := by
      dsimp [S]
      simp only [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← mul_neg, ← mul_sub]
      apply Finset.sum_congr rfl; intro μ _
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro σ _
      have h1 := F_eq_iso F h_su2 μ ν; have h2 := F_eq_iso F h_su2 ρ σ
      rcases h1 with ⟨i00, i11, i22, i12, i21, i20, i02, i01, i10⟩
      rcases h2 with ⟨j00, j11, j22, j12, j21, j20, j02, j01, j10⟩
      simp only [sum_fin_3_complex]
      rw [i20, j02, i21, j12, i22, j22]
      ring
    rwa [h_lhs] at h

  have e01 : S 1 0 = 0 := by
    have h := plebanski_wedge_eval Λ F h_plebanski 0 1
    have h_rhs : Λ * (if (0:Fin 3) = 1 then (1:ℂ) else 0) = 0 := by simp
    rw [h_rhs] at h
    have h_lhs : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * ∑ k : Fin 3, F μ ν 0 k * F ρ σ k 1) = S 1 0 := by
      dsimp [S]
      apply Finset.sum_congr rfl; intro μ _
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro σ _
      have h1 := F_eq_iso F h_su2 μ ν; have h2 := F_eq_iso F h_su2 ρ σ
      rcases h1 with ⟨i00, i11, i22, i12, i21, i20, i02, i01, i10⟩
      rcases h2 with ⟨j00, j11, j22, j12, j21, j20, j02, j01, j10⟩
      simp only [sum_fin_3_complex]
      rw [i00, j01, i01, j11, i02, j21]
      ring
    rwa [h_lhs] at h

  have e02 : S 2 0 = 0 := by
    have h := plebanski_wedge_eval Λ F h_plebanski 0 2
    have h_rhs : Λ * (if (0:Fin 3) = 2 then (1:ℂ) else 0) = 0 := by simp
    rw [h_rhs] at h
    have h_lhs : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * ∑ k : Fin 3, F μ ν 0 k * F ρ σ k 2) = S 2 0 := by
      dsimp [S]
      apply Finset.sum_congr rfl; intro μ _
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro σ _
      have h1 := F_eq_iso F h_su2 μ ν; have h2 := F_eq_iso F h_su2 ρ σ
      rcases h1 with ⟨i00, i11, i22, i12, i21, i20, i02, i01, i10⟩
      rcases h2 with ⟨j00, j11, j22, j12, j21, j20, j02, j01, j10⟩
      simp only [sum_fin_3_complex]
      rw [i00, j02, i01, j12, i02, j22]
      ring
    rwa [h_lhs] at h

  have e10 : S 0 1 = 0 := by
    have h := plebanski_wedge_eval Λ F h_plebanski 1 0
    have h_rhs : Λ * (if (1:Fin 3) = 0 then (1:ℂ) else 0) = 0 := by simp
    rw [h_rhs] at h
    have h_lhs : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * ∑ k : Fin 3, F μ ν 1 k * F ρ σ k 0) = S 0 1 := by
      dsimp [S]
      apply Finset.sum_congr rfl; intro μ _
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro σ _
      have h1 := F_eq_iso F h_su2 μ ν; have h2 := F_eq_iso F h_su2 ρ σ
      rcases h1 with ⟨i00, i11, i22, i12, i21, i20, i02, i01, i10⟩
      rcases h2 with ⟨j00, j11, j22, j12, j21, j20, j02, j01, j10⟩
      simp only [sum_fin_3_complex]
      rw [i10, j00, i11, j10, i12, j20]
      ring
    rwa [h_lhs] at h

  have e12 : S 2 1 = 0 := by
    have h := plebanski_wedge_eval Λ F h_plebanski 1 2
    have h_rhs : Λ * (if (1:Fin 3) = 2 then (1:ℂ) else 0) = 0 := by simp
    rw [h_rhs] at h
    have h_lhs : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * ∑ k : Fin 3, F μ ν 1 k * F ρ σ k 2) = S 2 1 := by
      dsimp [S]
      apply Finset.sum_congr rfl; intro μ _
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro σ _
      have h1 := F_eq_iso F h_su2 μ ν; have h2 := F_eq_iso F h_su2 ρ σ
      rcases h1 with ⟨i00, i11, i22, i12, i21, i20, i02, i01, i10⟩
      rcases h2 with ⟨j00, j11, j22, j12, j21, j20, j02, j01, j10⟩
      simp only [sum_fin_3_complex]
      rw [i10, j02, i11, j12, i12, j22]
      ring
    rwa [h_lhs] at h

  have e20 : S 0 2 = 0 := by
    have h := plebanski_wedge_eval Λ F h_plebanski 2 0
    have h_rhs : Λ * (if (2:Fin 3) = 0 then (1:ℂ) else 0) = 0 := by simp
    rw [h_rhs] at h
    have h_lhs : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * ∑ k : Fin 3, F μ ν 2 k * F ρ σ k 0) = S 0 2 := by
      dsimp [S]
      apply Finset.sum_congr rfl; intro μ _
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro σ _
      have h1 := F_eq_iso F h_su2 μ ν; have h2 := F_eq_iso F h_su2 ρ σ
      rcases h1 with ⟨i00, i11, i22, i12, i21, i20, i02, i01, i10⟩
      rcases h2 with ⟨j00, j11, j22, j12, j21, j20, j02, j01, j10⟩
      simp only [sum_fin_3_complex]
      rw [i20, j00, i21, j10, i22, j20]
      ring
    rwa [h_lhs] at h

  have e21 : S 1 2 = 0 := by
    have h := plebanski_wedge_eval Λ F h_plebanski 2 1
    have h_rhs : Λ * (if (2:Fin 3) = 1 then (1:ℂ) else 0) = 0 := by simp
    rw [h_rhs] at h
    have h_lhs : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * ∑ k : Fin 3, F μ ν 2 k * F ρ σ k 1) = S 1 2 := by
      dsimp [S]
      apply Finset.sum_congr rfl; intro μ _
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro σ _
      have h1 := F_eq_iso F h_su2 μ ν; have h2 := F_eq_iso F h_su2 ρ σ
      rcases h1 with ⟨i00, i11, i22, i12, i21, i20, i02, i01, i10⟩
      rcases h2 with ⟨j00, j11, j22, j12, j21, j20, j02, j01, j10⟩
      simp only [sum_fin_3_complex]
      rw [i20, j01, i21, j11, i22, j21]
      ring
    rwa [h_lhs] at h

  have hS00 : S 0 0 = -Λ / 2 := by
    have h : 2 * S 0 0 = -Λ := by
      calc 2 * S 0 0 = - (- S 1 1 - S 0 0) - (- S 2 2 - S 0 0) + (- S 2 2 - S 1 1) := by ring
      _ = - Λ - Λ + Λ := by rw [e22, e11, e00]
      _ = -Λ := by ring
    calc S 0 0 = (2 * S 0 0) / 2 := by ring
    _ = -Λ / 2 := by rw [h]

  have hS11 : S 1 1 = -Λ / 2 := by
    have h : 2 * S 1 1 = -Λ := by
      calc 2 * S 1 1 = - (- S 2 2 - S 1 1) - (- S 1 1 - S 0 0) + (- S 2 2 - S 0 0) := by ring
      _ = - Λ - Λ + Λ := by rw [e00, e22, e11]
      _ = -Λ := by ring
    calc S 1 1 = (2 * S 1 1) / 2 := by ring
    _ = -Λ / 2 := by rw [h]

  have hS22 : S 2 2 = -Λ / 2 := by
    have h : 2 * S 2 2 = -Λ := by
      calc 2 * S 2 2 = - (- S 2 2 - S 1 1) - (- S 2 2 - S 0 0) + (- S 1 1 - S 0 0) := by ring
      _ = - Λ - Λ + Λ := by rw [e00, e11, e22]
      _ = -Λ := by ring
    calc S 2 2 = (2 * S 2 2) / 2 := by ring
    _ = -Λ / 2 := by rw [h]

  have hS01 : S 0 1 = 0 := e10
  have hS02 : S 0 2 = 0 := e20
  have hS10 : S 1 0 = 0 := e01
  have hS12 : S 1 2 = 0 := e21
  have hS20 : S 2 0 = 0 := e02
  have hS21 : S 2 1 = 0 := e12

  have h_match : ∀ i j : Fin 3, S i j = (-Λ / 2) * (if i = j then (1:ℂ) else 0) := by
    intro i j
    fin_cases i <;> fin_cases j
    · simp; exact hS00
    · simp; exact hS01
    · simp; exact hS02
    · simp; exact hS10
    · simp; exact hS11
    · simp; exact hS12
    · simp; exact hS20
    · simp; exact hS21
    · simp; exact hS22
  exact h_match a b

-- ============================================================================
-- PHASE 2: URBANTKE METRIC EXPANSION
-- ============================================================================

lemma sum_fin_2_complex (f : Fin 2 → ℂ) :
  (∑ i : Fin 2, f i) = f 0 + f 1 := by
  simp [Fin.sum_univ_succ]

lemma project_eval_0 (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (μ ν : Fin 4) :
  project (fun m n => toSl2c (F m n 1 2 • sigma1.val + F m n 2 0 • sigma2.val + F m n 0 1 • sigma3.val)) 0 μ ν = F μ ν 1 2 := by
  unfold project getPauli toSl2c
  simp only [val_sigma1, val_sigma2, val_sigma3]
  unfold sigmaX sigmaY sigmaZ mkMat
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, sum_fin_2_complex]
  ring

lemma project_eval_1 (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (μ ν : Fin 4) :
  project (fun m n => toSl2c (F m n 1 2 • sigma1.val + F m n 2 0 • sigma2.val + F m n 0 1 • sigma3.val)) 1 μ ν = F μ ν 2 0 := by
  unfold project getPauli toSl2c
  simp only [val_sigma1, val_sigma2, val_sigma3]
  unfold sigmaX sigmaY sigmaZ mkMat
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, sum_fin_2_complex]
  ring_nf
  simp [Complex.I_sq]

lemma project_eval_2 (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (μ ν : Fin 4) :
  project (fun m n => toSl2c (F m n 1 2 • sigma1.val + F m n 2 0 • sigma2.val + F m n 0 1 • sigma3.val)) 2 μ ν = F μ ν 0 1 := by
  unfold project getPauli toSl2c
  simp only [val_sigma1, val_sigma2, val_sigma3]
  unfold sigmaX sigmaY sigmaZ mkMat
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, sum_fin_2_complex]
  ring

lemma project_eq_F_iso (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3) (μ ν : Fin 4) :
  project (fun m n => toSl2c (F m n 1 2 • sigma1.val + F m n 2 0 • sigma2.val + F m n 0 1 • sigma3.val)) a μ ν = F_iso F a μ ν := by
  unfold F_iso
  fin_cases a
  · simp [project_eval_0]
  · simp [project_eval_1]
  · simp [project_eval_2]

lemma g_covariant_eval (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (μ ν : Fin 4) :
  (cgdUnimodularMetricAdapter F) μ ν = 
    ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      epsilon3 a b c *
      ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
        epsilon4 α β γ δ * F_iso F a μ α * F_iso F b ν β * F_iso F c γ δ := by
  unfold cgdUnimodularMetricAdapter urbantkeMetric
  simp_rw [project_eq_F_iso]

-- ============================================================================
-- PHASE 3: COVARIANT CONTRACTION ENGINE (AST PRUNED)
-- ============================================================================

lemma sum_fin_4_complex (f : Fin 4 → ℂ) :
  (∑ i : Fin 4, f i) = f 0 + f 1 + f 2 + f 3 := by
  simp [Fin.sum_univ_succ, add_assoc]

lemma expand_cgd_epsilon (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
  (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, epsilon4 α β γ δ * f α β γ δ) =
    f 0 1 2 3 - f 0 1 3 2 - f 0 2 1 3 + f 0 2 3 1 + f 0 3 1 2 - f 0 3 2 1
  - f 1 0 2 3 + f 1 0 3 2 + f 1 2 0 3 - f 1 2 3 0 - f 1 3 0 2 + f 1 3 2 0
  + f 2 0 1 3 - f 2 0 3 1 - f 2 1 0 3 + f 2 1 3 0 + f 2 3 0 1 - f 2 3 1 0
  - f 3 0 1 2 + f 3 0 2 1 + f 3 1 0 2 - f 3 1 2 0 - f 3 2 0 1 + f 3 2 1 0 := by
  simp only [sum_fin_4_complex, epsilon4, epsilon4_int]
  ring

lemma antisymm_zero (A : Fin 4 → Fin 4 → ℂ) (hA : ∀ i j, A i j = -A j i) (i : Fin 4) : A i i = 0 := by
  have h : A i i = - A i i := hA i i
  have h2 : A i i + A i i = 0 := by
    calc A i i + A i i = A i i - (- A i i) := by ring
    _ = A i i - A i i := by rw [← h]
    _ = 0 := by ring
  calc A i i = (A i i + A i i) / 2 := by ring
  _ = 0 / 2 := by rw [h2]
  _ = 0 := by ring

lemma antisymm_cases (A : Fin 4 → Fin 4 → ℂ) (hA : ∀ i j, A i j = -A j i) :
  A 0 0 = 0 ∧ A 1 1 = 0 ∧ A 2 2 = 0 ∧ A 3 3 = 0 ∧
  A 1 0 = -A 0 1 ∧ A 2 0 = -A 0 2 ∧ A 3 0 = -A 0 3 ∧
  A 2 1 = -A 1 2 ∧ A 3 1 = -A 1 3 ∧ A 3 2 = -A 2 3 := 
  ⟨antisymm_zero A hA 0, antisymm_zero A hA 1, antisymm_zero A hA 2, antisymm_zero A hA 3, 
   hA 1 0, hA 2 0, hA 3 0, hA 2 1, hA 3 1, hA 3 2⟩

-- Isolates the unifier from searching the 256-term AST
noncomputable def eps_sum (B : Fin 4 → Fin 4 → ℂ) (ρ ν : Fin 4) : ℂ :=
  ∑ α : Fin 4, ∑ β : Fin 4, epsilon4 ρ ν α β * B α β

@[simp] lemma eps_sum_00 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 0 0 = 0 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_01 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 0 1 = B 2 3 - B 3 2 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_02 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 0 2 = B 3 1 - B 1 3 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_03 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 0 3 = B 1 2 - B 2 1 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_10 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 1 0 = B 3 2 - B 2 3 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_11 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 1 1 = 0 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_12 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 1 2 = B 0 3 - B 3 0 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_13 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 1 3 = B 2 0 - B 0 2 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_20 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 2 0 = B 1 3 - B 3 1 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_21 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 2 1 = B 3 0 - B 0 3 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_22 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 2 2 = 0 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_23 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 2 3 = B 0 1 - B 1 0 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_30 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 3 0 = B 2 1 - B 1 2 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_31 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 3 1 = B 0 2 - B 2 0 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_32 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 3 2 = B 1 0 - B 0 1 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring
@[simp] lemma eps_sum_33 (B : Fin 4 → Fin 4 → ℂ) : eps_sum B 3 3 = 0 := by unfold eps_sum; simp only [sum_fin_4_complex, epsilon4, epsilon4_int]; ring

lemma generic_hodge_anticommutator (A B : Fin 4 → Fin 4 → ℂ)
  (hA : ∀ i j, A i j = -A j i) (hB : ∀ i j, B i j = -B j i) (μ ν : Fin 4) :
  (∑ ρ : Fin 4, A μ ρ * eps_sum B ρ ν) +
  (∑ ρ : Fin 4, B μ ρ * eps_sum A ρ ν) =
  (if μ = ν then (1:ℂ) else 0) * (-1/4) * (∑ a1 : Fin 4, ∑ b1 : Fin 4, ∑ c1 : Fin 4, ∑ d1 : Fin 4, epsilon4 a1 b1 c1 d1 * (A a1 b1 * B c1 d1 + B a1 b1 * A c1 d1)) := by
  
  rw [expand_cgd_epsilon (fun a1 b1 c1 d1 => A a1 b1 * B c1 d1 + B a1 b1 * A c1 d1)]
  
  have h_sum1 : (∑ ρ : Fin 4, A μ ρ * eps_sum B ρ ν) = A μ 0 * eps_sum B 0 ν + A μ 1 * eps_sum B 1 ν + A μ 2 * eps_sum B 2 ν + A μ 3 * eps_sum B 3 ν := sum_fin_4_complex (fun ρ => A μ ρ * eps_sum B ρ ν)
  have h_sum2 : (∑ ρ : Fin 4, B μ ρ * eps_sum A ρ ν) = B μ 0 * eps_sum A 0 ν + B μ 1 * eps_sum A 1 ν + B μ 2 * eps_sum A 2 ν + B μ 3 * eps_sum A 3 ν := sum_fin_4_complex (fun ρ => B μ ρ * eps_sum A ρ ν)
  rw [h_sum1, h_sum2]

  rcases antisymm_cases A hA with ⟨A00, A11, A22, A33, A10, A20, A30, A21, A31, A32⟩
  rcases antisymm_cases B hB with ⟨B00, B11, B22, B33, B10, B20, B30, B21, B31, B32⟩

  fin_cases μ <;> fin_cases ν
  all_goals {
    simp
    try simp [A00, A11, A22, A33, A10, A20, A30, A21, A31, A32, B00, B11, B22, B33, B10, B20, B30, B21, B31, B32]
    ring
  }

noncomputable def hodgeDual (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3) (μ ν : Fin 4) : ℂ :=
  eps_sum (F_iso F a) μ ν

lemma F_iso_antisymm (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ) (a : Fin 3) (μ ν : Fin 4) :
  F_iso F a μ ν = - F_iso F a ν μ := by
  unfold F_iso
  have h := h_antisymm μ ν
  have h1 : F μ ν 1 2 = - F ν μ 1 2 := by rw [h]; rfl
  have h2 : F μ ν 2 0 = - F ν μ 2 0 := by rw [h]; rfl
  have h3 : F μ ν 0 1 = - F ν μ 0 1 := by rw [h]; rfl
  split_ifs
  · exact h1
  · exact h2
  · exact h3

lemma hodge_anticommutator (Λ : ℂ) (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ)
  (h_su2 : ∀ μ ν, F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧ 
    F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1)
  (h_plebanski : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
      epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1)
  (a b : Fin 3) (μ ν : Fin 4) :
  (∑ ρ : Fin 4, (F_iso F a μ ρ * hodgeDual F b ρ ν + F_iso F b μ ρ * hodgeDual F a ρ ν)) = 
    (Λ / 4) * (if a = b then (1:ℂ) else 0) * (if μ = ν then (1:ℂ) else 0) := by
  
  have h_gen := generic_hodge_anticommutator (F_iso F a) (F_iso F b) (F_iso_antisymm F h_antisymm a) (F_iso_antisymm F h_antisymm b) μ ν

  have h_lhs_eq : (∑ ρ : Fin 4, (F_iso F a μ ρ * hodgeDual F b ρ ν + F_iso F b μ ρ * hodgeDual F a ρ ν)) = 
    (∑ ρ : Fin 4, F_iso F a μ ρ * eps_sum (F_iso F b) ρ ν) +
    (∑ ρ : Fin 4, F_iso F b μ ρ * eps_sum (F_iso F a) ρ ν) := by
    unfold hodgeDual
    rw [Finset.sum_add_distrib]

  have h_wedge_ab := wedge_iso_eval Λ F h_antisymm h_su2 h_plebanski a b
  have h_wedge_ba := wedge_iso_eval Λ F h_antisymm h_su2 h_plebanski b a

  have h_sum_split : (∑ a1 : Fin 4, ∑ b1 : Fin 4, ∑ c1 : Fin 4, ∑ d1 : Fin 4, epsilon4 a1 b1 c1 d1 * (F_iso F a a1 b1 * F_iso F b c1 d1 + F_iso F b a1 b1 * F_iso F a c1 d1)) =
    (∑ a1 : Fin 4, ∑ b1 : Fin 4, ∑ c1 : Fin 4, ∑ d1 : Fin 4, epsilon4 a1 b1 c1 d1 * F_iso F a a1 b1 * F_iso F b c1 d1) +
    (∑ a1 : Fin 4, ∑ b1 : Fin 4, ∑ c1 : Fin 4, ∑ d1 : Fin 4, epsilon4 a1 b1 c1 d1 * F_iso F b a1 b1 * F_iso F a c1 d1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a1 _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b1 _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro c1 _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro d1 _
    ring

  have h_ab_eq : (∑ a1 : Fin 4, ∑ b1 : Fin 4, ∑ c1 : Fin 4, ∑ d1 : Fin 4, epsilon4 a1 b1 c1 d1 * F_iso F a a1 b1 * F_iso F b c1 d1) = (-Λ / 2) * (if a = b then (1:ℂ) else 0) := h_wedge_ab
  have h_ba_eq : (∑ a1 : Fin 4, ∑ b1 : Fin 4, ∑ c1 : Fin 4, ∑ d1 : Fin 4, epsilon4 a1 b1 c1 d1 * F_iso F b a1 b1 * F_iso F a c1 d1) = (-Λ / 2) * (if b = a then (1:ℂ) else 0) := h_wedge_ba

  have h_symm : (if b = a then (1:ℂ) else 0) = (if a = b then (1:ℂ) else 0) := by
    split_ifs with h_ba h_ab h_ab2
    · rfl
    · exact False.elim (h_ab h_ba.symm)
    · exact False.elim (h_ba h_ab2.symm)
    · rfl

  calc
    (∑ ρ : Fin 4, (F_iso F a μ ρ * hodgeDual F b ρ ν + F_iso F b μ ρ * hodgeDual F a ρ ν))
    _ = (∑ ρ : Fin 4, F_iso F a μ ρ * eps_sum (F_iso F b) ρ ν) +
        (∑ ρ : Fin 4, F_iso F b μ ρ * eps_sum (F_iso F a) ρ ν) := h_lhs_eq
    _ = (if μ = ν then (1:ℂ) else 0) * (-1/4) * (∑ a1 : Fin 4, ∑ b1 : Fin 4, ∑ c1 : Fin 4, ∑ d1 : Fin 4, epsilon4 a1 b1 c1 d1 * (F_iso F a a1 b1 * F_iso F b c1 d1 + F_iso F b a1 b1 * F_iso F a c1 d1)) := h_gen
    _ = (if μ = ν then (1:ℂ) else 0) * (-1/4) * (
          (∑ a1 : Fin 4, ∑ b1 : Fin 4, ∑ c1 : Fin 4, ∑ d1 : Fin 4, epsilon4 a1 b1 c1 d1 * F_iso F a a1 b1 * F_iso F b c1 d1) +
          (∑ a1 : Fin 4, ∑ b1 : Fin 4, ∑ c1 : Fin 4, ∑ d1 : Fin 4, epsilon4 a1 b1 c1 d1 * F_iso F b a1 b1 * F_iso F a c1 d1)
        ) := by rw [h_sum_split]
    _ = (if μ = ν then (1:ℂ) else 0) * (-1/4) * (
          (-Λ / 2) * (if a = b then (1:ℂ) else 0) +
          (-Λ / 2) * (if b = a then (1:ℂ) else 0)
        ) := by rw [h_ab_eq, h_ba_eq]
    _ = (if μ = ν then (1:ℂ) else 0) * (-1/4) * (
          (-Λ / 2) * (if a = b then (1:ℂ) else 0) +
          (-Λ / 2) * (if a = b then (1:ℂ) else 0)
        ) := by rw [h_symm]
    _ = (Λ / 4) * (if a = b then (1:ℂ) else 0) * (if μ = ν then (1:ℂ) else 0) := by ring

-- ============================================================================
-- ABSTRACT MATRIX CLIFFORD ALGEBRA
-- ============================================================================

noncomputable def F_mat (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ ν => F_iso F a μ ν

noncomputable def F_tilde (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ ν => hodgeDual F a μ ν

lemma F_mat_antisymm (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ) (a : Fin 3) (μ ν : Fin 4) :
  F_mat F a μ ν = - F_mat F a ν μ := by
  exact F_iso_antisymm F h_antisymm a μ ν

lemma F_mat_anticomm (Λ : ℂ) (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ)
  (h_su2 : ∀ μ ν, F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧ 
    F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1)
  (h_plebanski : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
      epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1)
  (a b : Fin 3) :
  F_mat F a * F_tilde F b + F_mat F b * F_tilde F a = (Λ / 4 * (if a = b then (1:ℂ) else 0)) • 1 := by
  ext μ ν
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply, F_mat, F_tilde]
  have h := hodge_anticommutator Λ F h_antisymm h_su2 h_plebanski a b μ ν
  rw [← Finset.sum_add_distrib]
  exact h

-- ============================================================================
-- METRIC MATRIX EQUIVALENCE
-- ============================================================================

lemma RHS_term_eq (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ) (μ ν : Fin 4) (a b c : Fin 3) :
  ((F_mat F a * F_tilde F b * F_mat F c) μ ν) =
  - ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    epsilon4 α β γ δ * F_iso F a μ α * F_iso F c ν β * F_iso F b γ δ := by
  have hc0 : F_iso F c 0 ν = - F_iso F c ν 0 := F_iso_antisymm F h_antisymm c 0 ν
  have hc1 : F_iso F c 1 ν = - F_iso F c ν 1 := F_iso_antisymm F h_antisymm c 1 ν
  have hc2 : F_iso F c 2 ν = - F_iso F c ν 2 := F_iso_antisymm F h_antisymm c 2 ν
  have hc3 : F_iso F c 3 ν = - F_iso F c ν 3 := F_iso_antisymm F h_antisymm c 3 ν
  unfold F_mat F_tilde hodgeDual eps_sum
  simp only [Matrix.mul_apply, sum_fin_4_complex]
  rw [hc0, hc1, hc2, hc3]
  simp only [epsilon4, epsilon4_int]
  ring

lemma epsilon3_antisymm_bc (a b c : Fin 3) : epsilon3 a b c = - epsilon3 a c b := by
  have h : epsilon3_int a b c = - epsilon3_int a c b := by revert a b c; decide
  unfold epsilon3
  exact_mod_cast h

lemma sum_epsilon3_antisymm (L : Fin 3 → Fin 3 → Fin 3 → ℂ) :
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * L a b c) =
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (- L a c b)) := by
  calc
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * L a b c)
    _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a c b * L a c b := by
      apply Finset.sum_congr rfl; intro a _
      -- Provide explicit typing so AddCommMonoid perfectly resolves to Complex
      exact Finset.sum_comm (f := fun b c => (epsilon3 a b c * L a b c : ℂ))
    _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (-epsilon3 a b c) * L a c b := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro c _
      rw [epsilon3_antisymm_bc a c b]
    _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (- L a c b) := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro c _
      ring

/-- 
Proves that the massive component-wise definition of the Urbantke Metric 
is equivalent to the algebraically closed matrix product: G = ∑ ε_{abc} F_a F̃_b F_c
-/
lemma M_matrix_eq (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ) (μ ν : Fin 4) :
  (cgdUnimodularMetricAdapter F) μ ν = 
    ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      epsilon3 a b c * ((F_mat F a * F_tilde F b * F_mat F c) μ ν) := by
  rw [g_covariant_eval F μ ν]
  have h_sum := sum_epsilon3_antisymm (fun a b c => ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, epsilon4 α β γ δ * F_iso F a μ α * F_iso F b ν β * F_iso F c γ δ)
  rw [h_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  rw [RHS_term_eq F h_antisymm μ ν a b c]

-- ============================================================================
-- ABSTRACT MATRIX METRIC
-- ============================================================================

/-- 
The Urbantke metric defined purely as an abstract matrix sum.
This removes all spacetime indices (μ, ν) from the computational AST.
-/
noncomputable def G_mat (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c • (F_mat F a * F_tilde F b * F_mat F c)

/-- 
Proves equivalence between the component-wise Spacetime Metric and the abstract Matrix Metric.
-/
lemma G_eq_G_mat (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ) : 
  cgdUnimodularMetricAdapter F = G_mat F := by
  ext μ ν
  rw [M_matrix_eq F h_antisymm μ ν]
  unfold G_mat
  
  -- Push μ and ν through the sum over a
  rw [Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl; intro a _
  
  -- Push μ and ν through the sum over b
  rw [Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl; intro b _
  
  -- Push μ and ν through the sum over c
  rw [Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl; intro c _
  
  -- The scalar multiplication of a matrix `c • M` evaluated at `μ, ν` is exactly `c * M μ ν`
  change epsilon3 a b c * ((F_mat F a * F_tilde F b * F_mat F c) μ ν) = 
         epsilon3 a b c * ((F_mat F a * F_tilde F b * F_mat F c) μ ν)
  rfl

-- ============================================================================
-- LEVERRIER MATRIX EXPANSION
-- ============================================================================

/-- 
Leverrier's Algorithm applied to the Urbantke Metric.
By converting the determinant into traces of matrix powers, we completely bypass 
the O(N!) Levi-Civita permutation expansion and the 31,000-term scalar AST.
-/
lemma urbantke_leverrier (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ) :
  (cgdUnimodularMetricAdapter F).det = 
    (1 / 24 : ℂ) * (
      (Matrix.trace (G_mat F))^4
      - 6 * Matrix.trace ((G_mat F)^2) * (Matrix.trace (G_mat F))^2
      + 3 * (Matrix.trace ((G_mat F)^2))^2
      + 8 * Matrix.trace ((G_mat F)^3) * Matrix.trace (G_mat F)
      - 6 * Matrix.trace ((G_mat F)^4)
    ) := by
  rw [G_eq_G_mat F h_antisymm]
  -- `ℂ` is a Field with CharZero, satisfying the typeclasses for Leverrier's identity
  exact Litlib.Math.Leverrier.newtons_identities_det (G_mat F)

-- ============================================================================
-- THE CLIFFORD ALGEBRA OF THE ASHTEKAR PHASE SPACE
-- ============================================================================

lemma F_tilde_eq_self_dual (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_self_dual : ∀ a, hodgeDual F a = 2 • (fun μ ν => F_iso F a μ ν)) (a : Fin 3) :
  F_tilde F a = (2 : ℂ) • F_mat F a := by
  ext μ ν
  have h := congr_fun (congr_fun (h_self_dual a) μ) ν
  unfold F_tilde F_mat
  
  -- The LHS evaluates to hodgeDual F a μ ν.
  -- The RHS evaluates to `(2 • f) μ ν` which is definitionally `2 • f μ ν` using `nsmul`.
  have h2 : (2 • fun m n => F_iso F a m n) μ ν = (2 : ℂ) * F_iso F a μ ν := by
    change (2 : ℕ) • F_iso F a μ ν = (2 : ℂ) * F_iso F a μ ν
    exact nsmul_eq_mul 2 (F_iso F a μ ν)
    
  rw [h2] at h
  change hodgeDual F a μ ν = (2 : ℂ) * F_iso F a μ ν
  exact h

/--
The Self-Dual F matrices literally form a Clifford Algebra perfectly proportional 
to the Unimodular Plebanski constant Λ.
-/
lemma clifford_anticommutator (Λ : ℂ) (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ)
  (h_su2 : ∀ μ ν, F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧ 
    F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1)
  (h_plebanski : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
      epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1)
  (h_self_dual : ∀ a, hodgeDual F a = 2 • (fun μ ν => F_iso F a μ ν))
  (a b : Fin 3) :
  F_mat F a * F_mat F b + F_mat F b * F_mat F a = (Λ / 8 * (if a = b then (1:ℂ) else 0)) • 1 := by
  have h_hodge := F_mat_anticomm Λ F h_antisymm h_su2 h_plebanski a b
  have ha := F_tilde_eq_self_dual F h_self_dual a
  have hb := F_tilde_eq_self_dual F h_self_dual b
  rw [ha, hb] at h_hodge
  
  -- Extract the Complex scalars safely
  have h_expand : F_mat F a * ((2 : ℂ) • F_mat F b) + F_mat F b * ((2 : ℂ) • F_mat F a) = 
    (2 : ℂ) • (F_mat F a * F_mat F b + F_mat F b * F_mat F a) := by
    rw [Matrix.mul_smul, Matrix.mul_smul]
    rw [← smul_add]
    
  rw [h_expand] at h_hodge
  
  -- Evaluate component-wise to avoid all `Module` scalar tower complaints
  ext μ ν
  have h_eval := congr_fun (congr_fun h_hodge μ) ν
  
  -- Unroll all matrix scalar multiplication into standard Complex field arithmetic
  simp only [Matrix.smul_apply, smul_eq_mul] at h_eval ⊢
  
  calc
    ((F_mat F a * F_mat F b + F_mat F b * F_mat F a) μ ν)
    _ = (1 / 2 : ℂ) * ((2 : ℂ) * ((F_mat F a * F_mat F b + F_mat F b * F_mat F a) μ ν)) := by ring
    _ = (1 / 2 : ℂ) * ((Λ / 4 * (if a = b then (1:ℂ) else 0)) * (1 : Matrix (Fin 4) (Fin 4) ℂ) μ ν) := by rw [h_eval]
    _ = (Λ / 8 * (if a = b then (1:ℂ) else 0)) * (1 : Matrix (Fin 4) (Fin 4) ℂ) μ ν := by ring

lemma sum_epsilon4_eq_sum_cgd_epsilon4 (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, (Litlib.Math.LeviCivita.epsilon4 μ ν ρ σ : ℂ) * f μ ν ρ σ) =
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * f μ ν ρ σ) := by
  rw [Litlib.Math.EpsilonDeterminant.expand_epsilon_complex f]
  rw [CGD.Gravity.expand_cgd_epsilon f]

lemma det_antisymm_4x4 (A : Matrix (Fin 4) (Fin 4) ℂ) (h_antisymm : ∀ μ ν, A μ ν = - A ν μ) :
  A.det = (1 / 64) * (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
    (Litlib.Math.LeviCivita.epsilon4 μ ν ρ σ : ℂ) * (A μ ν * A ρ σ))^2 := by
  have A00 : A 0 0 = 0 := CGD.Gravity.antisymm_zero A h_antisymm 0
  have A11 : A 1 1 = 0 := CGD.Gravity.antisymm_zero A h_antisymm 1
  have A22 : A 2 2 = 0 := CGD.Gravity.antisymm_zero A h_antisymm 2
  have A33 : A 3 3 = 0 := CGD.Gravity.antisymm_zero A h_antisymm 3
  have A10 : A 1 0 = -A 0 1 := h_antisymm 1 0
  have A20 : A 2 0 = -A 0 2 := h_antisymm 2 0
  have A30 : A 3 0 = -A 0 3 := h_antisymm 3 0
  have A21 : A 2 1 = -A 1 2 := h_antisymm 2 1
  have A31 : A 3 1 = -A 1 3 := h_antisymm 3 1
  have A32 : A 3 2 = -A 2 3 := h_antisymm 3 2

  have h_rhs : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, (Litlib.Math.LeviCivita.epsilon4 μ ν ρ σ : ℂ) * (A μ ν * A ρ σ)) =
    A 0 1 * A 2 3 - A 0 1 * A 3 2 - A 0 2 * A 1 3 + A 0 2 * A 3 1 + A 0 3 * A 1 2 - A 0 3 * A 2 1
    - A 1 0 * A 2 3 + A 1 0 * A 3 2 + A 1 2 * A 0 3 - A 1 2 * A 3 0 - A 1 3 * A 0 2 + A 1 3 * A 2 0
    + A 2 0 * A 1 3 - A 2 0 * A 3 1 - A 2 1 * A 0 3 + A 2 1 * A 3 0 + A 2 3 * A 0 1 - A 2 3 * A 1 0
    - A 3 0 * A 1 2 + A 3 0 * A 2 1 + A 3 1 * A 0 2 - A 3 1 * A 2 0 - A 3 2 * A 0 1 + A 3 2 * A 1 0 := by
    exact Litlib.Math.EpsilonDeterminant.expand_epsilon_complex (fun μ ν ρ σ => A μ ν * A ρ σ)

  calc A.det = A 0 0 * (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1) + A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1))
      - A 0 1 * (A 1 0 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 0 * A 3 3 - A 2 3 * A 3 0) + A 1 3 * (A 2 0 * A 3 2 - A 2 2 * A 3 0))
      + A 0 2 * (A 1 0 * (A 2 1 * A 3 3 - A 2 3 * A 3 1) - A 1 1 * (A 2 0 * A 3 3 - A 2 3 * A 3 0) + A 1 3 * (A 2 0 * A 3 1 - A 2 1 * A 3 0))
      - A 0 3 * (A 1 0 * (A 2 1 * A 3 2 - A 2 2 * A 3 1) - A 1 1 * (A 2 0 * A 3 2 - A 2 2 * A 3 0) + A 1 2 * (A 2 0 * A 3 1 - A 2 1 * A 3 0)) := Litlib.Math.Matrix4.expand_det_4 A
    _ = (1 / 64) * (A 0 1 * A 2 3 - A 0 1 * A 3 2 - A 0 2 * A 1 3 + A 0 2 * A 3 1 + A 0 3 * A 1 2 - A 0 3 * A 2 1
      - A 1 0 * A 2 3 + A 1 0 * A 3 2 + A 1 2 * A 0 3 - A 1 2 * A 3 0 - A 1 3 * A 0 2 + A 1 3 * A 2 0
      + A 2 0 * A 1 3 - A 2 0 * A 3 1 - A 2 1 * A 0 3 + A 2 1 * A 3 0 + A 2 3 * A 0 1 - A 2 3 * A 1 0
      - A 3 0 * A 1 2 + A 3 0 * A 2 1 + A 3 1 * A 0 2 - A 3 1 * A 2 0 - A 3 2 * A 0 1 + A 3 2 * A 1 0)^2 := by
      simp only [A00, A11, A22, A33, A10, A20, A30, A21, A31, A32]
      ring
    _ = (1 / 64) * (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, (Litlib.Math.LeviCivita.epsilon4 μ ν ρ σ : ℂ) * (A μ ν * A ρ σ))^2 := by rw [h_rhs]

lemma det_F_mat (Λ : ℂ) (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ)
  (h_su2 : ∀ μ ν, F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧ 
    F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1)
  (h_plebanski : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
      epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1)
  (a : Fin 3) :
  (F_mat F a).det = Λ^2 / 256 := by
  have h := det_antisymm_4x4 (F_mat F a) (F_mat_antisymm F h_antisymm a)
  have h_wedge := wedge_iso_eval Λ F h_antisymm h_su2 h_plebanski a a
  have h_eq : (if a = a then (1:ℂ) else 0) = 1 := if_pos rfl
  rw [h_eq] at h_wedge
  
  have h_wedge3 : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, (Litlib.Math.LeviCivita.epsilon4 μ ν ρ σ : ℂ) * ((F_mat F a) μ ν * (F_mat F a) ρ σ)) = -Λ / 2 := by
    calc (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, (Litlib.Math.LeviCivita.epsilon4 μ ν ρ σ : ℂ) * ((F_mat F a) μ ν * (F_mat F a) ρ σ))
      _ = ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * ((F_mat F a) μ ν * (F_mat F a) ρ σ) := sum_epsilon4_eq_sum_cgd_epsilon4 (fun μ ν ρ σ => (F_mat F a) μ ν * (F_mat F a) ρ σ)
      _ = ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * F_iso F a μ ν * F_iso F a ρ σ := by
        apply Finset.sum_congr rfl; intro μ _
        apply Finset.sum_congr rfl; intro ν _
        apply Finset.sum_congr rfl; intro ρ _
        apply Finset.sum_congr rfl; intro σ _
        unfold F_mat
        ring
      _ = (-Λ / 2) * 1 := h_wedge
      _ = -Λ / 2 := by ring
  
  rw [h_wedge3] at h
  calc (F_mat F a).det = (1 / 64) * (-Λ / 2)^2 := h
  _ = Λ^2 / 256 := by ring

lemma F_mat_anticomm_neq (Λ : ℂ) (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ)
  (h_su2 : ∀ μ ν, F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧ 
    F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1)
  (h_plebanski : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
      epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1)
  (h_self_dual : ∀ a, hodgeDual F a = 2 • (fun μ ν => F_iso F a μ ν))
  (a b : Fin 3) (h_neq : a ≠ b) :
  F_mat F a * F_mat F b = - (F_mat F b * F_mat F a) := by
  have h := clifford_anticommutator Λ F h_antisymm h_su2 h_plebanski h_self_dual a b
  have h_eq : (if a = b then (1:ℂ) else 0) = 0 := if_neg h_neq
  rw [h_eq] at h
  have h_zero : (Λ / 8 * 0) • (1 : Matrix (Fin 4) (Fin 4) ℂ) = 0 := by simp
  rw [h_zero] at h
  exact eq_neg_of_add_eq_zero_left h

noncomputable def G_term (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (a b c : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((2:ℂ) * (Litlib.Math.LeviCivita.epsilon3 a b c : ℂ)) • (F_mat F a * F_mat F b * F_mat F c)

lemma sum_fin_3_matrix (f : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ) :
  (∑ i : Fin 3, f i) = f 0 + f 1 + f 2 := by
  ext μ ν
  have h_sum : (∑ i : Fin 3, f i) μ ν = f 0 μ ν + f (Fin.succ 0) μ ν + f (Fin.succ (Fin.succ 0)) μ ν := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply, Matrix.zero_apply, add_zero, add_assoc]
  rw [h_sum]
  have h_succ1 : f (Fin.succ 0) = f 1 := rfl
  have h_succ2 : f (Fin.succ (Fin.succ 0)) = f 2 := rfl
  rw [h_succ1, h_succ2]
  have h2 : (f 0 + f 1 + f 2) μ ν = f 0 μ ν + f 1 μ ν + f 2 μ ν := by
    simp only [Matrix.add_apply, add_assoc]
  rw [h2]

lemma G_term_zero (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (a b c : Fin 3)
  (h_eps : (Litlib.Math.LeviCivita.epsilon3 a b c : ℂ) = 0) :
  G_term F a b c = 0 := by
  unfold G_term
  rw [h_eps]
  have h_mul : (2:ℂ) * 0 = 0 := mul_zero 2
  rw [h_mul]
  exact zero_smul ℂ _

lemma G_term_pos (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (a b c : Fin 3)
  (h_eps : (Litlib.Math.LeviCivita.epsilon3 a b c : ℂ) = 1) :
  G_term F a b c = (2:ℂ) • (F_mat F a * F_mat F b * F_mat F c) := by
  unfold G_term
  rw [h_eps]
  have h_mul : (2:ℂ) * 1 = 2 := mul_one 2
  rw [h_mul]

lemma G_term_neg (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (a b c : Fin 3)
  (h_eps : (Litlib.Math.LeviCivita.epsilon3 a b c : ℂ) = -1) :
  G_term F a b c = - ((2:ℂ) • (F_mat F a * F_mat F b * F_mat F c)) := by
  unfold G_term
  rw [h_eps]
  have h_mul : (2:ℂ) * -1 = -2 := mul_neg_one 2
  rw [h_mul]
  exact neg_smul (2:ℂ) (F_mat F a * F_mat F b * F_mat F c)

/-- The metric rigorously evaluates to 12 F_0 F_1 F_2 -/
lemma G_mat_eq_volume (Λ : ℂ) (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ)
  (h_su2 : ∀ μ ν, F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧ 
    F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1)
  (h_plebanski : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
      epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1)
  (h_self_dual : ∀ a, hodgeDual F a = 2 • (fun μ ν => F_iso F a μ ν)) :
  G_mat F = 12 • (F_mat F 0 * F_mat F 1 * F_mat F 2) := by
  
  have hac01 : ∀ μ ν, (F_mat F 0 * F_mat F 1) μ ν = - (F_mat F 1 * F_mat F 0) μ ν := by
    intro μ ν; exact congr_fun (congr_fun (F_mat_anticomm_neq Λ F h_antisymm h_su2 h_plebanski h_self_dual 0 1 (by decide)) μ) ν
  have hac10 : ∀ μ ν, (F_mat F 1 * F_mat F 0) μ ν = - (F_mat F 0 * F_mat F 1) μ ν := by
    intro μ ν; exact congr_fun (congr_fun (F_mat_anticomm_neq Λ F h_antisymm h_su2 h_plebanski h_self_dual 1 0 (by decide)) μ) ν
  have hac02 : ∀ μ ν, (F_mat F 0 * F_mat F 2) μ ν = - (F_mat F 2 * F_mat F 0) μ ν := by
    intro μ ν; exact congr_fun (congr_fun (F_mat_anticomm_neq Λ F h_antisymm h_su2 h_plebanski h_self_dual 0 2 (by decide)) μ) ν
  have hac20 : ∀ μ ν, (F_mat F 2 * F_mat F 0) μ ν = - (F_mat F 0 * F_mat F 2) μ ν := by
    intro μ ν; exact congr_fun (congr_fun (F_mat_anticomm_neq Λ F h_antisymm h_su2 h_plebanski h_self_dual 2 0 (by decide)) μ) ν
  have hac12 : ∀ μ ν, (F_mat F 1 * F_mat F 2) μ ν = - (F_mat F 2 * F_mat F 1) μ ν := by
    intro μ ν; exact congr_fun (congr_fun (F_mat_anticomm_neq Λ F h_antisymm h_su2 h_plebanski h_self_dual 1 2 (by decide)) μ) ν
  have hac21 : ∀ μ ν, (F_mat F 2 * F_mat F 1) μ ν = - (F_mat F 1 * F_mat F 2) μ ν := by
    intro μ ν; exact congr_fun (congr_fun (F_mat_anticomm_neq Λ F h_antisymm h_su2 h_plebanski h_self_dual 2 1 (by decide)) μ) ν

  unfold G_mat
  
  have h_eps_eq : ∀ a b c, CGD.Gravity.epsilon3 a b c = (Litlib.Math.LeviCivita.epsilon3 a b c : ℂ) := by
    intro a b c
    unfold CGD.Gravity.epsilon3
    have h : CGD.Gravity.epsilon3_int a b c = Litlib.Math.LeviCivita.epsilon3 a b c := by revert a b c; decide
    rw [h]

  have h_sum_eq : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, CGD.Gravity.epsilon3 a b c • (F_mat F a * F_tilde F b * F_mat F c)) =
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, G_term F a b c) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    unfold G_term
    have hf := F_tilde_eq_self_dual F h_self_dual b
    rw [hf, h_eps_eq a b c]
    have h_smul_assoc : F_mat F a * ((2:ℂ) • F_mat F b) * F_mat F c = (2:ℂ) • (F_mat F a * F_mat F b * F_mat F c) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [h_smul_assoc, smul_smul]
    have h_comm : (Litlib.Math.LeviCivita.epsilon3 a b c : ℂ) * (2:ℂ) = (2:ℂ) * (Litlib.Math.LeviCivita.epsilon3 a b c : ℂ) := mul_comm _ _
    rw [h_comm]
  
  rw [h_sum_eq]

  have e000 : (Litlib.Math.LeviCivita.epsilon3 0 0 0 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 0 0 0 = 0)
  have e001 : (Litlib.Math.LeviCivita.epsilon3 0 0 1 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 0 0 1 = 0)
  have e002 : (Litlib.Math.LeviCivita.epsilon3 0 0 2 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 0 0 2 = 0)
  have e010 : (Litlib.Math.LeviCivita.epsilon3 0 1 0 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 0 1 0 = 0)
  have e011 : (Litlib.Math.LeviCivita.epsilon3 0 1 1 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 0 1 1 = 0)
  have e012 : (Litlib.Math.LeviCivita.epsilon3 0 1 2 : ℂ) = 1 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 0 1 2 = 1)
  have e020 : (Litlib.Math.LeviCivita.epsilon3 0 2 0 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 0 2 0 = 0)
  have e021 : (Litlib.Math.LeviCivita.epsilon3 0 2 1 : ℂ) = -1 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 0 2 1 = -1)
  have e022 : (Litlib.Math.LeviCivita.epsilon3 0 2 2 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 0 2 2 = 0)
  
  have e100 : (Litlib.Math.LeviCivita.epsilon3 1 0 0 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 1 0 0 = 0)
  have e101 : (Litlib.Math.LeviCivita.epsilon3 1 0 1 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 1 0 1 = 0)
  have e102 : (Litlib.Math.LeviCivita.epsilon3 1 0 2 : ℂ) = -1 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 1 0 2 = -1)
  have e110 : (Litlib.Math.LeviCivita.epsilon3 1 1 0 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 1 1 0 = 0)
  have e111 : (Litlib.Math.LeviCivita.epsilon3 1 1 1 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 1 1 1 = 0)
  have e112 : (Litlib.Math.LeviCivita.epsilon3 1 1 2 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 1 1 2 = 0)
  have e120 : (Litlib.Math.LeviCivita.epsilon3 1 2 0 : ℂ) = 1 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 1 2 0 = 1)
  have e121 : (Litlib.Math.LeviCivita.epsilon3 1 2 1 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 1 2 1 = 0)
  have e122 : (Litlib.Math.LeviCivita.epsilon3 1 2 2 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 1 2 2 = 0)
  
  have e200 : (Litlib.Math.LeviCivita.epsilon3 2 0 0 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 2 0 0 = 0)
  have e201 : (Litlib.Math.LeviCivita.epsilon3 2 0 1 : ℂ) = 1 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 2 0 1 = 1)
  have e202 : (Litlib.Math.LeviCivita.epsilon3 2 0 2 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 2 0 2 = 0)
  have e210 : (Litlib.Math.LeviCivita.epsilon3 2 1 0 : ℂ) = -1 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 2 1 0 = -1)
  have e211 : (Litlib.Math.LeviCivita.epsilon3 2 1 1 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 2 1 1 = 0)
  have e212 : (Litlib.Math.LeviCivita.epsilon3 2 1 2 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 2 1 2 = 0)
  have e220 : (Litlib.Math.LeviCivita.epsilon3 2 2 0 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 2 2 0 = 0)
  have e221 : (Litlib.Math.LeviCivita.epsilon3 2 2 1 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 2 2 1 = 0)
  have e222 : (Litlib.Math.LeviCivita.epsilon3 2 2 2 : ℂ) = 0 := by exact_mod_cast (by decide : Litlib.Math.LeviCivita.epsilon3 2 2 2 = 0)

  have g000 := G_term_zero F 0 0 0 e000
  have g001 := G_term_zero F 0 0 1 e001
  have g002 := G_term_zero F 0 0 2 e002
  have g010 := G_term_zero F 0 1 0 e010
  have g011 := G_term_zero F 0 1 1 e011
  have g012 := G_term_pos F 0 1 2 e012
  have g020 := G_term_zero F 0 2 0 e020
  have g021 := G_term_neg F 0 2 1 e021
  have g022 := G_term_zero F 0 2 2 e022

  have g100 := G_term_zero F 1 0 0 e100
  have g101 := G_term_zero F 1 0 1 e101
  have g102 := G_term_neg F 1 0 2 e102
  have g110 := G_term_zero F 1 1 0 e110
  have g111 := G_term_zero F 1 1 1 e111
  have g112 := G_term_zero F 1 1 2 e112
  have g120 := G_term_pos F 1 2 0 e120
  have g121 := G_term_zero F 1 2 1 e121
  have g122 := G_term_zero F 1 2 2 e122

  have g200 := G_term_zero F 2 0 0 e200
  have g201 := G_term_pos F 2 0 1 e201
  have g202 := G_term_zero F 2 0 2 e202
  have g210 := G_term_neg F 2 1 0 e210
  have g211 := G_term_zero F 2 1 1 e211
  have g212 := G_term_zero F 2 1 2 e212
  have g220 := G_term_zero F 2 2 0 e220
  have g221 := G_term_zero F 2 2 1 e221
  have g222 := G_term_zero F 2 2 2 e222

  have h_all_eps : 
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, G_term F a b c) =
    2 • (F_mat F 0 * F_mat F 1 * F_mat F 2) - 2 • (F_mat F 0 * F_mat F 2 * F_mat F 1)
    - 2 • (F_mat F 1 * F_mat F 0 * F_mat F 2) + 2 • (F_mat F 1 * F_mat F 2 * F_mat F 0)
    + 2 • (F_mat F 2 * F_mat F 0 * F_mat F 1) - 2 • (F_mat F 2 * F_mat F 1 * F_mat F 0) := by
    rw [sum_fin_3_matrix (fun a => ∑ b : Fin 3, ∑ c : Fin 3, G_term F a b c)]
    rw [sum_fin_3_matrix (fun b => ∑ c : Fin 3, G_term F 0 b c)]
    rw [sum_fin_3_matrix (fun b => ∑ c : Fin 3, G_term F 1 b c)]
    rw [sum_fin_3_matrix (fun b => ∑ c : Fin 3, G_term F 2 b c)]
    rw [sum_fin_3_matrix (fun c => G_term F 0 0 c)]
    rw [sum_fin_3_matrix (fun c => G_term F 0 1 c)]
    rw [sum_fin_3_matrix (fun c => G_term F 0 2 c)]
    rw [sum_fin_3_matrix (fun c => G_term F 1 0 c)]
    rw [sum_fin_3_matrix (fun c => G_term F 1 1 c)]
    rw [sum_fin_3_matrix (fun c => G_term F 1 2 c)]
    rw [sum_fin_3_matrix (fun c => G_term F 2 0 c)]
    rw [sum_fin_3_matrix (fun c => G_term F 2 1 c)]
    rw [sum_fin_3_matrix (fun c => G_term F 2 2 c)]
    rw [g000, g001, g002, g010, g011, g012, g020, g021, g022]
    rw [g100, g101, g102, g110, g111, g112, g120, g121, g122]
    rw [g200, g201, g202, g210, g211, g212, g220, g221, g222]
    ext μ ν
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    ring

  rw [h_all_eps]

  ext μ ν

  have H021 : (F_mat F 0 * F_mat F 2 * F_mat F 1) μ ν = - (F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν := by
    have hc : F_mat F 0 * F_mat F 2 * F_mat F 1 = F_mat F 0 * (F_mat F 2 * F_mat F 1) := Matrix.mul_assoc _ _ _
    have hc2 : F_mat F 0 * F_mat F 1 * F_mat F 2 = F_mat F 0 * (F_mat F 1 * F_mat F 2) := Matrix.mul_assoc _ _ _
    rw [hc, hc2]
    calc (F_mat F 0 * (F_mat F 2 * F_mat F 1)) μ ν
      _ = ∑ x : Fin 4, F_mat F 0 μ x * (F_mat F 2 * F_mat F 1) x ν := by simp only [Matrix.mul_apply]
      _ = ∑ x : Fin 4, F_mat F 0 μ x * - (F_mat F 1 * F_mat F 2) x ν := by simp_rw [hac21]
      _ = - ∑ x : Fin 4, F_mat F 0 μ x * (F_mat F 1 * F_mat F 2) x ν := by simp only [mul_neg, Finset.sum_neg_distrib]
      _ = - (F_mat F 0 * (F_mat F 1 * F_mat F 2)) μ ν := by simp only [Matrix.mul_apply]

  have H102 : (F_mat F 1 * F_mat F 0 * F_mat F 2) μ ν = - (F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν := by
    calc (F_mat F 1 * F_mat F 0 * F_mat F 2) μ ν
      _ = ∑ y : Fin 4, (F_mat F 1 * F_mat F 0) μ y * F_mat F 2 y ν := by simp only [Matrix.mul_apply]
      _ = ∑ y : Fin 4, - (F_mat F 0 * F_mat F 1) μ y * F_mat F 2 y ν := by simp_rw [hac10]
      _ = - ∑ y : Fin 4, (F_mat F 0 * F_mat F 1) μ y * F_mat F 2 y ν := by simp only [neg_mul, Finset.sum_neg_distrib]
      _ = - (F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν := by simp only [Matrix.mul_apply]

  have H120 : (F_mat F 1 * F_mat F 2 * F_mat F 0) μ ν = (F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν := by
    have hc : F_mat F 1 * F_mat F 2 * F_mat F 0 = F_mat F 1 * (F_mat F 2 * F_mat F 0) := Matrix.mul_assoc _ _ _
    rw [hc]
    calc (F_mat F 1 * (F_mat F 2 * F_mat F 0)) μ ν
      _ = ∑ x : Fin 4, F_mat F 1 μ x * (F_mat F 2 * F_mat F 0) x ν := by simp only [Matrix.mul_apply]
      _ = ∑ x : Fin 4, F_mat F 1 μ x * - (F_mat F 0 * F_mat F 2) x ν := by simp_rw [hac20]
      _ = - ∑ x : Fin 4, F_mat F 1 μ x * (F_mat F 0 * F_mat F 2) x ν := by simp only [mul_neg, Finset.sum_neg_distrib]
      _ = - (F_mat F 1 * (F_mat F 0 * F_mat F 2)) μ ν := by simp only [Matrix.mul_apply]
      _ = - (F_mat F 1 * F_mat F 0 * F_mat F 2) μ ν := by rw [Matrix.mul_assoc]
      _ = - (- (F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν) := by rw [H102]
      _ = (F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν := by ring

  have H201 : (F_mat F 2 * F_mat F 0 * F_mat F 1) μ ν = (F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν := by
    calc (F_mat F 2 * F_mat F 0 * F_mat F 1) μ ν
      _ = ∑ y : Fin 4, (F_mat F 2 * F_mat F 0) μ y * F_mat F 1 y ν := by simp only [Matrix.mul_apply]
      _ = ∑ y : Fin 4, - (F_mat F 0 * F_mat F 2) μ y * F_mat F 1 y ν := by simp_rw [hac20]
      _ = - ∑ y : Fin 4, (F_mat F 0 * F_mat F 2) μ y * F_mat F 1 y ν := by simp only [neg_mul, Finset.sum_neg_distrib]
      _ = - (F_mat F 0 * F_mat F 2 * F_mat F 1) μ ν := by simp only [Matrix.mul_apply]
      _ = - (- (F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν) := by rw [H021]
      _ = (F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν := by ring
    
  have H210 : (F_mat F 2 * F_mat F 1 * F_mat F 0) μ ν = - (F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν := by
    have hc : F_mat F 2 * F_mat F 1 * F_mat F 0 = F_mat F 2 * (F_mat F 1 * F_mat F 0) := Matrix.mul_assoc _ _ _
    rw [hc]
    calc (F_mat F 2 * (F_mat F 1 * F_mat F 0)) μ ν
      _ = ∑ x : Fin 4, F_mat F 2 μ x * (F_mat F 1 * F_mat F 0) x ν := by simp only [Matrix.mul_apply]
      _ = ∑ x : Fin 4, F_mat F 2 μ x * - (F_mat F 0 * F_mat F 1) x ν := by simp_rw [hac10]
      _ = - ∑ x : Fin 4, F_mat F 2 μ x * (F_mat F 0 * F_mat F 1) x ν := by simp only [mul_neg, Finset.sum_neg_distrib]
      _ = - (F_mat F 2 * (F_mat F 0 * F_mat F 1)) μ ν := by simp only [Matrix.mul_apply]
      _ = - (F_mat F 2 * F_mat F 0 * F_mat F 1) μ ν := by rw [Matrix.mul_assoc]
      _ = - (F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν := by rw [H201]

  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [H021, H102, H120, H201, H210]
  ring

-- ============================================================================
-- PHASE 4: SU(2) INTERNAL SCHOUTEN FACTORIZATION
-- ============================================================================

/--
The Urbantke determinant can be factored perfectly into polynomials of the Plebanski constraint Λ
by expanding the SU(2) indices and computing the determinant of the Clifford volume element.
-/
lemma urbantke_det_factorization (Λ : ℂ) (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (h_antisymm : ∀ μ ν, F μ ν = -F ν μ)
  (h_su2 : ∀ μ ν, F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧ 
    F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1)
  (h_plebanski : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
      epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1)
  (h_self_dual : ∀ a, hodgeDual F a = 2 • (fun μ ν => F_iso F a μ ν)) :
  (cgdUnimodularMetricAdapter F).det = (81 / 65536 : ℂ) * Λ^6 := by
  
  -- cgdUnimodularMetricAdapter F = G_mat F
  rw [G_eq_G_mat F h_antisymm]
  
  -- G_mat F = 12 * (F0 * F1 * F2)
  have h_G := G_mat_eq_volume Λ F h_antisymm h_su2 h_plebanski h_self_dual
  rw [h_G]
  
  -- Elevate the scalar from ℕ to ℂ so det_smul typechecks
  have h_nsmul : 12 • (F_mat F 0 * F_mat F 1 * F_mat F 2) = (12 : ℂ) • (F_mat F 0 * F_mat F 1 * F_mat F 2) := by
    ext μ ν
    change (12 : ℕ) • ((F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν) = (12 : ℂ) * ((F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν)
    exact nsmul_eq_mul 12 ((F_mat F 0 * F_mat F 1 * F_mat F 2) μ ν)
  rw [h_nsmul]
  
  -- det(12 * M) = 12^4 * det M
  rw [Matrix.det_smul]
  have h_card : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
  rw [h_card]
  
  -- det(A * B * C) = det A * det B * det C
  rw [Matrix.det_mul, Matrix.det_mul]
  
  -- substitute det F_a = Λ^2 / 256
  have hd0 := det_F_mat Λ F h_antisymm h_su2 h_plebanski 0
  have hd1 := det_F_mat Λ F h_antisymm h_su2 h_plebanski 1
  have hd2 := det_F_mat Λ F h_antisymm h_su2 h_plebanski 2
  
  rw [hd0, hd1, hd2]
  
  -- Compute the final scalar
  ring

/--
The fundamental algebraic invariant of the Urbantke metric.
This theorem proves that for any tensor F representing an su(2) 2-form, 
if F satisfies the Unimodular Plebanski constraint (F ∧ F = Λ I) and is chiral (self-dual), 
the determinant of its constructed 4x4 Urbantke metric is uniquely fixed 
to a specific scalar value `det_val`, independent of the individual 
degrees of freedom of F.
-/
theorem urbantke_det_uniqueness (Λ : ℂ) :
  ∃ (det_val : ℂ), 
    ∀ (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ),
      (∀ μ ν, F μ ν = - F ν μ) →
      (∀ μ ν, 
        F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧
        F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1) →
      ((∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
        epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1) →
      (∀ a, hodgeDual F a = 2 • (fun μ ν => F_iso F a μ ν)) →
      (cgdUnimodularMetricAdapter F).det = det_val := by
  use (81 / 65536 : ℂ) * Λ^6
  intro F h_antisymm h_su2 h_plebanski h_self_dual
  exact urbantke_det_factorization Λ F h_antisymm h_su2 h_plebanski h_self_dual

end CGD.Gravity

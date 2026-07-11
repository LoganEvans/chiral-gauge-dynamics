-- FILENAME: CGD/Foundations/Lagrangian/Permutation.lean

import CGD.Foundations.Lagrangian.Epsilon
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Matrix Complex BigOperators CGD.Axioms CGD.Foundations

namespace CGD.Foundations

def permMatrix (p : Equiv.Perm (Fin 4)) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of (fun i j => if i = p j then 1 else 0)

lemma det_permMatrix (p : Equiv.Perm (Fin 4)) :
  Matrix.det (permMatrix p) = (Equiv.Perm.sign p : ℂ) := by
  rw [Matrix.det_apply]
  have h_prod : ∀ (σ : Equiv.Perm (Fin 4)),
    (∏ i : Fin 4, permMatrix p (σ i) i) = if σ = p then (1 : ℂ) else 0 := by
    intro σ
    by_cases h : σ = p
    · rw [h, if_pos rfl]
      have h_ones : (∏ i : Fin 4, permMatrix p (p i) i) = ∏ i : Fin 4, (1 : ℂ) := by
        apply Finset.prod_congr rfl
        intro x _
        unfold permMatrix
        rw [Matrix.of_apply]
        rw [if_pos rfl]
      rw [h_ones, Finset.prod_const_one]
    · rw [if_neg h]
      have h_ex : ∃ i, σ i ≠ p i := by
        by_contra hc
        push_neg at hc
        apply h
        apply Equiv.ext
        intro x
        exact hc x
      rcases h_ex with ⟨i, hi⟩
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      unfold permMatrix
      rw [Matrix.of_apply]
      rw [if_neg hi]

  -- Rewrite the sum body using the exact prod evaluation
  have h_sum_body : (∑ σ : Equiv.Perm (Fin 4), Equiv.Perm.sign σ • ∏ i : Fin 4, permMatrix p (σ i) i) =
    ∑ σ : Equiv.Perm (Fin 4), (Equiv.Perm.sign σ : ℤ) • (if σ = p then (1 : ℂ) else 0) := by
    apply Finset.sum_congr rfl
    intro σ _
    have h_eval := h_prod σ
    rw [h_eval]
    rfl
  rw [h_sum_body]

  -- Isolate the p-th term explicitly
  have h_single : (∑ σ : Equiv.Perm (Fin 4), (Equiv.Perm.sign σ : ℤ) • (if σ = p then (1 : ℂ) else 0)) =
    (Equiv.Perm.sign p : ℤ) • (1 : ℂ) := by
    have h_ext : (∑ σ : Equiv.Perm (Fin 4), (Equiv.Perm.sign σ : ℤ) • (if σ = p then (1 : ℂ) else 0)) =
      ∑ σ : Equiv.Perm (Fin 4), (fun x => (Equiv.Perm.sign x : ℤ) • (if x = p then (1 : ℂ) else 0)) σ := rfl
    rw [h_ext]
    rw [Finset.sum_eq_single p]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg hb]
      exact smul_zero (Equiv.Perm.sign b : ℤ)
    · intro h_not; exfalso; exact h_not (Finset.mem_univ p)
  rw [h_single]

  -- Evaluate the scalar multiplication as a complex cast
  rw [zsmul_eq_mul]
  rw [mul_one]

lemma det_swapMatrix (i j : Fin 4) (h : i ≠ j) :
  Matrix.det (permMatrix (Equiv.swap i j)) = -1 := by
  rw [det_permMatrix]
  have hs := Equiv.Perm.sign_swap h
  rw [hs]
  push_cast
  rfl

lemma ite_perm_symm (p : Equiv.Perm (Fin 4)) (μ α : Fin 4) :
  (if μ = p α then (1 : ℂ) else 0) = if α = p.symm μ then (1 : ℂ) else 0 := by
  by_cases h1 : μ = p α
  · by_cases h2 : α = p.symm μ
    · rw [if_pos h1, if_pos h2]
    · exfalso
      apply h2
      exact (Equiv.eq_symm_apply p).mpr h1.symm
  · by_cases h2 : α = p.symm μ
    · exfalso
      apply h1
      exact ((Equiv.eq_symm_apply p).mp h2).symm
    · rw [if_neg h1, if_neg h2]

lemma permMatrix_apply_factor (p : Equiv.Perm (Fin 4)) (F : Fin 4 → Fin 4 → ChiralM) (μ ν : Fin 4) :
  (∑ α : Fin 4, ∑ β : Fin 4, ((if α = p.symm μ then (1 : ℂ) else 0) * (if β = p.symm ν then (1 : ℂ) else 0)) • F α β) =
  ∑ α : Fin 4, (if α = p.symm μ then (1 : ℂ) else 0) •
    (∑ β : Fin 4, (if β = p.symm ν then (1 : ℂ) else 0) • F α β) := by
  symm
  have h_pull_smul : (∑ α : Fin 4, (if α = p.symm μ then (1 : ℂ) else 0) • ∑ β : Fin 4, (if β = p.symm ν then (1 : ℂ) else 0) • F α β) =
    ∑ α : Fin 4, ∑ β : Fin 4, (if α = p.symm μ then (1 : ℂ) else 0) • (if β = p.symm ν then (1 : ℂ) else 0) • F α β := by
    apply Finset.sum_congr rfl
    intro α _
    exact Finset.smul_sum
  rw [h_pull_smul]
  apply Finset.sum_congr rfl; intro α _
  apply Finset.sum_congr rfl; intro β _
  exact Eq.symm (mul_smul (if α = p.symm μ then (1 : ℂ) else 0) (if β = p.symm ν then (1 : ℂ) else 0) (F α β))

lemma permMatrix_apply (p : Equiv.Perm (Fin 4)) (F : Fin 4 → Fin 4 → ChiralM) :
  (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (permMatrix p μ α * permMatrix p ν β) • F α β) =
  (fun μ ν => F (p.symm μ) (p.symm ν)) := by
  ext μ ν
  unfold permMatrix
  simp_rw [Matrix.of_apply]
  simp_rw [ite_perm_symm p]
  rw [permMatrix_apply_factor]
  rw [sum_ite_smul]
  rw [sum_ite_smul]
  simp

lemma swapMatrix_topological_C (a b : Fin 4) (hab : a ≠ b) :
  ∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
      permMatrix (Equiv.swap a b) α μ * permMatrix (Equiv.swap a b) β ν * permMatrix (Equiv.swap a b) γ ρ * permMatrix (Equiv.swap a b) δ σ * CGD.Gravity.epsilon4 α β γ δ =
      Matrix.det (permMatrix (Equiv.swap a b)) * CGD.Gravity.epsilon4 μ ν ρ σ := by
  intro μ ν ρ σ
  rw [det_swapMatrix a b hab]
  have h_apply : ∀ α μ, permMatrix (Equiv.swap a b) α μ = if α = Equiv.swap a b μ then (1:ℂ) else 0 := by
    intro x y
    unfold permMatrix
    rw [Matrix.of_apply]
  simp_rw [h_apply]
  have h_rearrange := eps_perm_rearrange (Equiv.swap a b) μ ν ρ σ
  rw [h_rearrange]
  have h_sign := epsilon_swap_sign a b μ ν ρ σ
  rw [h_sign]
  have h_swap_sign : (Equiv.Perm.sign (Equiv.swap a b) : ℂ) = -1 := by
    have h_s := Equiv.Perm.sign_swap hab
    rw [h_s]
    push_cast; rfl
  rw [h_swap_sign]

end CGD.Foundations

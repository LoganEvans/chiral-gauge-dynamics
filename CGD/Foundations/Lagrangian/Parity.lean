-- FILENAME: CGD/Foundations/Lagrangian/Parity.lean

import CGD.Foundations.Lagrangian.Epsilon
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Matrix Complex BigOperators CGD.Axioms CGD.Foundations CGD.Math

namespace CGD.Foundations

def d_neg_int (k x : Fin 4) : ℤ := if x = k then -1 else 1

def Lambda_neg_mat_int (k : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of (fun i j => if i = j then d_neg_int k i else 0)

lemma det_Lambda_neg_mat_int (k : Fin 4) : Matrix.det (Lambda_neg_mat_int k) = -1 := by
  revert k; decide

def Lambda_neg_mat (k : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => (Lambda_neg_mat_int k i j : ℂ)

lemma det_Lambda_neg_mat (k : Fin 4) : Matrix.det (Lambda_neg_mat k) = -1 := by
  have h : Lambda_neg_mat k = (Int.castRingHom ℂ).mapMatrix (Lambda_neg_mat_int k) := by ext i j; rfl
  rw [h]
  have hm := RingHom.map_det (Int.castRingHom ℂ) (Lambda_neg_mat_int k)
  rw [←hm]
  have hd := det_Lambda_neg_mat_int k
  rw [hd]
  norm_num

lemma Lambda_neg_mat_apply_left (k α μ : Fin 4) :
  Lambda_neg_mat k α μ = if α = μ then (d_neg_int k α : ℂ) else 0 := by
  unfold Lambda_neg_mat Lambda_neg_mat_int
  simp only [Matrix.of_apply]
  by_cases h : α = μ
  · have ha1 : (if α = μ then d_neg_int k α else 0) = d_neg_int k α := if_pos h
    have ha2 : (if α = μ then (d_neg_int k α : ℂ) else 0) = (d_neg_int k α : ℂ) := if_pos h
    rw [ha1, ha2]
  · have ha1 : (if α = μ then d_neg_int k α else 0) = 0 := if_neg h
    have ha2 : (if α = μ then (d_neg_int k α : ℂ) else 0) = 0 := if_neg h
    rw [ha1, ha2]
    push_cast
    rfl

lemma Lambda_neg_mat_apply_right (k μ α : Fin 4) :
  Lambda_neg_mat k μ α = if α = μ then (d_neg_int k α : ℂ) else 0 := by
  unfold Lambda_neg_mat Lambda_neg_mat_int
  simp only [Matrix.of_apply]
  by_cases h : α = μ
  · have h_symm : μ = α := h.symm
    have ha1 : (if μ = α then d_neg_int k μ else 0) = d_neg_int k μ := if_pos h_symm
    have ha2 : (if α = μ then (d_neg_int k α : ℂ) else 0) = (d_neg_int k α : ℂ) := if_pos h
    rw [ha1, ha2]
    rw [h_symm]
  · have h_symm : μ ≠ α := fun hc => h hc.symm
    have ha1 : (if μ = α then d_neg_int k μ else 0) = 0 := if_neg h_symm
    have ha2 : (if α = μ then (d_neg_int k α : ℂ) else 0) = 0 := if_neg h
    rw [ha1, ha2]
    push_cast
    rfl

lemma d_neg_int_eps (k μ ν ρ σ : Fin 4) :
  d_neg_int k μ * d_neg_int k ν * d_neg_int k ρ * d_neg_int k σ * CGD.Gravity.epsilon4_int μ ν ρ σ =
  - CGD.Gravity.epsilon4_int μ ν ρ σ := by
  revert k μ ν ρ σ; decide

lemma Lambda_neg_topological (k : Fin 4) :
  ∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
      Lambda_neg_mat k α μ * Lambda_neg_mat k β ν * Lambda_neg_mat k γ ρ * Lambda_neg_mat k δ σ * CGD.Gravity.epsilon4 α β γ δ =
      Matrix.det (Lambda_neg_mat k) * CGD.Gravity.epsilon4 μ ν ρ σ := by
  intro μ ν ρ σ
  rw [det_Lambda_neg_mat]
  have h_apply : ∀ α μ, Lambda_neg_mat k α μ = if α = μ then (d_neg_int k α : ℂ) else 0 := by
    intro a m
    exact Lambda_neg_mat_apply_left k a m
  simp_rw [h_apply]
  have h_rearrange := eps_diag_rearrange (fun x => (d_neg_int k x : ℂ)) μ ν ρ σ
  rw [h_rearrange]
  have h_int := d_neg_int_eps k μ ν ρ σ
  have h_cast : (((d_neg_int k μ * d_neg_int k ν * d_neg_int k ρ * d_neg_int k σ * CGD.Gravity.epsilon4_int μ ν ρ σ) : ℤ) : ℂ) =
                (((- CGD.Gravity.epsilon4_int μ ν ρ σ) : ℤ) : ℂ) := by rw [h_int]
  push_cast at h_cast
  unfold CGD.Gravity.epsilon4
  rw [h_cast]
  ring

lemma smul_pull_F (k μ ν α β : Fin 4) (F : Fin 4 → Fin 4 → ChiralM) :
  (((if α = μ then (d_neg_int k α : ℂ) else 0) * (if β = ν then (d_neg_int k β : ℂ) else 0)) • F α β) =
  (if α = μ then (d_neg_int k α : ℂ) else 0) • ((if β = ν then (d_neg_int k β : ℂ) else 0) • F α β) := by
  exact mul_smul (if α = μ then (d_neg_int k α : ℂ) else 0) (if β = ν then (d_neg_int k β : ℂ) else 0) (F α β)

lemma sum_ite_smul_F_inner (k ν : Fin 4) (F : Fin 4 → Fin 4 → ChiralM) (α : Fin 4) :
  (∑ β : Fin 4, (if β = ν then (d_neg_int k β : ℂ) else 0) • F α β) = (d_neg_int k ν : ℂ) • F α ν := by
  exact sum_ite_smul ν (fun x => (d_neg_int k x : ℂ)) (fun x => F α x)

lemma sum_ite_smul_F_outer (k μ ν : Fin 4) (F : Fin 4 → Fin 4 → ChiralM) :
  (∑ α : Fin 4, (if α = μ then (d_neg_int k α : ℂ) else 0) • ((d_neg_int k ν : ℂ) • F α ν)) =
  (d_neg_int k μ : ℂ) • ((d_neg_int k ν : ℂ) • F μ ν) := by
  exact sum_ite_smul μ (fun x => (d_neg_int k x : ℂ)) (fun x => (d_neg_int k ν : ℂ) • F x ν)

lemma Lambda_neg_F (k : Fin 4) (F : Fin 4 → Fin 4 → ChiralM) (h_missing : ∀ μ ν, μ = k ∨ ν = k → F μ ν = 0) :
  (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Lambda_neg_mat k μ α * Lambda_neg_mat k ν β) • F α β) = F := by
  ext μ ν
  have h_sum_outer : (∑ α : Fin 4, ∑ β : Fin 4, (Lambda_neg_mat k μ α * Lambda_neg_mat k ν β) • F α β) =
                     (∑ α : Fin 4, ∑ β : Fin 4, ((if α = μ then (d_neg_int k α : ℂ) else 0) * (if β = ν then (d_neg_int k β : ℂ) else 0)) • F α β) := by
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro β _
    have h_a1 := Lambda_neg_mat_apply_right k μ α
    have h_a2 := Lambda_neg_mat_apply_right k ν β
    rw [h_a1, h_a2]

  rw [h_sum_outer]
  have h_sum_split : (∑ α : Fin 4, ∑ β : Fin 4, ((if α = μ then (d_neg_int k α : ℂ) else 0) * (if β = ν then (d_neg_int k β : ℂ) else 0)) • F α β) =
                     (∑ α : Fin 4, ∑ β : Fin 4, (if α = μ then (d_neg_int k α : ℂ) else 0) • ((if β = ν then (d_neg_int k β : ℂ) else 0) • F α β)) := by
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro β _
    exact smul_pull_F k μ ν α β F

  rw [h_sum_split]

  have h_sum_pull : (∑ α : Fin 4, ∑ β : Fin 4, (if α = μ then (d_neg_int k α : ℂ) else 0) • ((if β = ν then (d_neg_int k β : ℂ) else 0) • F α β)) =
                    (∑ α : Fin 4, (if α = μ then (d_neg_int k α : ℂ) else 0) • (∑ β : Fin 4, (if β = ν then (d_neg_int k β : ℂ) else 0) • F α β)) := by
    apply Finset.sum_congr rfl; intro α _
    exact Finset.smul_sum.symm

  rw [h_sum_pull]

  have h_inner_apply : (∑ α : Fin 4, (if α = μ then (d_neg_int k α : ℂ) else 0) • (∑ β : Fin 4, (if β = ν then (d_neg_int k β : ℂ) else 0) • F α β)) =
                       (∑ α : Fin 4, (if α = μ then (d_neg_int k α : ℂ) else 0) • ((d_neg_int k ν : ℂ) • F α ν)) := by
    apply Finset.sum_congr rfl; intro α _
    rw [sum_ite_smul_F_inner k ν F α]

  rw [h_inner_apply]
  rw [sum_ite_smul_F_outer k μ ν F]

  by_cases h : μ = k ∨ ν = k
  · rw [h_missing μ ν h]
    rw [smul_zero, smul_zero]
  · push_neg at h
    have h1 : d_neg_int k μ = 1 := by unfold d_neg_int; rw [if_neg h.1]
    have h2 : d_neg_int k ν = 1 := by unfold d_neg_int; rw [if_neg h.2]
    rw [h1, h2]
    have h_cast1 : ((1:ℤ):ℂ) = 1 := by norm_cast
    rw [h_cast1, one_smul, one_smul]

end CGD.Foundations

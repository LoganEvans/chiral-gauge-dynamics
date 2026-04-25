-- FILENAME: CGD/Foundations/Lagrangian.lean

import CGD.Axioms.Dynamics
import CGD.Foundations.Action
import CGD.Gravity.Geometry
import CGD.Litlib.Y1956.utiyama1956invariant.Signature
import Litlib.Y1956.utiyama1956invariant.Signature
import Litlib.Y2003.nakahara2003geometry.Signature
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Matrix Complex BigOperators CGD.Axioms CGD.Foundations

namespace CGD.Foundations

variable [ue : Litlib.Y1956.utiyama1956invariant.UtiyamaExpansion.{0}]
variable [bi : CGD.Litlib.Y1956.utiyama1956invariant.AppendixI_InvariantBilinearForm]
variable [pv : Litlib.Y2003.nakahara2003geometry.PontryaginActionVariation Universe universeAction isValidUniverseVariation]

/-- 
Pure Math Lemma: Any fully alternating rank-4 tensor on a 4D space 
is strictly proportional to the Levi-Civita epsilon tensor. 
Proven using explicit permutation group sign mappings without the unifier.
-/
lemma alternating_is_proportional_to_epsilon (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
  (h_alt : ∀ μ ν ρ σ, 
    T μ ν ρ σ = -T ν μ ρ σ ∧ 
    T μ ν ρ σ = -T μ ρ ν σ ∧ 
    T μ ν ρ σ = -T μ ν σ ρ) :
  ∃ c : ℂ, ∀ μ ν ρ σ, T μ ν ρ σ = c * CGD.Gravity.epsilon4 μ ν ρ σ := by
  use T 0 1 2 3
  have h_swap1 : ∀ μ ν ρ σ, T μ ν ρ σ = -T ν μ ρ σ := fun μ ν ρ σ => (h_alt μ ν ρ σ).1
  have h_swap2 : ∀ μ ν ρ σ, T μ ν ρ σ = -T μ ρ ν σ := fun μ ν ρ σ => (h_alt μ ν ρ σ).2.1
  have h_swap3 : ∀ μ ν ρ σ, T μ ν ρ σ = -T μ ν σ ρ := fun μ ν ρ σ => (h_alt μ ν ρ σ).2.2

  have h_zero : ∀ x : ℂ, x = -x → x = 0 := by
    intro x hx
    have h2 : x + x = x + -x := congrArg (fun y => x + y) hx
    have h3 : x + x = 0 := by
      calc x + x = x + -x := h2
           _ = 0 := add_neg_cancel x
    calc x = (1/2 : ℂ) * (x + x) := by ring
         _ = (1/2 : ℂ) * 0 := by rw [h3]
         _ = 0 := by ring

  have z1 : ∀ μ ρ σ, T μ μ ρ σ = 0 := fun μ ρ σ => h_zero _ (h_swap1 μ μ ρ σ)
  have z2 : ∀ μ ν σ, T μ ν ν σ = 0 := fun μ ν σ => h_zero _ (h_swap2 μ ν ν σ)
  have z3 : ∀ μ ν ρ, T μ ν ρ ρ = 0 := fun μ ν ρ => h_zero _ (h_swap3 μ ν ρ ρ)
  
  have z4 : ∀ μ ν σ, T μ ν μ σ = 0 := by
    intro μ ν σ
    calc T μ ν μ σ = -T ν μ μ σ := h_swap1 μ ν μ σ
         _ = -0 := by rw [z2]
         _ = 0 := by ring

  have z5 : ∀ μ ν ρ, T μ ν ρ μ = 0 := by
    intro μ ν ρ
    calc T μ ν ρ μ = -T ν μ ρ μ := h_swap1 μ ν ρ μ
         _ = -(-T ν ρ μ μ) := by rw [h_swap2 ν μ ρ μ]
         _ = -(-0) := by rw [z3]
         _ = 0 := by ring

  have z6 : ∀ μ ν ρ, T μ ν ρ ν = 0 := by
    intro μ ν ρ
    calc T μ ν ρ ν = -T μ ρ ν ν := h_swap2 μ ν ρ ν
         _ = -0 := by rw [z3]
         _ = 0 := by ring

  have p0132 : T 0 1 3 2 = -T 0 1 2 3 := h_swap3 0 1 3 2
  have p0213 : T 0 2 1 3 = -T 0 1 2 3 := h_swap2 0 2 1 3
  have p0231 : T 0 2 3 1 = T 0 1 2 3 := by 
    calc T 0 2 3 1 = -T 0 2 1 3 := h_swap3 0 2 3 1
         _ = -(-T 0 1 2 3) := by rw [p0213]
         _ = T 0 1 2 3 := by ring
  have p0312 : T 0 3 1 2 = T 0 1 2 3 := by 
    calc T 0 3 1 2 = -T 0 1 3 2 := h_swap2 0 3 1 2
         _ = -(-T 0 1 2 3) := by rw [p0132]
         _ = T 0 1 2 3 := by ring
  have p0321 : T 0 3 2 1 = -T 0 1 2 3 := by 
    calc T 0 3 2 1 = -T 0 3 1 2 := h_swap3 0 3 2 1
         _ = -(T 0 1 2 3) := by rw [p0312]
  
  have p1023 : T 1 0 2 3 = -T 0 1 2 3 := h_swap1 1 0 2 3
  have p1032 : T 1 0 3 2 = T 0 1 2 3 := by 
    calc T 1 0 3 2 = -T 1 0 2 3 := h_swap3 1 0 3 2
         _ = -(-T 0 1 2 3) := by rw [p1023]
         _ = T 0 1 2 3 := by ring
  have p1203 : T 1 2 0 3 = T 0 1 2 3 := by 
    calc T 1 2 0 3 = -T 1 0 2 3 := h_swap2 1 2 0 3
         _ = -(-T 0 1 2 3) := by rw [p1023]
         _ = T 0 1 2 3 := by ring
  have p1230 : T 1 2 3 0 = -T 0 1 2 3 := by 
    calc T 1 2 3 0 = -T 1 2 0 3 := h_swap3 1 2 3 0
         _ = -(T 0 1 2 3) := by rw [p1203]
  have p1302 : T 1 3 0 2 = -T 0 1 2 3 := by 
    calc T 1 3 0 2 = -T 1 0 3 2 := h_swap2 1 3 0 2
         _ = -(T 0 1 2 3) := by rw [p1032]
  have p1320 : T 1 3 2 0 = T 0 1 2 3 := by 
    calc T 1 3 2 0 = -T 1 3 0 2 := h_swap3 1 3 2 0
         _ = -(-T 0 1 2 3) := by rw [p1302]
         _ = T 0 1 2 3 := by ring
  
  have p2013 : T 2 0 1 3 = T 0 1 2 3 := by 
    calc T 2 0 1 3 = -T 0 2 1 3 := h_swap1 2 0 1 3
         _ = -(-T 0 1 2 3) := by rw [p0213]
         _ = T 0 1 2 3 := by ring
  have p2031 : T 2 0 3 1 = -T 0 1 2 3 := by 
    calc T 2 0 3 1 = -T 2 0 1 3 := h_swap3 2 0 3 1
         _ = -(T 0 1 2 3) := by rw [p2013]
  have p2103 : T 2 1 0 3 = -T 0 1 2 3 := by 
    calc T 2 1 0 3 = -T 2 0 1 3 := h_swap2 2 1 0 3
         _ = -(T 0 1 2 3) := by rw [p2013]
  have p2130 : T 2 1 3 0 = T 0 1 2 3 := by 
    calc T 2 1 3 0 = -T 2 1 0 3 := h_swap3 2 1 3 0
         _ = -(-T 0 1 2 3) := by rw [p2103]
         _ = T 0 1 2 3 := by ring
  have p2301 : T 2 3 0 1 = T 0 1 2 3 := by 
    calc T 2 3 0 1 = -T 2 0 3 1 := h_swap2 2 3 0 1
         _ = -(-T 0 1 2 3) := by rw [p2031]
         _ = T 0 1 2 3 := by ring
  have p2310 : T 2 3 1 0 = -T 0 1 2 3 := by 
    calc T 2 3 1 0 = -T 2 3 0 1 := h_swap3 2 3 1 0
         _ = -(T 0 1 2 3) := by rw [p2301]
  
  have p3012 : T 3 0 1 2 = -T 0 1 2 3 := by 
    calc T 3 0 1 2 = -T 0 3 1 2 := h_swap1 3 0 1 2
         _ = -(T 0 1 2 3) := by rw [p0312]
  have p3021 : T 3 0 2 1 = T 0 1 2 3 := by 
    calc T 3 0 2 1 = -T 3 0 1 2 := h_swap3 3 0 2 1
         _ = -(-T 0 1 2 3) := by rw [p3012]
         _ = T 0 1 2 3 := by ring
  have p3102 : T 3 1 0 2 = T 0 1 2 3 := by 
    calc T 3 1 0 2 = -T 3 0 1 2 := h_swap2 3 1 0 2
         _ = -(-T 0 1 2 3) := by rw [p3012]
         _ = T 0 1 2 3 := by ring
  have p3120 : T 3 1 2 0 = -T 0 1 2 3 := by 
    calc T 3 1 2 0 = -T 3 1 0 2 := h_swap3 3 1 2 0
         _ = -(T 0 1 2 3) := by rw [p3102]
  have p3201 : T 3 2 0 1 = -T 0 1 2 3 := by 
    calc T 3 2 0 1 = -T 3 0 2 1 := h_swap2 3 2 0 1
         _ = -(T 0 1 2 3) := by rw [p3021]
  have p3210 : T 3 2 1 0 = T 0 1 2 3 := by 
    calc T 3 2 1 0 = -T 3 2 0 1 := h_swap3 3 2 1 0
         _ = -(-T 0 1 2 3) := by rw [p3201]
         _ = T 0 1 2 3 := by ring

  intro μ ν ρ σ
  fin_cases μ <;> fin_cases ν <;> fin_cases ρ <;> fin_cases σ <;> {
    unfold CGD.Gravity.epsilon4
    dsimp [CGD.Gravity.epsilon4_int]
    push_cast
    try rw [z1]
    try rw [z2]
    try rw [z3]
    try rw [z4]
    try rw [z5]
    try rw [z6]
    try rw [p0132]
    try rw [p0213]
    try rw [p0231]
    try rw [p0312]
    try rw [p0321]
    try rw [p1023]
    try rw [p1032]
    try rw [p1203]
    try rw [p1230]
    try rw [p1302]
    try rw [p1320]
    try rw [p2013]
    try rw [p2031]
    try rw [p2103]
    try rw [p2130]
    try rw [p2301]
    try rw [p2310]
    try rw [p3012]
    try rw [p3021]
    try rw [p3102]
    try rw [p3120]
    try rw [p3201]
    try rw [p3210]
    ring
  }

lemma action_variation_master_lemma (u : Universe) (v : ℝ → Universe) 
  (h_valid : isValidUniverseVariation v)
  (h_zero : v 0 = u) :
  HasDerivAt (fun t => universeAction (v t)) 0 0 := by
  exact Litlib.Y2003.nakahara2003geometry.PontryaginActionVariation.variation_zero u v h_valid h_zero

/-- Rigorous evaluator for pulling Kronecker deltas out of sums without `simp` explosion. -/
lemma sum_ite_mul {α β : Type*} [Ring β] [Fintype α] [DecidableEq α] 
  (a : α) (f : α → β) (g : α → β) :
  (∑ x : α, (if x = a then f x else 0) * g x) = f a * g a := by
  have h : ∀ x, (if x = a then f x else 0) * g x = if x = a then f x * g x else 0 := by
    intro x
    split_ifs
    · rfl
    · exact zero_mul (g x)
  rw [Finset.sum_congr rfl (fun x _ => h x)]
  rw [Finset.sum_eq_single a]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb]
  · intro h_not_in
    exfalso
    exact h_not_in (Finset.mem_univ a)

lemma eps_diag_factor (d : Fin 4 → ℂ) (μ ν ρ σ : Fin 4) :
  (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
    (if α = μ then d α else 0) * (if β = ν then d β else 0) * (if γ = ρ then d γ else 0) * (if δ = σ then d δ else 0) * CGD.Gravity.epsilon4 α β γ δ) = 
  ∑ α : Fin 4, (if α = μ then d α else 0) * 
    (∑ β : Fin 4, (if β = ν then d β else 0) * 
      (∑ γ : Fin 4, (if γ = ρ then d γ else 0) * 
        (∑ δ : Fin 4, (if δ = σ then d δ else 0) * CGD.Gravity.epsilon4 α β γ δ))) := by
  symm
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro α _
  apply Finset.sum_congr rfl; intro β _
  apply Finset.sum_congr rfl; intro γ _
  apply Finset.sum_congr rfl; intro δ _
  ring

lemma eps_diag_rearrange (d : Fin 4 → ℂ) (μ ν ρ σ : Fin 4) :
  (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
    (if α = μ then d α else 0) * (if β = ν then d β else 0) * (if γ = ρ then d γ else 0) * (if δ = σ then d δ else 0) * CGD.Gravity.epsilon4 α β γ δ) = 
  (d μ * d ν * d ρ * d σ) * CGD.Gravity.epsilon4 μ ν ρ σ := by
  rw [eps_diag_factor]
  rw [sum_ite_mul]
  rw [sum_ite_mul]
  rw [sum_ite_mul]
  rw [sum_ite_mul]
  ring

lemma eps_perm_factor (p : Fin 4 → Fin 4) (μ ν ρ σ : Fin 4) :
  (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
    (if α = p μ then (1:ℂ) else 0) * (if β = p ν then (1:ℂ) else 0) * (if γ = p ρ then (1:ℂ) else 0) * (if δ = p σ then (1:ℂ) else 0) * CGD.Gravity.epsilon4 α β γ δ) = 
  ∑ α : Fin 4, (if α = p μ then (1:ℂ) else 0) * 
    (∑ β : Fin 4, (if β = p ν then (1:ℂ) else 0) * 
      (∑ γ : Fin 4, (if γ = p ρ then (1:ℂ) else 0) * 
        (∑ δ : Fin 4, (if δ = p σ then (1:ℂ) else 0) * CGD.Gravity.epsilon4 α β γ δ))) := by
  symm
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro α _
  apply Finset.sum_congr rfl; intro β _
  apply Finset.sum_congr rfl; intro γ _
  apply Finset.sum_congr rfl; intro δ _
  ring

lemma eps_perm_rearrange (p : Fin 4 → Fin 4) (μ ν ρ σ : Fin 4) :
  (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
    (if α = p μ then (1:ℂ) else 0) * (if β = p ν then (1:ℂ) else 0) * (if γ = p ρ then (1:ℂ) else 0) * (if δ = p σ then (1:ℂ) else 0) * CGD.Gravity.epsilon4 α β γ δ) = 
  CGD.Gravity.epsilon4 (p μ) (p ν) (p ρ) (p σ) := by
  rw [eps_perm_factor]
  rw [sum_ite_mul]
  rw [sum_ite_mul]
  rw [sum_ite_mul]
  rw [sum_ite_mul]
  ring

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

/-- Rigorous evaluator for pulling Kronecker deltas out of scalar-multiplied sums. -/
lemma sum_ite_smul {α M : Type*} [AddCommMonoid M] [Module ℂ M] [Fintype α] [DecidableEq α]
  (a : α) (f : α → ℂ) (g : α → M) :
  (∑ x : α, (if x = a then f x else 0) • g x) = f a • g a := by
  have h : ∀ x, (if x = a then f x else 0) • g x = if x = a then f x • g x else 0 := by
    intro x
    split_ifs
    · rfl
    · exact zero_smul ℂ (g x)
  rw [Finset.sum_congr rfl (fun x _ => h x)]
  rw [Finset.sum_eq_single a]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb]
  · intro h_not_in
    exfalso
    exact h_not_in (Finset.mem_univ a)

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
  -- Explicitly bypass the unifier for mul_smul
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

/-- 
Executes 4096 discrete permutation evaluations natively in Lean to prove that swapping 
two indices of the Levi-Civita symbol strictly multiplies it by the permutation sign.
-/
lemma epsilon_int_swap (a b μ ν ρ σ : Fin 4) :
  CGD.Gravity.epsilon4_int (Equiv.swap a b μ) (Equiv.swap a b ν) (Equiv.swap a b ρ) (Equiv.swap a b σ) =
  (Equiv.Perm.sign (Equiv.swap a b) : ℤ) * CGD.Gravity.epsilon4_int μ ν ρ σ := by
  revert a b μ ν ρ σ
  decide

lemma epsilon_swap_sign (a b μ ν ρ σ : Fin 4) :
  CGD.Gravity.epsilon4 (Equiv.swap a b μ) (Equiv.swap a b ν) (Equiv.swap a b ρ) (Equiv.swap a b σ) =
  (Equiv.Perm.sign (Equiv.swap a b) : ℂ) * CGD.Gravity.epsilon4 μ ν ρ σ := by
  unfold CGD.Gravity.epsilon4
  have h := epsilon_int_swap a b μ ν ρ σ
  have h_cast : ((CGD.Gravity.epsilon4_int (Equiv.swap a b μ) (Equiv.swap a b ν) (Equiv.swap a b ρ) (Equiv.swap a b σ) : ℂ)) =
    (((Equiv.Perm.sign (Equiv.swap a b) : ℤ) * CGD.Gravity.epsilon4_int μ ν ρ σ : ℤ) : ℂ) := by
    rw [h]
  push_cast at h_cast
  exact h_cast

/-- Formalizes the symmetric component of the rank-4 tensor. -/
def symm_part (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) (μ ν ρ σ : Fin 4) : ℂ :=
  T μ ν ρ σ + T ρ σ μ ν

/-- Rigorous sum swapping to bypass unifier failures. -/
lemma sum_swap_ab_cd (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
  (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4, f a b c d) =
  (∑ c : Fin 4, ∑ d : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4, f a b c d) := by
  have h1 : (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
    apply Finset.sum_congr rfl; intro a _
    exact Finset.sum_comm
  rw [h1]
  have h2 : (∑ a, ∑ c, ∑ b, ∑ d, f a b c d) = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
  rw [h2]
  have h3 : (∑ c, ∑ a, ∑ b, ∑ d, f a b c d) = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro a _
    exact Finset.sum_comm
  rw [h3]
  apply Finset.sum_congr rfl; intro c _
  exact Finset.sum_comm

lemma sum_T_trace_swap (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) (F : Fin 4 → Fin 4 → ChiralM) :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, T μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ)) =
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, T ρ σ μ ν * Matrix.trace (F μ ν * F ρ σ)) := by
  have h_swap_sum := sum_swap_ab_cd (fun a b c d => T a b c d * Matrix.trace (F a b * F c d))
  rw [h_swap_sum]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [Matrix.trace_mul_comm (F a b) (F c d)]

lemma L_eq_symm_part (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) (F : Fin 4 → Fin 4 → ChiralM) :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, T μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ)) =
  (1 / 2 : ℂ) * ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, symm_part T μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ) := by
  unfold symm_part
  simp_rw [add_mul, Finset.sum_add_distrib]
  have h1 : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, T ρ σ μ ν * Matrix.trace (F μ ν * F ρ σ)) =
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, T μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ)) := Eq.symm (sum_T_trace_swap T F)
  rw [h1]
  ring

lemma ite_and_mul (α μ β ν : Fin 4) : 
  (if α = μ ∧ β = ν then (1:ℂ) else 0) = (if α = μ then (1:ℂ) else 0) * (if β = ν then (1:ℂ) else 0) := by
  by_cases h1 : α = μ
  · by_cases h2 : β = ν
    · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, mul_one]
    · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul]

lemma h_or_ex (μ ν ρ σ α β : Fin 4) (h_diff : μ ≠ ρ ∨ ν ≠ σ) : 
  ¬ ((α = μ ∧ β = ν) ∧ (α = ρ ∧ β = σ)) := by
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  rcases h_diff with hd | hd
  · exact hd (h1.symm.trans h3)
  · exact hd (h2.symm.trans h4)

def F_single (μ ν : Fin 4) (M : ChiralM) : Fin 4 → Fin 4 → ChiralM :=
  fun α β => if α = μ ∧ β = ν then M else 0

def F_double (μ ν ρ σ : Fin 4) (M : ChiralM) : Fin 4 → Fin 4 → ChiralM :=
  fun α β => if (α = μ ∧ β = ν) ∨ (α = ρ ∧ β = σ) then M else 0

lemma ite_F_single_sq (μ ν : Fin 4) (M : ChiralM) (α β γ δ : Fin 4) :
  Matrix.trace (F_single μ ν M α β * F_single μ ν M γ δ) =
  (if α = μ ∧ β = ν then (1:ℂ) else 0) * (if γ = μ ∧ δ = ν then (1:ℂ) else 0) * Matrix.trace (M * M) := by
  unfold F_single
  by_cases h1 : α = μ ∧ β = ν
  · by_cases h2 : γ = μ ∧ δ = ν
    · have hf1 : (if α = μ ∧ β = ν then M else 0) = M := if_pos h1
      have hf2 : (if γ = μ ∧ δ = ν then M else 0) = M := if_pos h2
      have hi1 : (if α = μ ∧ β = ν then (1:ℂ) else 0) = 1 := if_pos h1
      have hi2 : (if γ = μ ∧ δ = ν then (1:ℂ) else 0) = 1 := if_pos h2
      rw [hf1, hf2, hi1, hi2]
      ring
    · have hf1 : (if α = μ ∧ β = ν then M else 0) = M := if_pos h1
      have hf2 : (if γ = μ ∧ δ = ν then M else 0) = 0 := if_neg h2
      have hi2 : (if γ = μ ∧ δ = ν then (1:ℂ) else 0) = 0 := if_neg h2
      rw [hf1, hf2, hi2]
      have hz : M * 0 = 0 := Matrix.mul_zero M
      rw [hz, Matrix.trace_zero]
      ring
  · have hf1 : (if α = μ ∧ β = ν then M else 0) = 0 := if_neg h1
    have hi1 : (if α = μ ∧ β = ν then (1:ℂ) else 0) = 0 := if_neg h1
    rw [hf1, hi1]
    have hz : 0 * (if γ = μ ∧ δ = ν then M else 0) = 0 := Matrix.zero_mul _
    rw [hz, Matrix.trace_zero]
    ring

lemma ite_F_double_sq (μ ν ρ σ : Fin 4) (M : ChiralM) (α β γ δ : Fin 4) (h_diff : μ ≠ ρ ∨ ν ≠ σ) :
  Matrix.trace (F_double μ ν ρ σ M α β * F_double μ ν ρ σ M γ δ) =
  ((if α = μ ∧ β = ν then (1:ℂ) else 0) + (if α = ρ ∧ β = σ then (1:ℂ) else 0)) * 
  ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) * 
  Matrix.trace (M * M) := by
  unfold F_double
  have hex_a := h_or_ex μ ν ρ σ α β h_diff
  have hex_g := h_or_ex μ ν ρ σ γ δ h_diff
  
  by_cases ha1 : α = μ ∧ β = ν
  · have ha2 : ¬ (α = ρ ∧ β = σ) := fun h => hex_a ⟨ha1, h⟩
    have hfa : (if α = μ ∧ β = ν ∨ α = ρ ∧ β = σ then M else 0) = M := if_pos (Or.inl ha1)
    have hea : ((if α = μ ∧ β = ν then (1:ℂ) else 0) + (if α = ρ ∧ β = σ then (1:ℂ) else 0)) = 1 := by rw [if_pos ha1, if_neg ha2]; ring
    
    by_cases hg1 : γ = μ ∧ δ = ν
    · have hg2 : ¬ (γ = ρ ∧ δ = σ) := fun h => hex_g ⟨hg1, h⟩
      have hfg : (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = M := if_pos (Or.inl hg1)
      have heg : ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) = 1 := by rw [if_pos hg1, if_neg hg2]; ring
      rw [hfa, hfg, hea, heg]; ring
    · by_cases hg2 : γ = ρ ∧ δ = σ
      · have hfg : (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = M := if_pos (Or.inr hg2)
        have heg : ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) = 1 := by rw [if_neg hg1, if_pos hg2]; ring
        rw [hfa, hfg, hea, heg]; ring
      · have hfg : (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = 0 := if_neg (fun h => h.elim hg1 hg2)
        have heg : ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) = 0 := by rw [if_neg hg1, if_neg hg2]; ring
        rw [hfa, hfg, hea, heg]
        have hz : M * 0 = 0 := Matrix.mul_zero M
        rw [hz, Matrix.trace_zero]; ring
  · by_cases ha2 : α = ρ ∧ β = σ
    · have hfa : (if α = μ ∧ β = ν ∨ α = ρ ∧ β = σ then M else 0) = M := if_pos (Or.inr ha2)
      have hea : ((if α = μ ∧ β = ν then (1:ℂ) else 0) + (if α = ρ ∧ β = σ then (1:ℂ) else 0)) = 1 := by rw [if_neg ha1, if_pos ha2]; ring
      
      by_cases hg1 : γ = μ ∧ δ = ν
      · have hg2 : ¬ (γ = ρ ∧ δ = σ) := fun h => hex_g ⟨hg1, h⟩
        have hfg : (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = M := if_pos (Or.inl hg1)
        have heg : ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) = 1 := by rw [if_pos hg1, if_neg hg2]; ring
        rw [hfa, hfg, hea, heg]; ring
      · by_cases hg2 : γ = ρ ∧ δ = σ
        · have hfg : (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = M := if_pos (Or.inr hg2)
          have heg : ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) = 1 := by rw [if_neg hg1, if_pos hg2]; ring
          rw [hfa, hfg, hea, heg]; ring
        · have hfg : (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = 0 := if_neg (fun h => h.elim hg1 hg2)
          have heg : ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) = 0 := by rw [if_neg hg1, if_neg hg2]; ring
          rw [hfa, hfg, hea, heg]
          have hz : M * 0 = 0 := Matrix.mul_zero M
          rw [hz, Matrix.trace_zero]; ring
    · have hfa : (if α = μ ∧ β = ν ∨ α = ρ ∧ β = σ then M else 0) = 0 := if_neg (fun h => h.elim ha1 ha2)
      have hea : ((if α = μ ∧ β = ν then (1:ℂ) else 0) + (if α = ρ ∧ β = σ then (1:ℂ) else 0)) = 0 := by rw [if_neg ha1, if_neg ha2]; ring
      rw [hfa, hea]
      have hz : 0 * (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = 0 := Matrix.zero_mul _
      rw [hz, Matrix.trace_zero]; ring

lemma L_single_eval (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) 
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_L_eq : ∀ F, L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (μ ν : Fin 4) (M : ChiralM) :
  L (F_single μ ν M) = T μ ν μ ν * Matrix.trace (M * M) := by
  rw [h_L_eq]
  simp_rw [ite_F_single_sq]
  have h_term : ∀ α β γ δ, T α β γ δ * ((if α = μ ∧ β = ν then (1:ℂ) else 0) * (if γ = μ ∧ δ = ν then (1:ℂ) else 0) * Matrix.trace (M * M)) =
    (if α = μ then (1:ℂ) else 0) * (if β = ν then (1:ℂ) else 0) * ((if γ = μ then (1:ℂ) else 0) * (if δ = ν then (1:ℂ) else 0)) * (T α β γ δ * Matrix.trace (M * M)) := by
    intro α β γ δ
    rw [ite_and_mul α μ β ν, ite_and_mul γ μ δ ν]
    ring
  simp_rw [h_term]
  have h_pull : (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, (if α = μ then (1:ℂ) else 0) * (if β = ν then (1:ℂ) else 0) * ((if γ = μ then (1:ℂ) else 0) * (if δ = ν then (1:ℂ) else 0)) * (T α β γ δ * Matrix.trace (M * M))) =
    ∑ α : Fin 4, (if α = μ then (1:ℂ) else 0) * 
      (∑ β : Fin 4, (if β = ν then (1:ℂ) else 0) * 
        (∑ γ : Fin 4, (if γ = μ then (1:ℂ) else 0) * 
          (∑ δ : Fin 4, (if δ = ν then (1:ℂ) else 0) * (T α β γ δ * Matrix.trace (M * M))))) := by
    symm
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro β _
    apply Finset.sum_congr rfl; intro γ _
    apply Finset.sum_congr rfl; intro δ _
    ring
  rw [h_pull, sum_ite_mul, sum_ite_mul, sum_ite_mul, sum_ite_mul]
  ring

lemma L_double_eval (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) 
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_L_eq : ∀ F, L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (μ ν ρ σ : Fin 4) (M : ChiralM) (h_diff : μ ≠ ρ ∨ ν ≠ σ) :
  L (F_double μ ν ρ σ M) = (T μ ν μ ν + T μ ν ρ σ + T ρ σ μ ν + T ρ σ ρ σ) * Matrix.trace (M * M) := by
  rw [h_L_eq]
  have h_term : ∀ α β γ δ, T α β γ δ * Matrix.trace (F_double μ ν ρ σ M α β * F_double μ ν ρ σ M γ δ) =
    ((if α = μ ∧ β = ν then (1:ℂ) else 0) + (if α = ρ ∧ β = σ then (1:ℂ) else 0)) * 
    ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) * 
    (T α β γ δ * Matrix.trace (M * M)) := by
    intro α β γ δ
    rw [ite_F_double_sq μ ν ρ σ M α β γ δ h_diff]
    ring
  simp_rw [h_term]
  have h_expand : ∀ a b c d x : ℂ, (a + b) * (c + d) * x = a * c * x + a * d * x + b * c * x + b * d * x := by intro a b c d x; ring
  simp_rw [h_expand, Finset.sum_add_distrib]
  have h_sum_pair : ∀ a b c d, (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, (if α = a ∧ β = b then (1:ℂ) else 0) * (if γ = c ∧ δ = d then (1:ℂ) else 0) * (T α β γ δ * Matrix.trace (M * M))) = T a b c d * Matrix.trace (M * M) := by
    intro a b c d
    simp_rw [ite_and_mul]
    have h_pull : (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, (if α = a then (1:ℂ) else 0) * (if β = b then (1:ℂ) else 0) * ((if γ = c then (1:ℂ) else 0) * (if δ = d then (1:ℂ) else 0)) * (T α β γ δ * Matrix.trace (M * M))) =
      ∑ α : Fin 4, (if α = a then (1:ℂ) else 0) * 
        (∑ β : Fin 4, (if β = b then (1:ℂ) else 0) * 
          (∑ γ : Fin 4, (if γ = c then (1:ℂ) else 0) * 
            (∑ δ : Fin 4, (if δ = d then (1:ℂ) else 0) * (T α β γ δ * Matrix.trace (M * M))))) := by
      symm
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro α _
      apply Finset.sum_congr rfl; intro β _
      apply Finset.sum_congr rfl; intro γ _
      apply Finset.sum_congr rfl; intro δ _
      ring
    rw [h_pull, sum_ite_mul, sum_ite_mul, sum_ite_mul, sum_ite_mul]
    ring
  rw [h_sum_pair μ ν μ ν, h_sum_pair μ ν ρ σ, h_sum_pair ρ σ μ ν, h_sum_pair ρ σ ρ σ]
  ring

lemma lorentz_trace_1 : Matrix.trace (CGD.Gravity.lorentzGenerators 1 * CGD.Gravity.lorentzGenerators 1) = 2 := by
  have h_mat : CGD.Gravity.lorentzGenerators 1 = Matrix.of ![![ (0:ℂ), 0, 1, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]] := rfl
  rw [h_mat]
  unfold Matrix.trace Matrix.diag
  simp_rw [Matrix.mul_apply]
  simp [Fin.sum_univ_four, Matrix.of_apply]
  norm_num

lemma extract_symm_part_eq
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
  (h_L_eq : ∀ F, L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (μ ν : Fin 4) :
  symm_part T μ ν μ ν = L (F_single μ ν (CGD.Gravity.lorentzGenerators 1)) / 2 * 2 := by
  have h_s := L_single_eval T L h_L_eq μ ν (CGD.Gravity.lorentzGenerators 1)
  rw [lorentz_trace_1] at h_s
  calc symm_part T μ ν μ ν = T μ ν μ ν + T μ ν μ ν := rfl
       _ = T μ ν μ ν * 2 := by ring
       _ = (T μ ν μ ν * 2) / 2 * 2 := by ring
       _ = L (F_single μ ν (CGD.Gravity.lorentzGenerators 1)) / 2 * 2 := by rw [h_s]

lemma extract_symm_part 
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
  (h_L_eq : ∀ F, L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (μ ν ρ σ : Fin 4) (h_diff : μ ≠ ρ ∨ ν ≠ σ) :
  symm_part T μ ν ρ σ = (L (F_double μ ν ρ σ (CGD.Gravity.lorentzGenerators 1)) - 
                         L (F_single μ ν (CGD.Gravity.lorentzGenerators 1)) - 
                         L (F_single ρ σ (CGD.Gravity.lorentzGenerators 1))) / 2 := by
  have h_d := L_double_eval T L h_L_eq μ ν ρ σ (CGD.Gravity.lorentzGenerators 1) h_diff
  have h_s1 := L_single_eval T L h_L_eq μ ν (CGD.Gravity.lorentzGenerators 1)
  have h_s2 := L_single_eval T L h_L_eq ρ σ (CGD.Gravity.lorentzGenerators 1)
  rw [lorentz_trace_1] at h_d h_s1 h_s2
  calc symm_part T μ ν ρ σ = T μ ν ρ σ + T ρ σ μ ν := rfl
       _ = ((T μ ν μ ν + T μ ν ρ σ + T ρ σ μ ν + T ρ σ ρ σ) * 2 - T μ ν μ ν * 2 - T ρ σ ρ σ * 2) / 2 := by ring
       _ = (L (F_double μ ν ρ σ (CGD.Gravity.lorentzGenerators 1)) - L (F_single μ ν (CGD.Gravity.lorentzGenerators 1)) - L (F_single ρ σ (CGD.Gravity.lorentzGenerators 1))) / 2 := by rw [h_d, h_s1, h_s2]

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

lemma L_zero_missing 
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_topological : ∀ Λ : Matrix (Fin 4) (Fin 4) ℂ, 
    (∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
      Λ α μ * Λ β ν * Λ γ ρ * Λ δ σ * CGD.Gravity.epsilon4 α β γ δ = Matrix.det Λ * CGD.Gravity.epsilon4 μ ν ρ σ) →
    ∀ F, L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F)
  (k : Fin 4) (F : Fin 4 → Fin 4 → ChiralM)
  (h_missing : ∀ μ ν, μ = k ∨ ν = k → F μ ν = 0) :
  L F = 0 := by
  have h_eval := h_topological (Lambda_neg_mat k) (Lambda_neg_topological k) F
  rw [Lambda_neg_F k F h_missing] at h_eval
  rw [det_Lambda_neg_mat k] at h_eval
  have h_eq : L F = - L F := by
    calc L F = -1 * L F := h_eval
         _ = - L F := by ring
  have h_eq_add : L F + L F = L F + -L F := congrArg (fun x => L F + x) h_eq
  calc L F = (1/2 : ℂ) * (L F + L F) := by ring
       _ = (1/2 : ℂ) * (L F + - L F) := by rw [h_eq_add]
       _ = 0 := by ring

lemma missing_index_of_dup (μ ν ρ σ : Fin 4) (h_dup : ¬ (μ ≠ ν ∧ μ ≠ ρ ∧ μ ≠ σ ∧ ν ≠ ρ ∧ ν ≠ σ ∧ ρ ≠ σ)) :
  ∃ k : Fin 4, k ≠ μ ∧ k ≠ ν ∧ k ≠ ρ ∧ k ≠ σ := by
  revert μ ν ρ σ
  decide

lemma F_single_missing (μ ν : Fin 4) (M : ChiralM) (k : Fin 4) (hk : k ≠ μ ∧ k ≠ ν) :
  ∀ α β, α = k ∨ β = k → F_single μ ν M α β = 0 := by
  intro α β h_or
  unfold F_single
  split_ifs with h_cond
  · rcases h_or with ha | hb
    · rw [h_cond.1] at ha; exfalso; exact hk.1 ha.symm
    · rw [h_cond.2] at hb; exfalso; exact hk.2 hb.symm
  · rfl

lemma F_double_missing (μ ν ρ σ : Fin 4) (M : ChiralM) (k : Fin 4) 
  (hk : k ≠ μ ∧ k ≠ ν ∧ k ≠ ρ ∧ k ≠ σ) :
  ∀ α β, α = k ∨ β = k → F_double μ ν ρ σ M α β = 0 := by
  intro α β h_or
  unfold F_double
  split_ifs with h_cond
  · rcases h_or with ha | hb
    · rcases h_cond with ⟨h1, h2⟩ | ⟨h3, h4⟩
      · rw [h1] at ha; exfalso; exact hk.1 ha.symm
      · rw [h3] at ha; exfalso; exact hk.2.2.1 ha.symm
    · rcases h_cond with ⟨h1, h2⟩ | ⟨h3, h4⟩
      · rw [h2] at hb; exfalso; exact hk.2.1 hb.symm
      · rw [h4] at hb; exfalso; exact hk.2.2.2 hb.symm
  · rfl

lemma symm_part_zero_of_dup 
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_topological : ∀ Λ : Matrix (Fin 4) (Fin 4) ℂ, 
    (∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
      Λ α μ * Λ β ν * Λ γ ρ * Λ δ σ * CGD.Gravity.epsilon4 α β γ δ = Matrix.det Λ * CGD.Gravity.epsilon4 μ ν ρ σ) →
    ∀ F, L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F)
  (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
  (h_L_eq : ∀ F, L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (μ ν ρ σ : Fin 4) (h_dup : ¬ (μ ≠ ν ∧ μ ≠ ρ ∧ μ ≠ σ ∧ ν ≠ ρ ∧ ν ≠ σ ∧ ρ ≠ σ)) :
  symm_part T μ ν ρ σ = 0 := by
  have ⟨k, hk⟩ := missing_index_of_dup μ ν ρ σ h_dup
  by_cases h_diff_eq : μ = ρ ∧ ν = σ
  · rcases h_diff_eq with ⟨rfl, rfl⟩
    have h_ex := extract_symm_part_eq L T h_L_eq μ ν
    have hk_single : k ≠ μ ∧ k ≠ ν := ⟨hk.1, hk.2.1⟩
    have h_miss := F_single_missing μ ν (CGD.Gravity.lorentzGenerators 1) k hk_single
    have h_z := L_zero_missing L h_topological k (F_single μ ν (CGD.Gravity.lorentzGenerators 1)) h_miss
    calc symm_part T μ ν μ ν = L (F_single μ ν (CGD.Gravity.lorentzGenerators 1)) / 2 * 2 := h_ex
         _ = 0 / 2 * 2 := by rw [h_z]
         _ = 0 := by ring
  · have h_diff : μ ≠ ρ ∨ ν ≠ σ := not_and_or.mp h_diff_eq
    have h_ex := extract_symm_part L T h_L_eq μ ν ρ σ h_diff
    have hk_s1 : k ≠ μ ∧ k ≠ ν := ⟨hk.1, hk.2.1⟩
    have hk_s2 : k ≠ ρ ∧ k ≠ σ := ⟨hk.2.2.1, hk.2.2.2⟩
    have h_miss_d := F_double_missing μ ν ρ σ (CGD.Gravity.lorentzGenerators 1) k hk
    have h_miss_s1 := F_single_missing μ ν (CGD.Gravity.lorentzGenerators 1) k hk_s1
    have h_miss_s2 := F_single_missing ρ σ (CGD.Gravity.lorentzGenerators 1) k hk_s2
    have h_zd := L_zero_missing L h_topological k _ h_miss_d
    have h_zs1 := L_zero_missing L h_topological k _ h_miss_s1
    have h_zs2 := L_zero_missing L h_topological k _ h_miss_s2
    rw [h_zd, h_zs1, h_zs2] at h_ex
    calc symm_part T μ ν ρ σ = (0 - 0 - 0) / 2 := h_ex
         _ = 0 := by ring

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

lemma L_swap_F
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_topological : ∀ Λ : Matrix (Fin 4) (Fin 4) ℂ, 
    (∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
      Λ α μ * Λ β ν * Λ γ ρ * Λ δ σ * CGD.Gravity.epsilon4 α β γ δ = Matrix.det Λ * CGD.Gravity.epsilon4 μ ν ρ σ) →
    ∀ F, L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F)
  (a b : Fin 4) (hab : a ≠ b) (F : Fin 4 → Fin 4 → ChiralM) :
  L (fun μ ν => F (Equiv.swap a b μ) (Equiv.swap a b ν)) = - L F := by
  have h_eval := h_topological (permMatrix (Equiv.swap a b)) (swapMatrix_topological_C a b hab) F
  rw [det_swapMatrix a b hab] at h_eval
  have h_F := permMatrix_apply (Equiv.swap a b) F
  have h_symm : (Equiv.swap a b).symm = Equiv.swap a b := Equiv.symm_swap a b
  rw [h_symm] at h_F
  rw [h_F] at h_eval
  calc L (fun μ ν => F (Equiv.swap a b μ) (Equiv.swap a b ν)) = -1 * L F := h_eval
       _ = - L F := by ring

lemma F_single_swap (a b μ ν : Fin 4) (M : ChiralM) :
  (fun α β => F_single μ ν M (Equiv.swap a b α) (Equiv.swap a b β)) = F_single (Equiv.swap a b μ) (Equiv.swap a b ν) M := by
  ext α β
  unfold F_single
  have h1 : Equiv.swap a b α = μ ↔ α = Equiv.swap a b μ := Equiv.swap_apply_eq_iff
  have h2 : Equiv.swap a b β = ν ↔ β = Equiv.swap a b ν := Equiv.swap_apply_eq_iff
  by_cases h : Equiv.swap a b α = μ ∧ Equiv.swap a b β = ν
  · have h_pos1 : (if Equiv.swap a b α = μ ∧ Equiv.swap a b β = ν then M else 0) = M := if_pos h
    have h_eq : α = Equiv.swap a b μ ∧ β = Equiv.swap a b ν := ⟨h1.mp h.1, h2.mp h.2⟩
    have h_pos2 : (if α = Equiv.swap a b μ ∧ β = Equiv.swap a b ν then M else 0) = M := if_pos h_eq
    rw [h_pos1, h_pos2]
  · have h_neg1 : (if Equiv.swap a b α = μ ∧ Equiv.swap a b β = ν then M else 0) = 0 := if_neg h
    have h_eq : ¬(α = Equiv.swap a b μ ∧ β = Equiv.swap a b ν) := fun hc => h ⟨h1.mpr hc.1, h2.mpr hc.2⟩
    have h_neg2 : (if α = Equiv.swap a b μ ∧ β = Equiv.swap a b ν then M else 0) = 0 := if_neg h_eq
    rw [h_neg1, h_neg2]

lemma F_double_swap (a b μ ν ρ σ : Fin 4) (M : ChiralM) :
  (fun α β => F_double μ ν ρ σ M (Equiv.swap a b α) (Equiv.swap a b β)) = F_double (Equiv.swap a b μ) (Equiv.swap a b ν) (Equiv.swap a b ρ) (Equiv.swap a b σ) M := by
  ext α β
  unfold F_double
  have h1 : Equiv.swap a b α = μ ↔ α = Equiv.swap a b μ := Equiv.swap_apply_eq_iff
  have h2 : Equiv.swap a b β = ν ↔ β = Equiv.swap a b ν := Equiv.swap_apply_eq_iff
  have h3 : Equiv.swap a b α = ρ ↔ α = Equiv.swap a b ρ := Equiv.swap_apply_eq_iff
  have h4 : Equiv.swap a b β = σ ↔ β = Equiv.swap a b σ := Equiv.swap_apply_eq_iff
  by_cases h : (Equiv.swap a b α = μ ∧ Equiv.swap a b β = ν) ∨ (Equiv.swap a b α = ρ ∧ Equiv.swap a b β = σ)
  · have h_pos1 : (if (Equiv.swap a b α = μ ∧ Equiv.swap a b β = ν) ∨ (Equiv.swap a b α = ρ ∧ Equiv.swap a b β = σ) then M else 0) = M := if_pos h
    have h_eq : (α = Equiv.swap a b μ ∧ β = Equiv.swap a b ν) ∨ (α = Equiv.swap a b ρ ∧ β = Equiv.swap a b σ) := by
      rcases h with hl | hr
      · exact Or.inl ⟨h1.mp hl.1, h2.mp hl.2⟩
      · exact Or.inr ⟨h3.mp hr.1, h4.mp hr.2⟩
    have h_pos2 : (if (α = Equiv.swap a b μ ∧ β = Equiv.swap a b ν) ∨ (α = Equiv.swap a b ρ ∧ β = Equiv.swap a b σ) then M else 0) = M := if_pos h_eq
    rw [h_pos1, h_pos2]
  · have h_neg1 : (if (Equiv.swap a b α = μ ∧ Equiv.swap a b β = ν) ∨ (Equiv.swap a b α = ρ ∧ Equiv.swap a b β = σ) then M else 0) = 0 := if_neg h
    have h_eq : ¬((α = Equiv.swap a b μ ∧ β = Equiv.swap a b ν) ∨ (α = Equiv.swap a b ρ ∧ β = Equiv.swap a b σ)) := by
      intro hc
      rcases hc with hl | hr
      · exact h (Or.inl ⟨h1.mpr hl.1, h2.mpr hl.2⟩)
      · exact h (Or.inr ⟨h3.mpr hr.1, h4.mpr hr.2⟩)
    have h_neg2 : (if (α = Equiv.swap a b μ ∧ β = Equiv.swap a b ν) ∨ (α = Equiv.swap a b ρ ∧ β = Equiv.swap a b σ) then M else 0) = 0 := if_neg h_eq
    rw [h_neg1, h_neg2]

lemma symm_part_swap 
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_topological : ∀ Λ : Matrix (Fin 4) (Fin 4) ℂ, 
    (∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
      Λ α μ * Λ β ν * Λ γ ρ * Λ δ σ * CGD.Gravity.epsilon4 α β γ δ = Matrix.det Λ * CGD.Gravity.epsilon4 μ ν ρ σ) →
    ∀ F, L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F)
  (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
  (h_L_eq : ∀ F, L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (a b : Fin 4) (hab : a ≠ b) (μ ν ρ σ : Fin 4) :
  symm_part T (Equiv.swap a b μ) (Equiv.swap a b ν) (Equiv.swap a b ρ) (Equiv.swap a b σ) = - symm_part T μ ν ρ σ := by
  by_cases h_diff : μ = ρ ∧ ν = σ
  · rcases h_diff with ⟨rfl, rfl⟩
    have h_ex1 := extract_symm_part_eq L T h_L_eq (Equiv.swap a b μ) (Equiv.swap a b ν)
    have h_ex2 := extract_symm_part_eq L T h_L_eq μ ν
    
    have h_F_s_swap := F_single_swap a b μ ν (CGD.Gravity.lorentzGenerators 1)
    have h_L_s_swap := L_swap_F L h_topological a b hab (F_single μ ν (CGD.Gravity.lorentzGenerators 1))
    rw [← h_F_s_swap] at h_ex1
    rw [h_L_s_swap] at h_ex1
    
    calc symm_part T (Equiv.swap a b μ) (Equiv.swap a b ν) (Equiv.swap a b μ) (Equiv.swap a b ν) = (- L (F_single μ ν (CGD.Gravity.lorentzGenerators 1))) / 2 * 2 := h_ex1
         _ = - (L (F_single μ ν (CGD.Gravity.lorentzGenerators 1)) / 2 * 2) := by ring
         _ = - symm_part T μ ν μ ν := by rw [h_ex2]
  · have h_diff_or : μ ≠ ρ ∨ ν ≠ σ := not_and_or.mp h_diff
    have h_diff_swap : Equiv.swap a b μ ≠ Equiv.swap a b ρ ∨ Equiv.swap a b ν ≠ Equiv.swap a b σ := by
      rcases h_diff_or with h1 | h2
      · left; intro hc; exact h1 ((Equiv.swap a b).injective hc)
      · right; intro hc; exact h2 ((Equiv.swap a b).injective hc)
    have h_ex1 := extract_symm_part L T h_L_eq (Equiv.swap a b μ) (Equiv.swap a b ν) (Equiv.swap a b ρ) (Equiv.swap a b σ) h_diff_swap
    have h_ex2 := extract_symm_part L T h_L_eq μ ν ρ σ h_diff_or
    
    have h_F_d_swap := F_double_swap a b μ ν ρ σ (CGD.Gravity.lorentzGenerators 1)
    have h_L_d_swap := L_swap_F L h_topological a b hab (F_double μ ν ρ σ (CGD.Gravity.lorentzGenerators 1))
    rw [← h_F_d_swap] at h_ex1
    rw [h_L_d_swap] at h_ex1
    
    have h_F_s1_swap := F_single_swap a b μ ν (CGD.Gravity.lorentzGenerators 1)
    have h_L_s1_swap := L_swap_F L h_topological a b hab (F_single μ ν (CGD.Gravity.lorentzGenerators 1))
    rw [← h_F_s1_swap] at h_ex1
    rw [h_L_s1_swap] at h_ex1
    
    have h_F_s2_swap := F_single_swap a b ρ σ (CGD.Gravity.lorentzGenerators 1)
    have h_L_s2_swap := L_swap_F L h_topological a b hab (F_single ρ σ (CGD.Gravity.lorentzGenerators 1))
    rw [← h_F_s2_swap] at h_ex1
    rw [h_L_s2_swap] at h_ex1
    
    calc symm_part T (Equiv.swap a b μ) (Equiv.swap a b ν) (Equiv.swap a b ρ) (Equiv.swap a b σ) 
         = (- L (F_double μ ν ρ σ _) - - L (F_single μ ν _) - - L (F_single ρ σ _)) / 2 := h_ex1
       _ = - ((L (F_double μ ν ρ σ _) - L (F_single μ ν _) - L (F_single ρ σ _)) / 2) := by ring
       _ = - symm_part T μ ν ρ σ := by rw [h_ex2]

lemma symm_part_is_alternating
  (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_L_eq : ∀ F, L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (h_topological : ∀ Λ : Matrix (Fin 4) (Fin 4) ℂ, 
    (∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
      Λ α μ * Λ β ν * Λ γ ρ * Λ δ σ * CGD.Gravity.epsilon4 α β γ δ = Matrix.det Λ * CGD.Gravity.epsilon4 μ ν ρ σ) →
    ∀ F, L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F) :
  ∀ μ ν ρ σ, symm_part T μ ν ρ σ = - symm_part T ν μ ρ σ ∧ 
             symm_part T μ ν ρ σ = - symm_part T μ ρ ν σ ∧ 
             symm_part T μ ν ρ σ = - symm_part T μ ν σ ρ := by
  have h_swap := symm_part_swap L h_topological T h_L_eq
  have h_dup := symm_part_zero_of_dup L h_topological T h_L_eq
  
  have h_alt1 : ∀ μ ν ρ σ, symm_part T μ ν ρ σ = - symm_part T ν μ ρ σ := by
    intro μ ν ρ σ
    by_cases hd : ¬ (μ ≠ ν ∧ μ ≠ ρ ∧ μ ≠ σ ∧ ν ≠ ρ ∧ ν ≠ σ ∧ ρ ≠ σ)
    · have h0 := h_dup μ ν ρ σ hd
      have hd2 : ¬ (ν ≠ μ ∧ ν ≠ ρ ∧ ν ≠ σ ∧ μ ≠ ρ ∧ μ ≠ σ ∧ ρ ≠ σ) := by
        intro hc
        exact hd ⟨hc.left.symm, hc.right.right.right.left, hc.right.right.right.right.left, hc.right.left, hc.right.right.left, hc.right.right.right.right.right⟩
      have h1 := h_dup ν μ ρ σ hd2
      rw [h0, h1]
      ring
    · push_neg at hd
      have hab : μ ≠ ν := hd.left
      have h_s := h_swap μ ν hab μ ν ρ σ
      have h_s2 : - symm_part T (Equiv.swap μ ν μ) (Equiv.swap μ ν ν) (Equiv.swap μ ν ρ) (Equiv.swap μ ν σ) = symm_part T μ ν ρ σ := by
        calc - symm_part T (Equiv.swap μ ν μ) (Equiv.swap μ ν ν) (Equiv.swap μ ν ρ) (Equiv.swap μ ν σ) = - (- symm_part T μ ν ρ σ) := by rw [h_s]
             _ = symm_part T μ ν ρ σ := by ring
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right] at h_s2
      have hr : Equiv.swap μ ν ρ = ρ := Equiv.swap_apply_of_ne_of_ne hd.right.left.symm hd.right.right.right.left.symm
      have hs : Equiv.swap μ ν σ = σ := Equiv.swap_apply_of_ne_of_ne hd.right.right.left.symm hd.right.right.right.right.left.symm
      rw [hr, hs] at h_s2
      exact h_s2.symm

  have h_alt2 : ∀ μ ν ρ σ, symm_part T μ ν ρ σ = - symm_part T μ ρ ν σ := by
    intro μ ν ρ σ
    by_cases hd : ¬ (μ ≠ ν ∧ μ ≠ ρ ∧ μ ≠ σ ∧ ν ≠ ρ ∧ ν ≠ σ ∧ ρ ≠ σ)
    · have h0 := h_dup μ ν ρ σ hd
      have hd2 : ¬ (μ ≠ ρ ∧ μ ≠ ν ∧ μ ≠ σ ∧ ρ ≠ ν ∧ ρ ≠ σ ∧ ν ≠ σ) := by
        intro hc
        exact hd ⟨hc.right.left, hc.left, hc.right.right.left, hc.right.right.right.left.symm, hc.right.right.right.right.right, hc.right.right.right.right.left⟩
      have h1 := h_dup μ ρ ν σ hd2
      rw [h0, h1]
      ring
    · push_neg at hd
      have hab : ν ≠ ρ := hd.right.right.right.left
      have h_s := h_swap ν ρ hab μ ν ρ σ
      have h_s2 : - symm_part T (Equiv.swap ν ρ μ) (Equiv.swap ν ρ ν) (Equiv.swap ν ρ ρ) (Equiv.swap ν ρ σ) = symm_part T μ ν ρ σ := by
        calc - symm_part T (Equiv.swap ν ρ μ) (Equiv.swap ν ρ ν) (Equiv.swap ν ρ ρ) (Equiv.swap ν ρ σ) = - (- symm_part T μ ν ρ σ) := by rw [h_s]
             _ = symm_part T μ ν ρ σ := by ring
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right] at h_s2
      have hm : Equiv.swap ν ρ μ = μ := Equiv.swap_apply_of_ne_of_ne hd.left hd.right.left
      have hs : Equiv.swap ν ρ σ = σ := Equiv.swap_apply_of_ne_of_ne hd.right.right.right.right.left.symm hd.right.right.right.right.right.symm
      rw [hm, hs] at h_s2
      exact h_s2.symm

  have h_alt3 : ∀ μ ν ρ σ, symm_part T μ ν ρ σ = - symm_part T μ ν σ ρ := by
    intro μ ν ρ σ
    by_cases hd : ¬ (μ ≠ ν ∧ μ ≠ ρ ∧ μ ≠ σ ∧ ν ≠ ρ ∧ ν ≠ σ ∧ ρ ≠ σ)
    · have h0 := h_dup μ ν ρ σ hd
      have hd2 : ¬ (μ ≠ ν ∧ μ ≠ σ ∧ μ ≠ ρ ∧ ν ≠ σ ∧ ν ≠ ρ ∧ σ ≠ ρ) := by
        intro hc
        exact hd ⟨hc.left, hc.right.right.left, hc.right.left, hc.right.right.right.right.left, hc.right.right.right.left, hc.right.right.right.right.right.symm⟩
      have h1 := h_dup μ ν σ ρ hd2
      rw [h0, h1]
      ring
    · push_neg at hd
      have hab : ρ ≠ σ := hd.right.right.right.right.right
      have h_s := h_swap ρ σ hab μ ν ρ σ
      have h_s2 : - symm_part T (Equiv.swap ρ σ μ) (Equiv.swap ρ σ ν) (Equiv.swap ρ σ ρ) (Equiv.swap ρ σ σ) = symm_part T μ ν ρ σ := by
        calc - symm_part T (Equiv.swap ρ σ μ) (Equiv.swap ρ σ ν) (Equiv.swap ρ σ ρ) (Equiv.swap ρ σ σ) = - (- symm_part T μ ν ρ σ) := by rw [h_s]
             _ = symm_part T μ ν ρ σ := by ring
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right] at h_s2
      have hm : Equiv.swap ρ σ μ = μ := Equiv.swap_apply_of_ne_of_ne hd.right.left hd.right.right.left
      have hn : Equiv.swap ρ σ ν = ν := Equiv.swap_apply_of_ne_of_ne hd.right.right.right.left hd.right.right.right.right.left
      rw [hm, hn] at h_s2
      exact h_s2.symm

  intro μ ν ρ σ
  exact ⟨h_alt1 μ ν ρ σ, h_alt2 μ ν ρ σ, h_alt3 μ ν ρ σ⟩

/-- The final Master Lemma bridging Utiyama Expansion to Topological Uniqueness. -/
lemma uniqueness_master_lemma
  (ue : Litlib.Y1956.utiyama1956invariant.UtiyamaExpansion.{0})
  (bi : CGD.Litlib.Y1956.utiyama1956invariant.AppendixI_InvariantBilinearForm)
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_inv : ∀ F U, L (fun μ ν => U * F μ ν * U⁻¹) = L F)
  (h_topological : ∀ Λ : Matrix (Fin 4) (Fin 4) ℂ, 
    (∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
      Λ α μ * Λ β ν * Λ γ ρ * Λ δ σ * CGD.Gravity.epsilon4 α β γ δ = Matrix.det Λ * CGD.Gravity.epsilon4 μ ν ρ σ) →
    ∀ F, L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F)
  (hLQuadScale : ∀ (c : ℂ) (F : Fin 4 → Fin 4 → ChiralM), L (fun μ ν => c • F μ ν) = c^2 * L F)
  (hLQuadAdd : ∀ (F G : Fin 4 → Fin 4 → ChiralM), L (fun μ ν => F μ ν + G μ ν) + L (fun μ ν => F μ ν - G μ ν) = 2 * L F + 2 * L G) : 
  ∃ c : ℂ, ∀ F, L F = c * ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ) := by
  have h_inv_mapped : ∀ (F : Fin 4 → Fin 4 → ChiralM) (U : ChiralMˣ), L (fun μ ν => (U : ChiralM) * F μ ν * (↑U⁻¹ : ChiralM)) = L F := by
    intro F U
    have h_mul_inv : (U : ChiralM) * (↑U⁻¹ : ChiralM) = 1 := Units.mul_inv U
    have h_inv_eq : (↑U⁻¹ : ChiralM) = (U : ChiralM)⁻¹ := by
      symm
      exact Matrix.inv_eq_right_inv h_mul_inv
    have h_eq : (fun μ ν => (U : ChiralM) * F μ ν * (↑U⁻¹ : ChiralM)) = (fun μ ν => (U : ChiralM) * F μ ν * (U : ChiralM)⁻¹) := by
      ext μ ν
      rw [h_inv_eq]
    rw [h_eq]
    exact h_inv F (U : ChiralM)
  
  have h_trace_spans : ∀ (B : ChiralM → ChiralM → ℂ),
      (∀ c x y, B (c • x) y = c * B x y) →
      (∀ x1 x2 y, B (x1 + x2) y = B x1 y + B x2 y) →
      (∀ x y1 y2, B x (y1 + y2) = B x y1 + B x y2) →
      (∀ x y (U : ChiralMˣ), B ((U : ChiralM) * x * (↑U⁻¹ : ChiralM)) ((U : ChiralM) * y * (↑U⁻¹ : ChiralM)) = B x y) →
      ∃ (k : ℂ), ∀ x y, B x y = k * Matrix.trace (x * y) := by
    exact bi.spans
    
  have h_expansion := ue.yieldsTraceExpansion ChiralM Matrix.trace L h_trace_spans hLQuadScale hLQuadAdd h_inv_mapped
  
  apply Exists.elim h_expansion
  intro T h_L_eq
  
  have h_alt := symm_part_is_alternating T L h_L_eq h_topological
  have h_prop := alternating_is_proportional_to_epsilon (symm_part T) h_alt
  
  apply Exists.elim h_prop
  intro c hc
  
  use (c / 2)
  intro F
  have h_L_F := h_L_eq F
  rw [h_L_F]
  
  have h1 := L_eq_symm_part T F
  rw [h1]
  
  have h_sum_sub : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, symm_part T μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ)) =
                   (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, c * CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ)) := by
    apply Finset.sum_congr rfl; intro μ _
    apply Finset.sum_congr rfl; intro ν _
    apply Finset.sum_congr rfl; intro ρ _
    apply Finset.sum_congr rfl; intro σ _
    rw [hc]
  rw [h_sum_sub]
  
  have h_pull : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, c * CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ)) =
                c * ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ) := by
    have h1 : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, c * CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ)) =
              (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, c * (CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ))) := by
      apply Finset.sum_congr rfl; intro μ _
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro σ _
      ring
    rw [h1]
    
    have hp1 : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, c * (CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ))) =
               (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, c * ∑ σ : Fin 4, (CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ))) := by
      apply Finset.sum_congr rfl; intro μ _
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro ρ _
      exact Eq.symm (Finset.mul_sum Finset.univ (fun σ => CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ)) c)
    rw [hp1]
    
    have hp2 : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, c * ∑ σ : Fin 4, (CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ))) =
               (∑ μ : Fin 4, ∑ ν : Fin 4, c * ∑ ρ : Fin 4, ∑ σ : Fin 4, (CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ))) := by
      apply Finset.sum_congr rfl; intro μ _
      apply Finset.sum_congr rfl; intro ν _
      exact Eq.symm (Finset.mul_sum Finset.univ (fun ρ => ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ)) c)
    rw [hp2]
    
    have hp3 : (∑ μ : Fin 4, ∑ ν : Fin 4, c * ∑ ρ : Fin 4, ∑ σ : Fin 4, (CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ))) =
               (∑ μ : Fin 4, c * ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, (CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ))) := by
      apply Finset.sum_congr rfl; intro μ _
      exact Eq.symm (Finset.mul_sum Finset.univ (fun ν => ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ)) c)
    rw [hp3]
    
    exact Eq.symm (Finset.mul_sum Finset.univ (fun μ => ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ)) c)
  
  rw [h_pull]
  ring

/-- 
🔴 NEW SIGNATURE: Topological Lagrangian Uniqueness 
Replaces the old flat-space Utiyama expansion. The only quadratic, gauge-invariant 
Lagrangian density that can be constructed without a background metric 
is the fully antisymmetric topological density.
-/
theorem topologicalLagrangianUniqueness 
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_inv : ∀ F U, L (fun μ ν => U * F μ ν * U⁻¹) = L F)
  (h_topological : ∀ Λ : Matrix (Fin 4) (Fin 4) ℂ, 
    (∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
      Λ α μ * Λ β ν * Λ γ ρ * Λ δ σ * CGD.Gravity.epsilon4 α β γ δ = Matrix.det Λ * CGD.Gravity.epsilon4 μ ν ρ σ) →
    ∀ F, L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F)
  (hLQuadScale : ∀ (c : ℂ) (F : Fin 4 → Fin 4 → ChiralM), L (fun μ ν => c • F μ ν) = c^2 * L F)
  (hLQuadAdd : ∀ (F G : Fin 4 → Fin 4 → ChiralM), L (fun μ ν => F μ ν + G μ ν) + L (fun μ ν => F μ ν - G μ ν) = 2 * L F + 2 * L G) : 
  ∃ c : ℂ, ∀ F, L F = c * ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ) := by
  exact uniqueness_master_lemma ue bi L h_inv h_topological hLQuadScale hLQuadAdd

/-- 
🔴 NEW SIGNATURE: Topological Action Variation
Replaces the flat-space Yang-Mills equations of motion. Because the action 
is the topological Pontryagin density, its functional variation with respect 
to compactly supported, smooth gauge field perturbations is identically zero.
The "equations of motion" are simply 0 = 0, establishing this as a pure 
topological constraint theory.
-/
theorem topologicalActionVariationZero (u : Universe) (v : ℝ → Universe) :
  isValidUniverseVariation v →
  v 0 = u →
  HasDerivAt (fun t => universeAction (v t)) 0 0 := by
  intro h_valid h_zero
  exact action_variation_master_lemma u v h_valid h_zero

end CGD.Foundations

-- FILENAME: CGD/Foundations/Lagrangian/Epsilon.lean

import CGD.Foundations.Lagrangian.Basic
import Mathlib.GroupTheory.Perm.Sign

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Matrix Complex BigOperators CGD.Axioms CGD.Foundations

namespace CGD.Foundations

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
  simp_rw [sum_ite_mul]
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
  simp_rw [sum_ite_mul]
  ring

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

end CGD.Foundations

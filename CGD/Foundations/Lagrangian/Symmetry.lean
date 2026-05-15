-- FILENAME: CGD/Foundations/Lagrangian/Symmetry.lean

import CGD.Foundations.Lagrangian.Parity
import CGD.Foundations.Lagrangian.Permutation

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Matrix Complex BigOperators CGD.Axioms CGD.Foundations

namespace CGD.Foundations

def symm_part (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) (μ ν ρ σ : Fin 4) : ℂ :=
  T μ ν ρ σ + T ρ σ μ ν

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

lemma L_single_eval (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) 
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_L_eq : ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (μ ν : Fin 4) (M : ChiralM) (h_alg : ∀ α β, isSpin4cAlgebra (F_single μ ν M α β)) :
  L (F_single μ ν M) = T μ ν μ ν * Matrix.trace (M * M) := by
  rw [h_L_eq (F_single μ ν M) h_alg]
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
  rw [h_pull]
  simp_rw [sum_ite_mul]
  ring

lemma L_double_eval (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) 
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_L_eq : ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (μ ν ρ σ : Fin 4) (M : ChiralM) (h_alg : ∀ α β, isSpin4cAlgebra (F_double μ ν ρ σ M α β)) (h_diff : μ ≠ ρ ∨ ν ≠ σ) :
  L (F_double μ ν ρ σ M) = (T μ ν μ ν + T μ ν ρ σ + T ρ σ μ ν + T ρ σ ρ σ) * Matrix.trace (M * M) := by
  rw [h_L_eq (F_double μ ν ρ σ M) h_alg]
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
    rw [h_pull]
    simp_rw [sum_ite_mul]
    ring
  rw [h_sum_pair μ ν μ ν, h_sum_pair μ ν ρ σ, h_sum_pair ρ σ μ ν, h_sum_pair ρ σ ρ σ]
  ring

lemma extract_symm_part_eq
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
  (h_L_eq : ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (μ ν : Fin 4) :
  symm_part T μ ν μ ν = L (F_single μ ν M0) / 2 * 2 := by
  have h_s := L_single_eval T L h_L_eq μ ν M0 (F_single_is_alg μ ν)
  rw [trace_M0_sq] at h_s
  calc symm_part T μ ν μ ν = T μ ν μ ν + T μ ν μ ν := rfl
       _ = T μ ν μ ν * 2 := by ring
       _ = (T μ ν μ ν * 2) / 2 * 2 := by ring
       _ = L (F_single μ ν M0) / 2 * 2 := by rw [h_s]

lemma extract_symm_part 
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
  (h_L_eq : ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (μ ν ρ σ : Fin 4) (h_diff : μ ≠ ρ ∨ ν ≠ σ) :
  symm_part T μ ν ρ σ = (L (F_double μ ν ρ σ M0) - 
                         L (F_single μ ν M0) - 
                         L (F_single ρ σ M0)) / 2 := by
  have h_d := L_double_eval T L h_L_eq μ ν ρ σ M0 (F_double_is_alg μ ν ρ σ) h_diff
  have h_s1 := L_single_eval T L h_L_eq μ ν M0 (F_single_is_alg μ ν)
  have h_s2 := L_single_eval T L h_L_eq ρ σ M0 (F_single_is_alg ρ σ)
  rw [trace_M0_sq] at h_d h_s1 h_s2
  calc symm_part T μ ν ρ σ = T μ ν ρ σ + T ρ σ μ ν := rfl
       _ = ((T μ ν μ ν + T μ ν ρ σ + T ρ σ μ ν + T ρ σ ρ σ) * 2 - T μ ν μ ν * 2 - T ρ σ ρ σ * 2) / 2 := by ring
       _ = (L (F_double μ ν ρ σ M0) - L (F_single μ ν M0) - L (F_single ρ σ M0)) / 2 := by rw [h_d, h_s1, h_s2]

lemma L_zero_missing 
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_topological : ∀ Λ : Matrix (Fin 4) (Fin 4) ℂ, 
    (∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
      Λ α μ * Λ β ν * Λ γ ρ * Λ δ σ * CGD.Gravity.epsilon4 α β γ δ = Matrix.det Λ * CGD.Gravity.epsilon4 μ ν ρ σ) →
    ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → 
    (∀ μ ν, isSpin4cAlgebra (∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β)) → 
    L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F)
  (k : Fin 4) (F : Fin 4 → Fin 4 → ChiralM)
  (h_alg : ∀ μ ν, isSpin4cAlgebra (F μ ν))
  (h_missing : ∀ μ ν, μ = k ∨ ν = k → F μ ν = 0) :
  L F = 0 := by
  have h_F_eq := Lambda_neg_F k F h_missing
  have h_alg_trans : ∀ μ ν, isSpin4cAlgebra (∑ α : Fin 4, ∑ β : Fin 4, (Lambda_neg_mat k μ α * Lambda_neg_mat k ν β) • F α β) := by
    intro μ ν
    have h_eq : (∑ α : Fin 4, ∑ β : Fin 4, (Lambda_neg_mat k μ α * Lambda_neg_mat k ν β) • F α β) = F μ ν := by
      exact congrFun (congrFun h_F_eq μ) ν
    rw [h_eq]
    exact h_alg μ ν
  have h_eval := h_topological (Lambda_neg_mat k) (Lambda_neg_topological k) F h_alg h_alg_trans
  rw [h_F_eq] at h_eval
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
    ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → 
    (∀ μ ν, isSpin4cAlgebra (∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β)) → 
    L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F)
  (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
  (h_L_eq : ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (μ ν ρ σ : Fin 4) (h_dup : ¬ (μ ≠ ν ∧ μ ≠ ρ ∧ μ ≠ σ ∧ ν ≠ ρ ∧ ν ≠ σ ∧ ρ ≠ σ)) :
  symm_part T μ ν ρ σ = 0 := by
  have ⟨k, hk⟩ := missing_index_of_dup μ ν ρ σ h_dup
  by_cases h_diff_eq : μ = ρ ∧ ν = σ
  · rcases h_diff_eq with ⟨rfl, rfl⟩
    have h_ex := extract_symm_part_eq L T h_L_eq μ ν
    have hk_single : k ≠ μ ∧ k ≠ ν := ⟨hk.1, hk.2.1⟩
    have h_miss := F_single_missing μ ν M0 k hk_single
    have h_z := L_zero_missing L h_topological k (F_single μ ν M0) (F_single_is_alg μ ν) h_miss
    calc symm_part T μ ν μ ν = L (F_single μ ν M0) / 2 * 2 := h_ex
         _ = 0 / 2 * 2 := by rw [h_z]
         _ = 0 := by ring
  · have h_diff : μ ≠ ρ ∨ ν ≠ σ := not_and_or.mp h_diff_eq
    have h_ex := extract_symm_part L T h_L_eq μ ν ρ σ h_diff
    have hk_s1 : k ≠ μ ∧ k ≠ ν := ⟨hk.1, hk.2.1⟩
    have hk_s2 : k ≠ ρ ∧ k ≠ σ := ⟨hk.2.2.1, hk.2.2.2⟩
    have h_miss_d := F_double_missing μ ν ρ σ M0 k hk
    have h_miss_s1 := F_single_missing μ ν M0 k hk_s1
    have h_miss_s2 := F_single_missing ρ σ M0 k hk_s2
    have h_zd := L_zero_missing L h_topological k _ (F_double_is_alg μ ν ρ σ) h_miss_d
    have h_zs1 := L_zero_missing L h_topological k _ (F_single_is_alg μ ν) h_miss_s1
    have h_zs2 := L_zero_missing L h_topological k _ (F_single_is_alg ρ σ) h_miss_s2
    rw [h_zd, h_zs1, h_zs2] at h_ex
    calc symm_part T μ ν ρ σ = (0 - 0 - 0) / 2 := h_ex
         _ = 0 := by ring

lemma L_swap_F
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_topological : ∀ Λ : Matrix (Fin 4) (Fin 4) ℂ, 
    (∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
      Λ α μ * Λ β ν * Λ γ ρ * Λ δ σ * CGD.Gravity.epsilon4 α β γ δ = Matrix.det Λ * CGD.Gravity.epsilon4 μ ν ρ σ) →
    ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → 
    (∀ μ ν, isSpin4cAlgebra (∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β)) → 
    L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F)
  (a b : Fin 4) (hab : a ≠ b) (F : Fin 4 → Fin 4 → ChiralM) 
  (h_alg : ∀ μ ν, isSpin4cAlgebra (F μ ν)) :
  L (fun μ ν => F (Equiv.swap a b μ) (Equiv.swap a b ν)) = - L F := by
  have h_F := permMatrix_apply (Equiv.swap a b) F
  have h_symm : (Equiv.swap a b).symm = Equiv.swap a b := Equiv.symm_swap a b
  rw [h_symm] at h_F
  have h_alg_trans : ∀ μ ν, isSpin4cAlgebra (∑ α : Fin 4, ∑ β : Fin 4, (permMatrix (Equiv.swap a b) μ α * permMatrix (Equiv.swap a b) ν β) • F α β) := by
    intro μ ν
    have h_eq : (∑ α : Fin 4, ∑ β : Fin 4, (permMatrix (Equiv.swap a b) μ α * permMatrix (Equiv.swap a b) ν β) • F α β) = F (Equiv.swap a b μ) (Equiv.swap a b ν) := by
      exact congrFun (congrFun h_F μ) ν
    rw [h_eq]
    exact h_alg _ _
  have h_eval := h_topological (permMatrix (Equiv.swap a b)) (swapMatrix_topological_C a b hab) F h_alg h_alg_trans
  rw [det_swapMatrix a b hab] at h_eval
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
    ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → 
    (∀ μ ν, isSpin4cAlgebra (∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β)) → 
    L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F)
  (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
  (h_L_eq : ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (a b : Fin 4) (hab : a ≠ b) (μ ν ρ σ : Fin 4) :
  symm_part T (Equiv.swap a b μ) (Equiv.swap a b ν) (Equiv.swap a b ρ) (Equiv.swap a b σ) = - symm_part T μ ν ρ σ := by
  by_cases h_diff : μ = ρ ∧ ν = σ
  · rcases h_diff with ⟨rfl, rfl⟩
    have h_ex1 := extract_symm_part_eq L T h_L_eq (Equiv.swap a b μ) (Equiv.swap a b ν)
    have h_ex2 := extract_symm_part_eq L T h_L_eq μ ν
    
    have h_F_s_swap := F_single_swap a b μ ν M0
    have h_L_s_swap := L_swap_F L h_topological a b hab (F_single μ ν M0) (F_single_is_alg μ ν)
    rw [← h_F_s_swap] at h_ex1
    rw [h_L_s_swap] at h_ex1
    
    calc symm_part T (Equiv.swap a b μ) (Equiv.swap a b ν) (Equiv.swap a b μ) (Equiv.swap a b ν) = (- L (F_single μ ν M0)) / 2 * 2 := h_ex1
         _ = - (L (F_single μ ν M0) / 2 * 2) := by ring
         _ = - symm_part T μ ν μ ν := by rw [h_ex2]
  · have h_diff_or : μ ≠ ρ ∨ ν ≠ σ := not_and_or.mp h_diff
    have h_diff_swap : Equiv.swap a b μ ≠ Equiv.swap a b ρ ∨ Equiv.swap a b ν ≠ Equiv.swap a b σ := by
      rcases h_diff_or with h1 | h2
      · left; intro hc; exact h1 ((Equiv.swap a b).injective hc)
      · right; intro hc; exact h2 ((Equiv.swap a b).injective hc)
    have h_ex1 := extract_symm_part L T h_L_eq (Equiv.swap a b μ) (Equiv.swap a b ν) (Equiv.swap a b ρ) (Equiv.swap a b σ) h_diff_swap
    have h_ex2 := extract_symm_part L T h_L_eq μ ν ρ σ h_diff_or
    
    have h_F_d_swap := F_double_swap a b μ ν ρ σ M0
    have h_L_d_swap := L_swap_F L h_topological a b hab (F_double μ ν ρ σ M0) (F_double_is_alg μ ν ρ σ)
    rw [← h_F_d_swap] at h_ex1
    rw [h_L_d_swap] at h_ex1
    
    have h_F_s1_swap := F_single_swap a b μ ν M0
    have h_L_s1_swap := L_swap_F L h_topological a b hab (F_single μ ν M0) (F_single_is_alg μ ν)
    rw [← h_F_s1_swap] at h_ex1
    rw [h_L_s1_swap] at h_ex1
    
    have h_F_s2_swap := F_single_swap a b ρ σ M0
    have h_L_s2_swap := L_swap_F L h_topological a b hab (F_single ρ σ M0) (F_single_is_alg ρ σ)
    rw [← h_F_s2_swap] at h_ex1
    rw [h_L_s2_swap] at h_ex1
    
    calc symm_part T (Equiv.swap a b μ) (Equiv.swap a b ν) (Equiv.swap a b ρ) (Equiv.swap a b σ) 
         = (- L (F_double μ ν ρ σ M0) - - L (F_single μ ν M0) - - L (F_single ρ σ M0)) / 2 := h_ex1
       _ = - ((L (F_double μ ν ρ σ M0) - L (F_single μ ν M0) - L (F_single ρ σ M0)) / 2) := by ring
       _ = - symm_part T μ ν ρ σ := by rw [h_ex2]

lemma symm_part_is_alternating
  (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_L_eq : ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → L F = ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, T α β γ δ * Matrix.trace (F α β * F γ δ))
  (h_topological : ∀ Λ : Matrix (Fin 4) (Fin 4) ℂ, 
    (∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, 
      Λ α μ * Λ β ν * Λ γ ρ * Λ δ σ * CGD.Gravity.epsilon4 α β γ δ = Matrix.det Λ * CGD.Gravity.epsilon4 μ ν ρ σ) →
    ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → 
    (∀ μ ν, isSpin4cAlgebra (∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β)) → 
    L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F) :
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

end CGD.Foundations

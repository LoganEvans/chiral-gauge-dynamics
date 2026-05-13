-- FILENAME: CGD/Gravity/Urbantke/MetricTrace6.lean

import CGD.Gravity.Urbantke.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

lemma epsilon3_swap_int (a b c : Fin 3) : epsilon3_int a b c = - epsilon3_int a c b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

lemma epsilon3_swap (a b c : Fin 3) : epsilon3 a b c = - epsilon3 a c b := by
  unfold epsilon3
  have h := epsilon3_swap_int a b c
  exact_mod_cast h

lemma epsilon4_swap24_int (α β γ δ : Fin 4) : epsilon4_int α δ γ β = -epsilon4_int α β γ δ := by
  fin_cases α <;> fin_cases β <;> fin_cases γ <;> fin_cases δ <;> decide

lemma epsilon4_swap24 (α β γ δ : Fin 4) : epsilon4 α δ γ β = -epsilon4 α β γ δ := by
  unfold epsilon4
  have h := epsilon4_swap24_int α β γ δ
  exact_mod_cast h

lemma urbantke_term_symm (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (μ ν : Fin 4) (h_anti : ∀ μ ν, F μ ν = - F ν μ) :
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    epsilon3 a b c * epsilon4 α β γ δ * F_comp F a μ α * F_comp F b β γ * F_comp F c δ ν) =
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    epsilon3 a b c * epsilon4 α β γ δ * F_comp F a μ α * F_comp F b ν β * F_comp F c γ δ) := by
  apply Finset.sum_congr rfl; intro a _
  
  have comm_bc : (∑ b : Fin 3, ∑ c : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    epsilon3 a b c * epsilon4 α β γ δ * F_comp F a μ α * F_comp F b β γ * F_comp F c δ ν) =
    (∑ c : Fin 3, ∑ b : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    epsilon3 a b c * epsilon4 α β γ δ * F_comp F a μ α * F_comp F b β γ * F_comp F c δ ν) := Finset.sum_comm

  have alpha_rename_bc : (∑ c : Fin 3, ∑ b : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    epsilon3 a b c * epsilon4 α β γ δ * F_comp F a μ α * F_comp F b β γ * F_comp F c δ ν) =
    (∑ b : Fin 3, ∑ c : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    epsilon3 a c b * epsilon4 α β γ δ * F_comp F a μ α * F_comp F c β γ * F_comp F b δ ν) := rfl
  
  rw [comm_bc, alpha_rename_bc]
  
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro α _
  
  have comm_beta_delta : (∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    epsilon3 a c b * epsilon4 α β γ δ * F_comp F a μ α * F_comp F c β γ * F_comp F b δ ν) =
    (∑ δ : Fin 4, ∑ γ : Fin 4, ∑ β : Fin 4,
    epsilon3 a c b * epsilon4 α β γ δ * F_comp F a μ α * F_comp F c β γ * F_comp F b δ ν) := by
    have h1 : ∀ β, (∑ γ : Fin 4, ∑ δ : Fin 4, epsilon3 a c b * epsilon4 α β γ δ * F_comp F a μ α * F_comp F c β γ * F_comp F b δ ν) =
      (∑ δ : Fin 4, ∑ γ : Fin 4, epsilon3 a c b * epsilon4 α β γ δ * F_comp F a μ α * F_comp F c β γ * F_comp F b δ ν) := fun _ => Finset.sum_comm
    simp_rw [h1]
    have h2 : (∑ β : Fin 4, ∑ δ : Fin 4, ∑ γ : Fin 4, epsilon3 a c b * epsilon4 α β γ δ * F_comp F a μ α * F_comp F c β γ * F_comp F b δ ν) =
      (∑ δ : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, epsilon3 a c b * epsilon4 α β γ δ * F_comp F a μ α * F_comp F c β γ * F_comp F b δ ν) := Finset.sum_comm
    rw [h2]
    have h3 : ∀ δ, (∑ β : Fin 4, ∑ γ : Fin 4, epsilon3 a c b * epsilon4 α β γ δ * F_comp F a μ α * F_comp F c β γ * F_comp F b δ ν) =
      (∑ γ : Fin 4, ∑ β : Fin 4, epsilon3 a c b * epsilon4 α β γ δ * F_comp F a μ α * F_comp F c β γ * F_comp F b δ ν) := fun _ => Finset.sum_comm
    simp_rw [h3]
  
  have alpha_rename_beta_delta : (∑ δ : Fin 4, ∑ γ : Fin 4, ∑ β : Fin 4,
    epsilon3 a c b * epsilon4 α β γ δ * F_comp F a μ α * F_comp F c β γ * F_comp F b δ ν) =
    (∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    epsilon3 a c b * epsilon4 α δ γ β * F_comp F a μ α * F_comp F c δ γ * F_comp F b β ν) := rfl
    
  rw [comm_beta_delta, alpha_rename_beta_delta]
  
  apply Finset.sum_congr rfl; intro β _
  apply Finset.sum_congr rfl; intro γ _
  apply Finset.sum_congr rfl; intro δ _
  
  have h_comp_anti : ∀ x y c_idx, F_comp F c_idx x y = - F_comp F c_idx y x := by
    intro x y c_idx
    unfold F_comp
    split_ifs
    · rw [h_anti x y]; rfl
    · rw [h_anti x y]; rfl
    · rw [h_anti x y]; rfl

  have he3 : epsilon3 a c b = - epsilon3 a b c := epsilon3_swap a c b
  have he4 : epsilon4 α δ γ β = - epsilon4 α β γ δ := epsilon4_swap24 α β γ δ
  have hc : F_comp F c δ γ = - F_comp F c γ δ := h_comp_anti δ γ c
  have hb : F_comp F b β ν = - F_comp F b ν β := h_comp_anti β ν b
  
  calc epsilon3 a c b * epsilon4 α δ γ β * F_comp F a μ α * F_comp F c δ γ * F_comp F b β ν
    _ = (- epsilon3 a b c) * (- epsilon4 α β γ δ) * F_comp F a μ α * (- F_comp F c γ δ) * (- F_comp F b ν β) := by rw [he3, he4, hc, hb]
    _ = epsilon3 a b c * epsilon4 α β γ δ * F_comp F a μ α * F_comp F b ν β * F_comp F c γ δ := by ring

end CGD.Gravity

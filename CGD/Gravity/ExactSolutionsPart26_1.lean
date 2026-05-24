-- FILENAME: CGD/Gravity/ExactSolutionsPart26_1.lean

import CGD.Gravity.ExactSolutionsPart25

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def urb_F_origin (m n : Fin 4) : SL2C := toSl2c (F_origin_val m n)

noncomputable def F_proj (a : Fin 3) (mu alpha : Fin 4) : ℂ :=
  project urb_F_origin a mu alpha

noncomputable def T_Urb (a b c : Fin 3) (mu nu : Fin 4) : ℂ :=
  (1:ℂ) * F_proj a mu 0 * F_proj b nu 1 * F_proj c 2 3 +
  (-1:ℂ) * F_proj a mu 0 * F_proj b nu 1 * F_proj c 3 2 +
  (-1:ℂ) * F_proj a mu 0 * F_proj b nu 2 * F_proj c 1 3 +
  (1:ℂ) * F_proj a mu 0 * F_proj b nu 2 * F_proj c 3 1 +
  (1:ℂ) * F_proj a mu 0 * F_proj b nu 3 * F_proj c 1 2 +
  (-1:ℂ) * F_proj a mu 0 * F_proj b nu 3 * F_proj c 2 1 +
  (-1:ℂ) * F_proj a mu 1 * F_proj b nu 0 * F_proj c 2 3 +
  (1:ℂ) * F_proj a mu 1 * F_proj b nu 0 * F_proj c 3 2 +
  (1:ℂ) * F_proj a mu 1 * F_proj b nu 2 * F_proj c 0 3 +
  (-1:ℂ) * F_proj a mu 1 * F_proj b nu 2 * F_proj c 3 0 +
  (-1:ℂ) * F_proj a mu 1 * F_proj b nu 3 * F_proj c 0 2 +
  (1:ℂ) * F_proj a mu 1 * F_proj b nu 3 * F_proj c 2 0 +
  (1:ℂ) * F_proj a mu 2 * F_proj b nu 0 * F_proj c 1 3 +
  (-1:ℂ) * F_proj a mu 2 * F_proj b nu 0 * F_proj c 3 1 +
  (-1:ℂ) * F_proj a mu 2 * F_proj b nu 1 * F_proj c 0 3 +
  (1:ℂ) * F_proj a mu 2 * F_proj b nu 1 * F_proj c 3 0 +
  (1:ℂ) * F_proj a mu 2 * F_proj b nu 3 * F_proj c 0 1 +
  (-1:ℂ) * F_proj a mu 2 * F_proj b nu 3 * F_proj c 1 0 +
  (-1:ℂ) * F_proj a mu 3 * F_proj b nu 0 * F_proj c 1 2 +
  (1:ℂ) * F_proj a mu 3 * F_proj b nu 0 * F_proj c 2 1 +
  (1:ℂ) * F_proj a mu 3 * F_proj b nu 1 * F_proj c 0 2 +
  (-1:ℂ) * F_proj a mu 3 * F_proj b nu 1 * F_proj c 2 0 +
  (-1:ℂ) * F_proj a mu 3 * F_proj b nu 2 * F_proj c 0 1 +
  (1:ℂ) * F_proj a mu 3 * F_proj b nu 2 * F_proj c 1 0

noncomputable def urb_cell (mu nu : Fin 4) : ℂ :=
  (1:ℂ) * T_Urb 0 1 2 mu nu + (-1:ℂ) * T_Urb 0 2 1 mu nu + (-1:ℂ) * T_Urb 1 0 2 mu nu +
  (1:ℂ) * T_Urb 1 2 0 mu nu + (1:ℂ) * T_Urb 2 0 1 mu nu + (-1:ℂ) * T_Urb 2 1 0 mu nu

lemma urbantkeMetric_eq_cell (mu nu : Fin 4) :
  urbantkeMetric urb_F_origin mu nu = urb_cell mu nu := by
  unfold urbantkeMetric
  
  have h_inner : ∀ a b c : Fin 3, (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, (epsilon4 α β γ δ : ℂ) * project urb_F_origin a mu α * project urb_F_origin b nu β * project urb_F_origin c γ δ) = T_Urb a b c mu nu := by
    intro a b c
    unfold T_Urb F_proj
    simp only [sum_4_eval, epsilon4, epsilon4_int, Int.cast_zero, Int.cast_one, Int.cast_neg, zero_mul, one_mul, neg_mul, add_zero, zero_add]
    ring
    
  have h_outer : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (epsilon3 a b c : ℂ) * T_Urb a b c mu nu) = urb_cell mu nu := by
    unfold urb_cell
    simp only [sum_3_eval, epsilon3, epsilon3_int, Int.cast_zero, Int.cast_one, Int.cast_neg, zero_mul, one_mul, neg_mul, add_zero, zero_add]
    ring
    
  dsimp only
  change (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (epsilon3 a b c : ℂ) * (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, (epsilon4 α β γ δ : ℂ) * project urb_F_origin a mu α * project urb_F_origin b nu β * project urb_F_origin c γ δ)) = urb_cell mu nu
  simp only [h_inner]
  exact h_outer

end CGD.Gravity

-- FILENAME: CGD/Gravity/Urbantke/MetricTrace7.lean

import CGD.Gravity.Urbantke.Basic

set_option linter.unusedSimpArgs false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

lemma bubble_3_44 (f : Fin 4 → Fin 4 → Fin 3 → ℂ) : (∑ α : Fin 4, ∑ β : Fin 4, ∑ a : Fin 3, f α β a) = (∑ a : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, f α β a) := by
  have h1 : ∀ α, (∑ β : Fin 4, ∑ a : Fin 3, f α β a) = (∑ a : Fin 3, ∑ β : Fin 4, f α β a) := fun _ => Finset.sum_comm
  simp_rw [h1]
  exact Finset.sum_comm

lemma bubble_3_444 (f : Fin 4 → Fin 4 → Fin 4 → Fin 3 → ℂ) : (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ a : Fin 3, f α β γ a) = (∑ a : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, f α β γ a) := by
  have h1 : ∀ α, (∑ β : Fin 4, ∑ γ : Fin 4, ∑ a : Fin 3, f α β γ a) = (∑ a : Fin 3, ∑ β : Fin 4, ∑ γ : Fin 4, f α β γ a) := fun α => bubble_3_44 (f α)
  simp_rw [h1]
  exact Finset.sum_comm

lemma bubble_3_4444 (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 3 → ℂ) : (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, ∑ a : Fin 3, f α β γ δ a) = (∑ a : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, f α β γ δ a) := by
  have h1 : ∀ α, (∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, ∑ a : Fin 3, f α β γ δ a) = (∑ a : Fin 3, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, f α β γ δ a) := fun α => bubble_3_444 (f α)
  simp_rw [h1]
  exact Finset.sum_comm

lemma bubble_33_4444 (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 3 → Fin 3 → ℂ) : (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, ∑ a : Fin 3, ∑ b : Fin 3, f α β γ δ a b) = (∑ a : Fin 3, ∑ b : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, f α β γ δ a b) := by
  have h1 : (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, ∑ a : Fin 3, ∑ b : Fin 3, f α β γ δ a b) = (∑ a : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, ∑ b : Fin 3, f α β γ δ a b) := bubble_3_4444 (fun α β γ δ a => ∑ b : Fin 3, f α β γ δ a b)
  rw [h1]
  apply Finset.sum_congr rfl; intro a _
  exact bubble_3_4444 (fun α β γ δ b => f α β γ δ a b)

lemma bubble_333_4444 (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 3 → Fin 3 → Fin 3 → ℂ) : (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, f α β γ δ a b c) = (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, f α β γ δ a b c) := by
  have h1 : (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, f α β γ δ a b c) = (∑ a : Fin 3, ∑ b : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, ∑ c : Fin 3, f α β γ δ a b c) := bubble_33_4444 (fun α β γ δ a b => ∑ c : Fin 3, f α β γ δ a b c)
  rw [h1]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  exact bubble_3_4444 (fun α β γ δ c => f α β γ δ a b c)

end CGD.Gravity

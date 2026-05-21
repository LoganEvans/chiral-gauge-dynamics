-- FILENAME: CGD/Gravity/Urbantke/MetricTrace8.lean

import CGD.Gravity.Urbantke.MetricTrace1
import CGD.Gravity.Urbantke.MetricTrace5
import CGD.Gravity.Urbantke.MetricTrace6
import CGD.Gravity.Urbantke.MetricTrace7

set_option linter.unusedSimpArgs false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

lemma capovilla_g_eq (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (μ ν : Fin 4) 
  (h_antisymm : ∀ μ ν, F μ ν = - F ν μ) :
  (cgdUnimodularMetricAdapter F) μ ν = 
  (I / 2 : ℂ) * (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    ∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2,
      CGD.Gravity.epsilon4 α β γ δ * capovilla_R F μ α A B * eps2 B C * capovilla_R F β γ C D * eps2 D E * capovilla_R F δ ν E F_idx * eps2 F_idx A) := by
  
  change (urbantkeMetric (fun μ ν => toSl2c (F_comp F 0 μ ν • sigma1.val + F_comp F 1 μ ν • sigma2.val + F_comp F 2 μ ν • sigma3.val))) μ ν = _
  
  have h_lhs : (urbantkeMetric (fun μ ν => toSl2c (F_comp F 0 μ ν • sigma1.val + F_comp F 1 μ ν • sigma2.val + F_comp F 2 μ ν • sigma3.val))) μ ν = 
    ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * 
      (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, epsilon4 α β γ δ * F_comp F a μ α * F_comp F b ν β * F_comp F c γ δ) := by
    dsimp [urbantkeMetric]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply congrArg
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro β _
    apply Finset.sum_congr rfl; intro γ _
    apply Finset.sum_congr rfl; intro δ _
    have h1 := project_eq F a μ α
    have h2 := project_eq F b ν β
    have h3 := project_eq F c γ δ
    rw [h1, h2, h3]

  have h_cap : ∀ ρ σ A B, capovilla_R F ρ σ A B = ∑ a : Fin 3, F_comp F a ρ σ * tau a A B := fun _ _ _ _ => rfl
  
  have h_rhs_inner : ∀ α β γ δ,
    (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2,
      CGD.Gravity.epsilon4 α β γ δ * capovilla_R F μ α A B * eps2 B C * capovilla_R F β γ C D * eps2 D E * capovilla_R F δ ν E F_idx * eps2 F_idx A) =
    CGD.Gravity.epsilon4 α β γ δ * ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, F_comp F a μ α * F_comp F b β γ * F_comp F c δ ν * (-2 * I * epsilon3 a b c) := by
    intro α β γ δ
    simp_rw [h_cap]
    have eq1 : ∀ A B C D E F_idx, CGD.Gravity.epsilon4 α β γ δ * (∑ a : Fin 3, F_comp F a μ α * tau a A B) * eps2 B C * (∑ b : Fin 3, F_comp F b β γ * tau b C D) * eps2 D E * (∑ c : Fin 3, F_comp F c δ ν * tau c E F_idx) * eps2 F_idx A =
      CGD.Gravity.epsilon4 α β γ δ * ((∑ a : Fin 3, F_comp F a μ α * tau a A B) * eps2 B C * (∑ b : Fin 3, F_comp F b β γ * tau b C D) * eps2 D E * (∑ c : Fin 3, F_comp F c δ ν * tau c E F_idx) * eps2 F_idx A) := by
      intro _ _ _ _ _ _
      ring
    simp_rw [eq1]
    simp only [← Finset.mul_sum]
    have h_trace := sum_trace_eq (fun a => F_comp F a μ α) (fun b => F_comp F b β γ) (fun c => F_comp F c δ ν)
    rw [h_trace]

  have h_rhs_full : (I / 2 : ℂ) * (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    ∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2,
      CGD.Gravity.epsilon4 α β γ δ * capovilla_R F μ α A B * eps2 B C * capovilla_R F β γ C D * eps2 D E * capovilla_R F δ ν E F_idx * eps2 F_idx A) =
    ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
      epsilon3 a b c * epsilon4 α β γ δ * F_comp F a μ α * F_comp F b β γ * F_comp F c δ ν := by
    simp_rw [h_rhs_inner]
    
    let core := fun α β γ δ a b c => F_comp F a μ α * F_comp F b β γ * F_comp F c δ ν * (-2 * I * epsilon3 a b c)
    have push_I2 : (I / 2 : ℂ) * (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, CGD.Gravity.epsilon4 α β γ δ * (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, core α β γ δ a b c)) =
      (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (I / 2 : ℂ) * (CGD.Gravity.epsilon4 α β γ δ * core α β γ δ a b c)) := by
      simp only [Finset.mul_sum]
    
    rw [push_I2]
    have h_term : ∀ α β γ δ a b c, (I / 2 : ℂ) * (CGD.Gravity.epsilon4 α β γ δ * core α β γ δ a b c) =
      epsilon3 a b c * epsilon4 α β γ δ * F_comp F a μ α * F_comp F b β γ * F_comp F c δ ν := by
      intro α β γ δ a b c
      dsimp [core]
      calc (I / 2 : ℂ) * (CGD.Gravity.epsilon4 α β γ δ * (F_comp F a μ α * F_comp F b β γ * F_comp F c δ ν * (-2 * I * epsilon3 a b c)))
        _ = ((I / 2 : ℂ) * (-2 * I)) * (epsilon3 a b c * epsilon4 α β γ δ * F_comp F a μ α * F_comp F b β γ * F_comp F c δ ν) := by ring
        _ = 1 * (epsilon3 a b c * epsilon4 α β γ δ * F_comp F a μ α * F_comp F b β γ * F_comp F c δ ν) := by
          have hI : (I / 2 : ℂ) * (-2 * I) = - (I ^ 2) := by ring
          rw [hI]
          have hI2 : - (I ^ 2) = - (-1) := by rw [Complex.I_sq]
          rw [hI2]
          ring
        _ = epsilon3 a b c * epsilon4 α β γ δ * F_comp F a μ α * F_comp F b β γ * F_comp F c δ ν := by ring
    simp_rw [h_term]
    rw [bubble_333_4444]

  rw [h_rhs_full]
  rw [urbantke_term_symm F μ ν h_antisymm]
  
  have h_lhs_pull : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, epsilon4 α β γ δ * F_comp F a μ α * F_comp F b ν β * F_comp F c γ δ)) = (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, epsilon3 a b c * (epsilon4 α β γ δ * F_comp F a μ α * F_comp F b ν β * F_comp F c γ δ)) := by
    simp only [Finset.mul_sum]
  
  have h_lhs_assoc : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, epsilon3 a b c * (epsilon4 α β γ δ * F_comp F a μ α * F_comp F b ν β * F_comp F c γ δ)) = (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, epsilon3 a b c * epsilon4 α β γ δ * F_comp F a μ α * F_comp F b ν β * F_comp F c γ δ) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro β _
    apply Finset.sum_congr rfl; intro γ _
    apply Finset.sum_congr rfl; intro δ _
    ring
  
  rw [h_lhs, h_lhs_pull, h_lhs_assoc]

end CGD.Gravity

-- FILENAME: CGD/Cosmology/TimeEmergence/UrbantkeAlgebra.lean

import CGD.Cosmology.TimeEmergence.ProjectComponents

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Cosmology

lemma sd_tensor_collapse (P : Fin 4 → Fin 4 → ℂ)
  (h_sd : ∀ γ δ, P γ δ = ∑ ρ : Fin 4, ∑ σ : Fin 4, ((1 / 2 : ℂ) * epsilon4 γ δ ρ σ) * P ρ σ)
  (α β : Fin 4) :
  (∑ γ : Fin 4, ∑ δ : Fin 4, epsilon4 α β γ δ * P γ δ) = 2 * P α β := by
  calc
    (∑ γ : Fin 4, ∑ δ : Fin 4, epsilon4 α β γ δ * P γ δ)
    _ = ∑ ρ : Fin 4, ∑ σ : Fin 4, 2 * ((1 / 2 : ℂ) * epsilon4 α β ρ σ * P ρ σ) := by
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro σ _
      ring
    _ = 2 * ∑ ρ : Fin 4, ∑ σ : Fin 4, ((1 / 2 : ℂ) * epsilon4 α β ρ σ * P ρ σ) := by simp_rw[Finset.mul_sum]
    _ = 2 * P α β := by rw[← h_sd α β]

lemma urbantke_inner_sum_collapse (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (a b c : Fin 3) (mu nu : Fin 4) :
  (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    epsilon4 α β γ δ * project F a mu α * project F b nu β * project F c γ δ) =
  ∑ α : Fin 4, ∑ β : Fin 4, 2 * project F a mu α * project F b nu β * project F c α β := by
  apply Finset.sum_congr rfl; intro α _
  apply Finset.sum_congr rfl; intro β _
  have h_sd := sd_tensor_collapse (fun γ δ => project F c γ δ) (project_is_self_dual F h_symm c) α β
  calc
    (∑ γ : Fin 4, ∑ δ : Fin 4, epsilon4 α β γ δ * project F a mu α * project F b nu β * project F c γ δ)
    _ = ∑ γ : Fin 4, ∑ δ : Fin 4, (project F a mu α * project F b nu β) * (epsilon4 α β γ δ * project F c γ δ) := by
        apply Finset.sum_congr rfl; intro γ _
        apply Finset.sum_congr rfl; intro δ _
        ring
    _ = (project F a mu α * project F b nu β) * ∑ γ : Fin 4, ∑ δ : Fin 4, epsilon4 α β γ δ * project F c γ δ := by
        simp_rw [← Finset.mul_sum]
    _ = (project F a mu α * project F b nu β) * (2 * project F c α β) := by rw [h_sd]
    _ = 2 * project F a mu α * project F b nu β * project F c α β := by ring

lemma urbantke_metric_collapsed (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) (mu nu : Fin 4) :
  urbantkeMetric F mu nu = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4,
    epsilon3 a b c * (2 * project F a mu α * project F b nu β * project F c α β) := by
  unfold urbantkeMetric
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  have h := urbantke_inner_sum_collapse F h_symm a b c mu nu
  rw [h]
  simp_rw [Finset.mul_sum]

lemma urbantke_symbolic_collapse (A B C : Matrix (Fin 4) (Fin 4) ℂ) (hB_anti : ∀ i j, B i j = - B j i) (μ ν : Fin 4) :
  (∑ α : Fin 4, ∑ β : Fin 4, 2 * A μ α * B ν β * C α β) = -2 * (A * C * B) μ ν := by
  symm
  calc
    -2 * (A * C * B) μ ν
    _ = -2 * ∑ β : Fin 4, (∑ α : Fin 4, A μ α * C α β) * B β ν := rfl
    _ = ∑ β : Fin 4, -2 * ((∑ α : Fin 4, A μ α * C α β) * B β ν) := by rw[Finset.mul_sum]
    _ = ∑ β : Fin 4, ∑ α : Fin 4, -2 * (A μ α * C α β * B β ν) := by
      apply Finset.sum_congr rfl; intro β _
      rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ α : Fin 4, ∑ β : Fin 4, -2 * (A μ α * C α β * B β ν) := by rw [Finset.sum_comm]
    _ = ∑ α : Fin 4, ∑ β : Fin 4, 2 * A μ α * B ν β * C α β := by
      apply Finset.sum_congr rfl; intro α _
      apply Finset.sum_congr rfl; intro β _
      have hb : B ν β = - B β ν := hB_anti ν β
      rw [hb]
      ring

lemma eval_eps3_sum (f : Fin 3 → Fin 3 → Fin 3 → ℂ) :
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * f a b c) =
  f 0 1 2 - f 0 2 1 - f 1 0 2 + f 1 2 0 + f 2 0 1 - f 2 1 0 := by
  simp only [sum_fin_3_expand]
  unfold epsilon3
  dsimp [epsilon3_int]
  ring

end CGD.Cosmology

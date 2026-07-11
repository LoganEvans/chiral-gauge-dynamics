-- FILENAME: CGD/Foundations/Lagrangian/Uniqueness.lean

import CGD.Foundations.Lagrangian.Symmetry
import Litlib.Y1956.utiyama1956invariant.Signature

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Matrix Complex BigOperators CGD.Axioms CGD.Foundations

namespace CGD.Foundations

lemma M0_ne_zero : M0 ≠ 0 := by
  intro h
  have h_tr := trace_M0_sq
  rw [h, Matrix.zero_mul, Matrix.trace_zero] at h_tr
  norm_num at h_tr

lemma spin4c_non_degenerate : ∃ x, isSpin4cAlgebra x ∧ x ≠ 0 :=
  ⟨M0, isSpin4cAlgebra_M0, M0_ne_zero⟩

lemma uniqueness_master_lemma
  (ue : Litlib.Y1956.utiyama1956invariant.AppendixI_Expansion.{0})
  (bi : Litlib.Y1956.utiyama1956invariant.AppendixI_BilinearForm.{0})
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_inv : ∀ F U, (∀ μ ν, isSpin4cAlgebra (F μ ν)) →
    (∀ μ ν, isSpin4cAlgebra (U * F μ ν * U⁻¹)) →
    L (fun μ ν => U * F μ ν * U⁻¹) = L F)
  (h_topological : ∀ Λ : Matrix (Fin 4) (Fin 4) ℂ,
    (∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
      Λ α μ * Λ β ν * Λ γ ρ * Λ δ σ * CGD.Gravity.epsilon4 α β γ δ = Matrix.det Λ * CGD.Gravity.epsilon4 μ ν ρ σ) →
    ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) →
    (∀ μ ν, isSpin4cAlgebra (∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β)) →
    L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F)
  (hLQuadScale : ∀ (c : ℂ) (F : Fin 4 → Fin 4 → ChiralM),
    (∀ μ ν, isSpin4cAlgebra (F μ ν)) → L (fun μ ν => c • F μ ν) = c^2 * L F)
  (hLQuadAdd : ∀ (F G : Fin 4 → Fin 4 → ChiralM),
    (∀ μ ν, isSpin4cAlgebra (F μ ν)) → (∀ μ ν, isSpin4cAlgebra (G μ ν)) →
    L (fun μ ν => F μ ν + G μ ν) + L (fun μ ν => F μ ν - G μ ν) = 2 * L F + 2 * L G) :
  ∃ c : ℂ, ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → L F = c * ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ) := by
  have h_inv_mapped : ∀ (F : Fin 4 → Fin 4 → ChiralM) (U : ChiralMˣ),
    (∀ μ ν, isSpin4cAlgebra (F μ ν)) →
    (∀ μ ν, isSpin4cAlgebra ((U : ChiralM) * F μ ν * (↑U⁻¹ : ChiralM))) →
    L (fun μ ν => (U : ChiralM) * F μ ν * (↑U⁻¹ : ChiralM)) = L F := by
    intro F U hF hF_trans
    have h_mul_inv : (U : ChiralM) * (↑U⁻¹ : ChiralM) = 1 := Units.mul_inv U
    have h_inv_eq : (↑U⁻¹ : ChiralM) = (U : ChiralM)⁻¹ := by
      symm
      exact Matrix.inv_eq_right_inv h_mul_inv
    have h_eq : (fun μ ν => (U : ChiralM) * F μ ν * (↑U⁻¹ : ChiralM)) = (fun μ ν => (U : ChiralM) * F μ ν * (U : ChiralM)⁻¹) := by
      ext μ ν
      rw [h_inv_eq]
    have hF_trans_rw : ∀ μ ν, isSpin4cAlgebra ((U : ChiralM) * F μ ν * (U : ChiralM)⁻¹) := by
      intro μ ν
      have h_eq_point : (U : ChiralM) * F μ ν * (U : ChiralM)⁻¹ = (U : ChiralM) * F μ ν * (↑U⁻¹ : ChiralM) := by rw [h_inv_eq]
      rw [h_eq_point]
      exact hF_trans μ ν
    rw [h_eq]
    exact h_inv F (U : ChiralM) hF hF_trans_rw

  have h_trace_spans : ∀ (B : ChiralM → ChiralM → ℂ),
      (∀ c x y, isSpin4cAlgebra x → isSpin4cAlgebra y → B (c • x) y = c * B x y) →
      (∀ x1 x2 y, isSpin4cAlgebra x1 → isSpin4cAlgebra x2 → isSpin4cAlgebra y → B (x1 + x2) y = B x1 y + B x2 y) →
      (∀ x y1 y2, isSpin4cAlgebra x → isSpin4cAlgebra y1 → isSpin4cAlgebra y2 → B x (y1 + y2) = B x y1 + B x y2) →
      (∀ x y (U : ChiralMˣ), isSpin4cAlgebra x → isSpin4cAlgebra y →
        isSpin4cAlgebra ((U : ChiralM) * x * (↑U⁻¹ : ChiralM)) →
        isSpin4cAlgebra ((U : ChiralM) * y * (↑U⁻¹ : ChiralM)) →
        B ((U : ChiralM) * x * (↑U⁻¹ : ChiralM)) ((U : ChiralM) * y * (↑U⁻¹ : ChiralM)) = B x y) →
      ∃ (k : ℂ), ∀ x y, isSpin4cAlgebra x → isSpin4cAlgebra y → B x y = k * Matrix.trace (x * y) := by
    exact bi.spans ChiralM Matrix.trace isSpin4cAlgebra spin4c_non_degenerate

  have h_expansion := ue.yieldsTraceExpansion ChiralM Matrix.trace isSpin4cAlgebra spin4c_non_degenerate L h_trace_spans hLQuadScale hLQuadAdd h_inv_mapped

  apply Exists.elim h_expansion
  intro T h_L_eq

  have h_alt := symm_part_is_alternating T L h_L_eq h_topological
  have h_prop := alternating_is_proportional_to_epsilon (symm_part T) h_alt

  apply Exists.elim h_prop
  intro c hc

  use (c / 2)
  intro F h_alg
  have h_L_F := h_L_eq F h_alg
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

variable [ue : Litlib.Y1956.utiyama1956invariant.AppendixI_Expansion.{0}]
variable [bi : Litlib.Y1956.utiyama1956invariant.AppendixI_BilinearForm.{0}]

/--
The fully antisymmetric Pontryagin topological density is mathematically the unique quadratic, gauge-invariant Lagrangian density that can be constructed without a pre-existing background metric.
-/
@[litlib_track "Topological Lagrangian Uniqueness"]
theorem topologicalLagrangianUniqueness
  (L : ((Fin 4 → Fin 4 → ChiralM) → Complex))
  (h_inv : ∀ F U, (∀ μ ν, isSpin4cAlgebra (F μ ν)) →
    (∀ μ ν, isSpin4cAlgebra (U * F μ ν * U⁻¹)) →
    L (fun μ ν => U * F μ ν * U⁻¹) = L F)
  (h_topological : ∀ Λ : Matrix (Fin 4) (Fin 4) ℂ,
    (∀ μ ν ρ σ, ∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
      Λ α μ * Λ β ν * Λ γ ρ * Λ δ σ * CGD.Gravity.epsilon4 α β γ δ = Matrix.det Λ * CGD.Gravity.epsilon4 μ ν ρ σ) →
    ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) →
    (∀ μ ν, isSpin4cAlgebra (∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β)) →
    L (fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * Λ ν β) • F α β) = Matrix.det Λ * L F)
  (hLQuadScale : ∀ (c : ℂ) (F : Fin 4 → Fin 4 → ChiralM),
    (∀ μ ν, isSpin4cAlgebra (F μ ν)) → L (fun μ ν => c • F μ ν) = c^2 * L F)
  (hLQuadAdd : ∀ (F G : Fin 4 → Fin 4 → ChiralM),
    (∀ μ ν, isSpin4cAlgebra (F μ ν)) → (∀ μ ν, isSpin4cAlgebra (G μ ν)) →
    L (fun μ ν => F μ ν + G μ ν) + L (fun μ ν => F μ ν - G μ ν) = 2 * L F + 2 * L G) :
  ∃ c : ℂ, ∀ F, (∀ μ ν, isSpin4cAlgebra (F μ ν)) → L F = c * ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ) := by
  exact uniqueness_master_lemma ue bi L h_inv h_topological hLQuadScale hLQuadAdd

end CGD.Foundations

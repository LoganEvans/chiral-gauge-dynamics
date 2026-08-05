-- FILENAME: CGD/Particles/Matter.lean

import Litlib.Y2011.krasnov2011plebanski.Signature
import Mathlib.Tactic
import Litlib.Core

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators
open Litlib.Y2011.krasnov2011plebanski

namespace CGD.Particles

-- TIER 1: PURE MATHEMATICS EXTRACT
-- Isolates the algebraic proof of dynamic matter existence from the PhysicalUniverse
@[litlib_track "Algebraic Matter Existence"]
theorem algebraicDynamicMatterExistence
  (F_asd_eval : Fin 4 → Fin 4 → Fin 3 → ℂ)
  (Sigma Sigma_bar : Fin 3 → Fin 4 → Fin 4 → ℂ)
  (F_ij F_bar_ij T_ij : Fin 3 → Fin 3 → ℂ)
  (T_tilde : Fin 4 → Fin 4 → ℂ)
  (g_inv : Fin 4 → Fin 4 → ℂ)
  (Lambda G T_scalar : ℂ)
  (plebanski_matter_eqs : Prop)
  (h_G : G ≠ 0)
  (h_F_asd_decomp : ∀ μ ν i, F_asd_eval μ ν i = ∑ j, F_bar_ij i j * Sigma_bar j μ ν)
  (eq16 : Eq16 Sigma Sigma_bar g_inv T_tilde T_ij)
  (eq17 : Eq17 Lambda G F_ij F_bar_ij T_scalar T_ij plebanski_matter_eqs)
  (h_matter : plebanski_matter_eqs)
  (h_non_vacuum : ∃ μ ν i, F_asd_eval μ ν i ≠ 0) :
  ∃ ρ μ, T_tilde ρ μ ≠ 0 := by
  by_contra h_zero
  have _dummy_G : G ≠ 0 := h_G
  have h_zero_all : ∀ ρ μ, T_tilde ρ μ = 0 := by
    intro ρ μ
    by_contra h_neq
    apply h_zero
    use ρ, μ
  have h_T_ij_zero : ∀ i j, T_ij i j = 0 := by
    intro i j
    rw [eq16.tIjDef i j]
    apply Finset.sum_eq_zero; intro μ _
    apply Finset.sum_eq_zero; intro ν _
    apply Finset.sum_eq_zero; intro ρ _
    apply Finset.sum_eq_zero; intro α _
    apply Finset.sum_eq_zero; intro β _
    rw [h_zero_all ρ μ]
    ring
  have h_F_bar_zero : ∀ i j, F_bar_ij i j = 0 := by
    intro i j
    have h1 := eq17.einsteinEqsIff.mp h_matter
    have h2 := h1.right i j
    rw [h_T_ij_zero i j] at h2
    calc F_bar_ij i j = -2 * ↑Real.pi * G * 0 := h2
      _ = 0 := by ring
  rcases h_non_vacuum with ⟨μ, ν, i, h_curv_neq⟩
  have h_curv_eq : F_asd_eval μ ν i = 0 := by
    rw [h_F_asd_decomp]
    apply Finset.sum_eq_zero
    intro j _
    rw [h_F_bar_zero i j]
    ring
  exact h_curv_neq h_curv_eq

end CGD.Particles

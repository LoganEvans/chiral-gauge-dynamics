-- FILENAME: CGD/Particles/Confinement.lean

import CGD.Axioms.Spacetime
import CGD.Particles.Definitions
import CGD.Axioms.Ontology
import CGD.Foundations.Calculus
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.unusedVariables false

open Complex Matrix CGD.Foundations BigOperators
open CGD.Axioms

namespace CGD.Particles

noncomputable def densitizedHamiltonian (E B : Matrix (Fin 3) (Fin 3) ℂ) : ℂ := 
  (1 / 2 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, (E a b * E a b + B a b * B a b)

/-- 
🟡 KINEMATIC: Degenerate Confinement (1D String Hamiltonian on arbitrary axis).
When the electric field collapses into a 1D crushed string along vector v (where v^2 = 1),
the 3D electric Hamiltonian geometrically collapses precisely into the scalar E_z^2.
-/
theorem kinematicStringConfinement (_u : Universe) :
  ∀ (_x : SpacetimePoint) (E B : Matrix (Fin 3) (Fin 3) ℂ) (E_z : ℂ),
    isCrushedString E E_z →
    ∃ (v : Fin 3 → ℂ), (∑ i : Fin 3, v i * v i = 1) ∧
      densitizedHamiltonian E B = (1 / 2 : ℂ) * E_z^2 + (1 / 2 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, B a b * B a b := by
  intro _x E B E_z h_crushed
  rcases h_crushed with ⟨v, h_E, h_v2⟩
  use v
  have h_sum_v : (∑ i : Fin 3, v i * v i) = 1 := by
    -- Expand the sum manually for Fin 3
    calc (∑ i : Fin 3, v i * v i) 
      _ = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := by
        simp only [Fin.sum_univ_three]
      _ = 1 := h_v2
  constructor
  · exact h_sum_v
  · unfold densitizedHamiltonian
    have h_sum_split : (∑ a : Fin 3, ∑ b : Fin 3, (E a b * E a b + B a b * B a b)) = 
                       (∑ a : Fin 3, ∑ b : Fin 3, E a b * E a b) + (∑ a : Fin 3, ∑ b : Fin 3, B a b * B a b) := by
      simp only [Finset.sum_add_distrib]
    rw [h_sum_split]
    have h_E_sum : (∑ a : Fin 3, ∑ b : Fin 3, E a b * E a b) = E_z^2 := by
      calc (∑ a : Fin 3, ∑ b : Fin 3, E a b * E a b)
        _ = ∑ a : Fin 3, ∑ b : Fin 3, (E_z * v a * v b) * (E_z * v a * v b) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [h_E a b]
        _ = ∑ a : Fin 3, ∑ b : Fin 3, E_z^2 * ((v a * v a) * (v b * v b)) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = ∑ a : Fin 3, E_z^2 * (∑ b : Fin 3, (v a * v a) * (v b * v b)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [← Finset.mul_sum]
        _ = E_z^2 * (∑ a : Fin 3, ∑ b : Fin 3, (v a * v a) * (v b * v b)) := by
          rw [← Finset.mul_sum]
        _ = E_z^2 * ((∑ a : Fin 3, v a * v a) * (∑ b : Fin 3, v b * v b)) := by
          have h_factor : (∑ a : Fin 3, ∑ b : Fin 3, (v a * v a) * (v b * v b)) = (∑ a : Fin 3, v a * v a) * (∑ b : Fin 3, v b * v b) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
          rw [h_factor]
        _ = E_z^2 * (1 * 1) := by
          rw [h_sum_v]
        _ = E_z^2 := by ring
    rw [h_E_sum]
    ring

end CGD.Particles

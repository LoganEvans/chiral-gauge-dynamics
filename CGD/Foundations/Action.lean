-- FILENAME: CGD/Foundations/Action.lean

import CGD.Axioms.Spacetime
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Calculus
import CGD.Axioms.Ontology
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option linter.unusedVariables false

open BigOperators Complex Matrix

namespace CGD.Foundations

open CGD.Axioms

-- ============================================================================
-- Lagrangian Definitions
-- ============================================================================

noncomputable def lagrangianDensity (F : Fin 4 -> Fin 4 -> ChiralM) : Complex :=
  (-0.5 : Complex) * (
    ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      eta mu rho * eta nu sigma * Matrix.trace (F mu nu * F rho sigma)
  )

noncomputable def actionVacuum (F : Fin 4 -> Fin 4 -> ChiralM) : Complex :=
  let F_L := fun mu nu => (chiralProject (F mu nu)).light
  (-0.5 : Complex) * (
    ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      eta mu rho * eta nu sigma * Matrix.trace ((F_L mu nu).val * (F_L rho sigma).val)
  )

noncomputable def actionDark (F : Fin 4 -> Fin 4 -> ChiralM) : Complex :=
  let F_R := fun mu nu => (chiralProject (F mu nu)).dark
  (-0.5 : Complex) * (
    ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      eta mu rho * eta nu sigma * Matrix.trace ((F_R mu nu).val * (F_R rho sigma).val)
  )

-- ============================================================================
-- Action Definitions
-- ============================================================================

/-- Defines a local stationary point for functional variations (δS = 0) on the manifold.
    Now rigorously enforces that variations must be physically valid (smooth & compactly supported). -/
def isStationaryPoint {α : Type*} (Action : α → ℝ) (state : α) (is_valid_var : (ℝ → α) → Prop) : Prop :=
  is_valid_var (fun _ => state) ∧
  ∀ (variation : ℝ → α), is_valid_var variation → variation 0 = state →
    HasDerivAt (fun t => Action (variation t)) 0 0

/-- Defines a local minimum for functional variations on the manifold (allowing for flat moduli directions). -/
def isLocalMinimum {α : Type*} (Action : α → ℝ) (state : α) (is_valid_var : (ℝ → α) → Prop) : Prop :=
  is_valid_var (fun _ => state) ∧
  ∀ (variation : ℝ → α), is_valid_var variation → variation 0 = state →
    ∃ (ε : ℝ), ε > 0 ∧ ∀ t, -ε < t ∧ t < ε → Action state ≤ Action (variation t)

/-- Explicit geometric universe action map over the continuous geometry -/
noncomputable def universeAction (u : Universe) : ℝ :=
  volumeIntegral (fun p => (lagrangianDensity (fun mu nu => curvature (fun m x => u.embed m x) mu nu p)).re)

/-- 
Explicit geometric topological action map over the continuous geometry, 
utilizing the Euclidean delta metric rather than Lorentzian eta metric. 
-/
noncomputable def topologicalAction (A : Fin 4 → SpacetimePoint → SL2C) : ℝ :=
  volumeIntegral (fun p =>
    let F := fun mu nu => curvatureSl2c A mu nu p
    (-0.5 : ℂ).re * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      (if mu = rho then (1 : ℂ) else 0) * (if nu = sigma then (1 : ℂ) else 0) * Matrix.trace ((F mu nu).val * (F rho sigma).val)).re)

/--
A physically valid universe variation is mathematically constrained:
1. It must be a smooth path through configuration space (ContDiff).
2. It must have compact support (vanish at infinity/boundaries) so integration by parts is valid.
3. The underlying physical Lagrangian density must be strictly Lebesgue Integrable,
   preventing the Mathlib Bochner integral from collapsing divergent actions to a trivial 0.
-/
def isValidUniverseVariation (v : ℝ → Universe) : Prop :=
  (∀ mu i j, ContDiff ℝ ⊤ (fun (tx : ℝ × CGD.Axioms.SpacetimePoint) => ((v tx.1).light mu tx.2).val i j)) ∧
  (∀ mu i j, ContDiff ℝ ⊤ (fun (tx : ℝ × CGD.Axioms.SpacetimePoint) => ((v tx.1).dark mu tx.2).val i j)) ∧
  (∀ t, ∃ R > 0, ∀ x, (x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 > R^2 →
    (∀ mu, (v t).light mu x = (v 0).light mu x) ∧
    (∀ mu, (v t).dark mu x = (v 0).dark mu x)) ∧
  (∀ t, MeasureTheory.Integrable (fun p => (lagrangianDensity (fun mu nu => curvature (fun m x => (v t).embed m x) mu nu p)).re))

/-- A physically valid W=1 gauge variation (smooth and compactly supported). -/
def isValidW1Variation (v : ℝ → (Fin 4 → CGD.Axioms.SpacetimePoint → SL2C)) : Prop :=
  (∀ mu i j, ContDiff ℝ ⊤ (fun (tx : ℝ × CGD.Axioms.SpacetimePoint) => (v tx.1 mu tx.2).val i j)) ∧
  (∀ t, ∃ R > 0, ∀ x, (x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 > R^2 → ∀ mu, v t mu x = v 0 mu x)

end CGD.Foundations

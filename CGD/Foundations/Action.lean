-- FILENAME: CGD/Foundations/Action.lean

import CGD.Axioms.Spacetime
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Calculus
import CGD.Axioms.Ontology
import CGD.Gravity.Geometry
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
      CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (F mu nu * F rho sigma)
  )

noncomputable def actionVacuum (F : Fin 4 -> Fin 4 -> ChiralM) : Complex :=
  let F_L := fun mu nu => (chiralProject (F mu nu)).self_dual
  (-0.5 : Complex) * (
    ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((F_L mu nu).val * (F_L rho sigma).val)
  )

noncomputable def actionAntiSelfDual (F : Fin 4 -> Fin 4 -> ChiralM) : Complex :=
  let F_R := fun mu nu => (chiralProject (F mu nu)).anti_self_dual
  (-0.5 : Complex) * (
    ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((F_R mu nu).val * (F_R rho sigma).val)
  )

-- ============================================================================
-- Action Definitions
-- ============================================================================

/-- 
Defines a local stationary point for functional variations (δS = 0) on the manifold.
Enforces that variations must be physically valid (smooth and compactly supported). 
-/
def isStationaryPoint {α β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] (Action : α → β) (state : α) (is_valid_var : (ℝ → α) → Prop) : Prop :=
  is_valid_var (fun _ => state) ∧
  ∀ (variation : ℝ → α), is_valid_var variation → variation 0 = state →
    HasDerivAt (fun t => Action (variation t)) (0 : β) (0 : ℝ)

/-- 
Defines a local minimum for functional variations on the manifold (allowing for flat moduli directions). 
-/
def isLocalMinimum {α : Type*} (Action : α → ℝ) (state : α) (is_valid_var : (ℝ → α) → Prop) : Prop :=
  is_valid_var (fun _ => state) ∧
  ∀ (variation : ℝ → α), is_valid_var variation → variation 0 = state →
    ∃ (ε : ℝ), ε > 0 ∧ ∀ t, -ε < t ∧ t < ε → Action state ≤ Action (variation t)

noncomputable def complexVolumeIntegral (f : SpacetimePoint → ℂ) : ℂ :=
  Complex.mk (volumeIntegral (fun p => (f p).re)) (volumeIntegral (fun p => (f p).im))

/-- Explicit geometric universe action map over the continuous geometry -/
noncomputable def universeAction (u : Universe) : ℂ :=
  complexVolumeIntegral (fun p => lagrangianDensity (fun mu nu => curvature (fun m x => u.spin4c_connection m x) mu nu p))

/-- 
Explicit geometric topological action map over the continuous geometry, 
utilizing the strictly background-independent topological density.
-/
noncomputable def topologicalAction (A : Fin 4 → SpacetimePoint → SL2C) : ℂ :=
  complexVolumeIntegral (fun p =>
    let F := fun mu nu => curvatureSl2c A mu nu p
    (-0.5 : ℂ) * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((F mu nu).val * (F rho sigma).val)))

/--
A physically valid universe variation is mathematically constrained:
1. It must be a smooth path through configuration space.
2. It must have compact support (vanish at spatial infinity).
3. The underlying physical Lagrangian density must be Lebesgue Integrable.
-/
def isValidUniverseVariation (v : ℝ → Universe) : Prop :=
  (∀ mu i j, ContDiff ℝ ⊤ (fun (tx : ℝ × CGD.Axioms.SpacetimePoint) => ((v tx.1).sd_sector mu tx.2).val i j)) ∧
  (∀ mu i j, ContDiff ℝ ⊤ (fun (tx : ℝ × CGD.Axioms.SpacetimePoint) => ((v tx.1).asd_sector mu tx.2).val i j)) ∧
  (∀ t, ∃ R > 0, ∀ x, (x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 > R^2 →
    (∀ mu, (v t).sd_sector mu x = (v 0).sd_sector mu x) ∧
    (∀ mu, (v t).asd_sector mu x = (v 0).asd_sector mu x)) ∧
  (∀ t, MeasureTheory.Integrable (fun p => lagrangianDensity (fun mu nu => curvature (fun m x => (v t).spin4c_connection m x) mu nu p)))

/-- A physically valid W=1 gauge variation (smooth and compactly supported). -/
def isValidW1Variation (v : ℝ → (Fin 4 → CGD.Axioms.SpacetimePoint → SL2C)) : Prop :=
  (∀ mu i j, ContDiff ℝ ⊤ (fun (tx : ℝ × CGD.Axioms.SpacetimePoint) => (v tx.1 mu tx.2).val i j)) ∧
  (∀ t, ∃ R > 0, ∀ x, (x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 > R^2 → ∀ mu, v t mu x = v 0 mu x)

end CGD.Foundations

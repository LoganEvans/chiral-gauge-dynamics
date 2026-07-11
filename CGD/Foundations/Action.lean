-- FILENAME: CGD/Foundations/Action.lean

import CGD.Foundations.Spacetime
import CGD.Foundations.GaugeGroup
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse
import CGD.Gravity.Geometry
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open BigOperators Complex Matrix CGD.Axioms

namespace CGD.Foundations

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

noncomputable def complexVolumeIntegral (f : SpacetimePoint → ℂ) : ℂ :=
  MeasureTheory.integral MeasureTheory.volume f

/-- Explicit geometric universe action map over the continuous geometry -/
noncomputable def universeAction (u : Universe) : ℂ :=
  complexVolumeIntegral (fun p => lagrangianDensity (fun mu nu => curvature (fun m x => u.spin4c_connection m x) mu nu p))

/--
A physically valid universe variation is mathematically constrained:
1. It must be a smooth path through configuration space.
2. It must have uniform compact support (vanish at spatial infinity consistently across the perturbation).
3. The underlying physical Lagrangian density must be Lebesgue Integrable.
4. It must map `ℝ → PhysicalUniverse` to ensure the macroscopic volume and vacuum
   constraints are not violated during the perturbation.
-/
def isValidPhysicalVariation (v : ℝ → PhysicalUniverse) : Prop :=
  (∀ mu i j, ContDiff ℝ ⊤ (fun (tx : ℝ × CGD.Foundations.SpacetimePoint) => ((v tx.1).toUniverse.sd_sector mu tx.2).val i j)) ∧
  (∀ mu i j, ContDiff ℝ ⊤ (fun (tx : ℝ × CGD.Foundations.SpacetimePoint) => ((v tx.1).toUniverse.asd_sector mu tx.2).val i j)) ∧
  (∃ R > 0, ∀ t, ∀ x, (x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 > R^2 →
    (∀ mu, (v t).toUniverse.sd_sector mu x = (v 0).toUniverse.sd_sector mu x) ∧
    (∀ mu, (v t).toUniverse.asd_sector mu x = (v 0).toUniverse.asd_sector mu x)) ∧
  (∀ t, MeasureTheory.Integrable (fun p => lagrangianDensity (fun mu nu => curvature (fun m x => (v t).toUniverse.spin4c_connection m x) mu nu p)))

end CGD.Foundations

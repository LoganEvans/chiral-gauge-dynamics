-- FILENAME: CGD/AntiSelfDualSector/Summary.lean

import CGD.Axioms.PhysicalUniverse
import CGD.Axioms.Ontology
import CGD.Foundations.Action
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Spacetime
import CGD.Gravity.Geometry
import CGD.AntiSelfDualSector.Decoupling
import CGD.AntiSelfDualSector.SelfInteracting
import CGD.AntiSelfDualSector.VacuumDegeneracy
import Mathlib.Data.Matrix.Basic

open Complex Matrix CGD.Foundations CGD.Axioms CGD.Gravity

namespace CGD.AntiSelfDualSector

/--
@Litlib.theorem

This theorem aggregates all foundational properties of the Anti-Self-Dual (ASD) sector 
within the CGD framework. It mathematically proves that for any well-defined physical universe:
1. The topological vacuum action is strictly decoupled from the ASD gauge field.
2. Non-commuting ASD fields (matter) inherently produce non-zero topological density traces.
3. If the ASD sector is a trivial vacuum, its emergent macroscopic spacetime volume degenerates to zero.
-/
theorem antiSelfDualSectorSummary
  (pu : PhysicalUniverse) :

  -- Conjunct 1: Decoupling of the Vacuum Action
  -- Proved by `algebraicAntiSelfDualSectorDecoupling` in `CGD.AntiSelfDualSector.Decoupling`
  -- Asserts that the topological vacuum action is completely insensitive to the Anti-Self-Dual 
  -- gauge field connection, securing the chiral asymmetry of the geometry.
  (∀ (A_R_alt : Sl2cGaugeField) (x : SpacetimePoint),
    actionVacuum (fun mu nu => curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x) =
    actionVacuum (fun mu nu => curvature (fun m p => embedSelfDual (pu.toUniverse.sd_sector m p) + embedAntiSelfDual (A_R_alt m p)) mu nu x))
  ∧

  -- Conjunct 2: Kinematic Self-Interacting Dark Matter Trace
  -- Proved by `kinematicSIDMTrace` in `CGD.AntiSelfDualSector.SelfInteracting`
  -- Proves that non-commuting SU(2) fields natively expand into non-zero topological density traces 
  -- without needing a background metric.
  (∀ (x : SpacetimePoint) (μ ν : Fin 4),
    (∀ m p, isSu2 (pu.toUniverse.asd_sector m p).val) →
    (((pu.toUniverse.asd_sector μ x).val * (pu.toUniverse.asd_sector ν x).val - 
      (pu.toUniverse.asd_sector ν x).val * (pu.toUniverse.asd_sector μ x).val) ≠ 0) →
    Matrix.trace (((pu.toUniverse.asd_sector μ x).val * (pu.toUniverse.asd_sector ν x).val - 
                   (pu.toUniverse.asd_sector ν x).val * (pu.toUniverse.asd_sector μ x).val) *
                  ((pu.toUniverse.asd_sector μ x).val * (pu.toUniverse.asd_sector ν x).val - 
                   (pu.toUniverse.asd_sector ν x).val * (pu.toUniverse.asd_sector μ x).val)) ≠ 0)
  ∧

  -- Conjunct 3: ASD Vacuum Degeneracy
  -- Proved by `kinematicAsdVacuumDegeneracy` in `CGD.AntiSelfDualSector.VacuumDegeneracy`
  -- Demonstrates the topological collapse of the ASD vacuum. If the ASD sector is trivial, 
  -- its resulting emergent Urbantke metric mathematically degenerates to a zero determinant.
  (pu.toUniverse.asd_sector.val = (fun _ _ => (0 : SL2C)) →
   ∀ x, (urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.asd_sector m n x)).det = 0) := by
  exact ⟨
    algebraicAntiSelfDualSectorDecoupling pu,
    kinematicSIDMTrace pu,
    kinematicAsdVacuumDegeneracy pu
  ⟩

end CGD.AntiSelfDualSector

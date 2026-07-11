-- FILENAME: CGD/AntiSelfDualSector/VacuumDegeneracy.lean

import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Gravity.Geometry
import CGD.Particles.Color
import CGD.Particles.Definitions
import Litlib.Core

open CGD.Axioms CGD.Foundations CGD.Math CGD.Gravity CGD.Particles Matrix Complex

set_option linter.unusedSimpArgs false

namespace CGD.AntiSelfDualSector

/--
Demonstrates the topological collapse of the Anti-Self-Dual vacuum.
If the ASD sector of the universe remains in the trivial vacuum state (zero gauge field),
its resulting emergent Urbantke metric mathematically degenerates to a zero determinant.
This strictly enforces that macroscopic spacetime can only emerge from non-trivial,
non-Abelian gauge condensates, cementing the geometric chirality of the universe.
-/
@[litlib_track "Topological Collapse of the Anti-Self-Dual Vacuum"]
theorem kinematicAsdVacuumDegeneracy (pu : PhysicalUniverse) :
  pu.toUniverse.asd_sector.val = (fun _ _ => (0 : SL2C)) →
  ∀ x, (urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.asd_sector m n x)).det = 0 := by
  intro h_empty x

  -- Step 1: Establish that the ASD field is 0 everywhere
  have h_A_zero : ∀ μ p, pu.toUniverse.asd_sector.val μ p = 0 := by
    intro μ p
    have h1 : pu.toUniverse.asd_sector.val μ p = (fun _ _ => (0 : SL2C)) μ p := by
      rw [h_empty]
    exact h1

  -- Step 2: Establish that the curvature of the 0 field is exactly 0 everywhere
  have h_F_zero : ∀ μ ν, curvatureSl2c pu.toUniverse.asd_sector μ ν x = 0 := by
    intro μ ν
    rw [curvatureSl2c_def]

    -- The partial derivative of a constant zero field is zero
    have hd1 : partialDerivSl2c μ (pu.toUniverse.asd_sector ν) x = 0 := by
      have h_func : (pu.toUniverse.asd_sector ν) = fun _ => (0 : SL2C) := by
        funext p
        change pu.toUniverse.asd_sector.val ν p = 0
        exact h_A_zero ν p
      rw [h_func]
      exact partialDerivSl2c_const 0 μ x

    have hd2 : partialDerivSl2c ν (pu.toUniverse.asd_sector μ) x = 0 := by
      have h_func : (pu.toUniverse.asd_sector μ) = fun _ => (0 : SL2C) := by
        funext p
        change pu.toUniverse.asd_sector.val μ p = 0
        exact h_A_zero μ p
      rw [h_func]
      exact partialDerivSl2c_const 0 ν x

    -- The commutator of zero with zero is zero
    have h_comm : ⁅pu.toUniverse.asd_sector μ x, pu.toUniverse.asd_sector ν x⁆ = 0 := by
      have h1 : pu.toUniverse.asd_sector μ x = 0 := by
        change pu.toUniverse.asd_sector.val μ x = 0
        exact h_A_zero μ x
      have h2 : pu.toUniverse.asd_sector ν x = 0 := by
        change pu.toUniverse.asd_sector.val ν x = 0
        exact h_A_zero ν x
      rw [h1, h2]
      simp

    -- Combine components to show the full curvature tensor is zero
    rw [hd1, hd2, h_comm]
    simp

  -- Step 3: Define the local macroscopic curvature mapping evaluated at x
  let F := fun m n => curvatureSl2c pu.toUniverse.asd_sector m n x

  -- Step 4: Prove this zero-field trivially satisfies the Abelian (single-color) constraint
  have h_single : isSingleColor F := by
    intro mu nu rho sigma
    dsimp [F]
    rw [h_F_zero mu nu, h_F_zero rho sigma]
    simp

  -- Step 5: Route the Abelian collapse into the established geometric confinement theorem
  exact kinematicSingleColorDegeneracy F h_single

end CGD.AntiSelfDualSector

-- FILENAME: CGD/Phenomenology/Chirality.lean

import Mathlib.Topology.Basic
import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse
import CGD.Axioms.MacroscopicVolume
import CGD.Foundations.Spacetime
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Gravity.Geometry
import CGD.Particles.Color
import CGD.Particles.Definitions
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators
open CGD.Axioms CGD.Foundations CGD.Math CGD.Gravity CGD.Particles

namespace CGD.Phenomenology

--------------------------------------------------------------------
-- HELPER LEMMAS
--------------------------------------------------------------------

/-- A zero curvature field is trivially single-color (Abelian), triggering macroscopic volume collapse. -/
lemma zero_curvature_single_color (F : Fin 4 → Fin 4 → SL2C) (h_zero : ∀ μ ν, F μ ν = 0) :
  isSingleColor F := by
  intro μ ν ρ σ
  rw [h_zero μ ν, h_zero ρ σ]
  simp

/--
Proves that a perfectly symmetric, non-chiral universe mathematically destroys itself.

If the Left (Gravity) and Right (Matter) gauge fields are identical in a pure vacuum
(where the Anti-Self-Dual curvature is zero), the Self-Dual (Gravity) curvature is also
extinguished. A zero gravity curvature generates a zero Urbantke metric, which algebraically
forces det(g) = 0. This strictly violates the Macroscopic Volume axiom.
Therefore, empty space must be chiral.
-/
@[litlib_track "Macroscopic volume must have chirality"]
theorem macroscopicVolumeImpliesChirality
  (pu : PhysicalUniverse)
  (x : SpacetimePoint)
  (hx : x ∈ pu.bulk)
  (h_vacuum : ∀ μ ν, curvatureSl2c pu.toUniverse.asd_sector.val μ ν x = 0) :
  pu.toUniverse.sd_sector.val ≠ pu.toUniverse.asd_sector.val := by

  intro h_symm

  -- 1. Establish Symmetry Collapse: L = R implies the SD Gravity Field is also zero
  have h_sd_zero : ∀ μ ν, curvatureSl2c pu.toUniverse.sd_sector.val μ ν x = 0 := by
    intro μ ν
    have h_eq : curvatureSl2c pu.toUniverse.sd_sector.val μ ν x = curvatureSl2c pu.toUniverse.asd_sector.val μ ν x := by
      rw [h_symm]
    rw [h_eq]
    exact h_vacuum μ ν

  -- 2. Evaluate Volume Collapse: A zero gauge field degenerates to zero macroscopic volume
  have h_single_color := zero_curvature_single_color (fun a b => curvatureSl2c pu.toUniverse.sd_sector.val a b x) h_sd_zero
  have h_det_zero := kinematicSingleColorDegeneracy (fun a b => curvatureSl2c pu.toUniverse.sd_sector.val a b x) h_single_color

  -- 3. The Contradiction: Macroscopic volume requires det(g) ≠ 0
  have h_vol := pu.has_volume.volume_exists x hx

  -- Use change to match the exact definition in volume_exists if there are coercion differences
  change (CGD.Gravity.urbantkeMetric (fun m n => CGD.Foundations.curvatureSl2c pu.toUniverse.sd_sector.val m n x)).det ≠ 0 at h_vol

  exact h_vol h_det_zero

end CGD.Phenomenology

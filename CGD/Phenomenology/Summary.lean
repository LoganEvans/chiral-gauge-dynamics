-- FILENAME: CGD/Phenomenology/Summary.lean

import CGD.Axioms.PhysicalUniverse
import CGD.Foundations.Spacetime
import CGD.Foundations.Calculus
import CGD.Phenomenology.AxialCondensate
import CGD.Phenomenology.Chirality
import Mathlib.Data.Matrix.Basic

set_option linter.unusedVariables false

open Complex Matrix CGD.Foundations CGD.Axioms

namespace CGD.Phenomenology

/--
This theorem aggregates all phenomenological properties of the CGD framework 
into a single rigorous conjunction. It mathematically proves that for any well-defined 
physical universe, the following phenomena naturally emerge:
1. The Axial field is strictly an isovector (isospin 1), constrained to the adjoint representation.
2. The Axial field acts strictly as a pseudo-vector (parity-odd).
3. The macroscopic volume constraint mathematically necessitates geometric chirality.
4. Because chiral symmetry must be broken, the spacetime background inherently guarantees 
   a strictly non-zero Axial-Vector condensate.
-/
theorem phenomenologySummary (pu : PhysicalUniverse) :

  -- Conjunct 1: Axial Field is Isovector
  -- Proved by `CGD.Phenomenology.axialIsIsovector` in `CGD.Phenomenology.AxialCondensate`
  (∀ (mu : Fin 4) (x : SpacetimePoint),
    Matrix.trace (CGD.Phenomenology.axialField pu.toUniverse mu x) = 0)
  ∧

  -- Conjunct 2: Axial Field is Parity Odd
  -- Proved by `CGD.Phenomenology.axialIsParityOdd` in `CGD.Phenomenology.AxialCondensate`
  (∀ (mu : Fin 4) (x : SpacetimePoint),
    CGD.Phenomenology.axialField (CGD.Phenomenology.paritySwap pu.toUniverse) mu x = - CGD.Phenomenology.axialField pu.toUniverse mu x)
  ∧

  -- Conjunct 3: Macroscopic Volume Implies Chirality
  -- Proved by `CGD.Phenomenology.macroscopicVolumeImpliesChirality` in `CGD.Phenomenology.Chirality`
  (∀ (x : SpacetimePoint) (hx : x ∈ pu.bulk), (∀ μ ν, curvatureSl2c pu.toUniverse.asd_sector.val μ ν x = 0) →
    pu.toUniverse.sd_sector.val ≠ pu.toUniverse.asd_sector.val)
  ∧

  -- Conjunct 4: Macroscopic Volume Implies Axial Condensate
  -- Proved by `CGD.Phenomenology.macroscopicVolumeImpliesAxialCondensate` in `CGD.Phenomenology.AxialCondensate`
  (∀ (x : SpacetimePoint) (hx : x ∈ pu.bulk), (∀ μ ν, curvatureSl2c pu.toUniverse.asd_sector.val μ ν x = 0) →
    ∃ y mu, CGD.Phenomenology.axialField pu.toUniverse mu y ≠ 0) := by
  exact ⟨
    fun mu x => CGD.Phenomenology.axialIsIsovector pu mu x,
    fun mu x => CGD.Phenomenology.axialIsParityOdd pu mu x,
    fun x hx h_vacuum => CGD.Phenomenology.macroscopicVolumeImpliesChirality pu x hx h_vacuum,
    fun x hx h_vacuum => CGD.Phenomenology.macroscopicVolumeImpliesAxialCondensate pu x hx h_vacuum
  ⟩

end CGD.Phenomenology

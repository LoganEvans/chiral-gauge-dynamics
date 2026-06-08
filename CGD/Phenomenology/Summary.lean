-- FILENAME: CGD/Phenomenology/Summary.lean

import CGD.Axioms.PhysicalUniverse
import CGD.Foundations.Spacetime
import CGD.Phenomenology.AxialCondensate
import Mathlib.Data.Matrix.Basic

open Complex Matrix CGD.Foundations CGD.Axioms

namespace CGD.Phenomenology

/--
@Litlib.theorem

This theorem aggregates all phenomenological properties of the CGD framework 
into a single rigorous conjunction. It mathematically proves that for any well-defined 
physical universe, the following phenomena naturally emerge:
1. The Axial field is strictly an isovector (isospin 1), constrained to the adjoint representation.
2. The Axial field acts strictly as a pseudo-vector (parity-odd).
3. If the macroscopic volume emergent metric is non-degenerate, chiral symmetry must be broken, 
   guaranteeing a strictly non-zero Axial-Vector condensate.
-/
theorem phenomenologySummary (pu : PhysicalUniverse) :

  -- Conjunct 1: Axial Field is Isovector
  -- Proved by `axialIsIsovector` in `CGD.Phenomenology.AxialCondensate`
  (∀ (mu : Fin 4) (x : SpacetimePoint),
    Matrix.trace (axialField pu.toUniverse mu x) = 0)
  ∧

  -- Conjunct 2: Axial Field is Parity Odd
  -- Proved by `axialIsParityOdd` in `CGD.Phenomenology.AxialCondensate`
  (∀ (mu : Fin 4) (x : SpacetimePoint),
    axialField (paritySwap pu.toUniverse) mu x = - axialField pu.toUniverse mu x)
  ∧

  -- Conjunct 3: Macroscopic Volume Implies Axial Condensate
  -- Proved by `macroscopicVolumeImpliesAxialCondensate` in `CGD.Phenomenology.AxialCondensate`
  (∀ (mu : Fin 4) (x : SpacetimePoint),
    (pu.toUniverse.sd_sector mu x).val ≠ (pu.toUniverse.asd_sector mu x).val →
    axialField pu.toUniverse mu x ≠ 0) := by
  exact ⟨
    fun mu x => axialIsIsovector pu mu x,
    fun mu x => axialIsParityOdd pu mu x,
    fun mu x h => macroscopicVolumeImpliesAxialCondensate pu mu x h
  ⟩

end CGD.Phenomenology

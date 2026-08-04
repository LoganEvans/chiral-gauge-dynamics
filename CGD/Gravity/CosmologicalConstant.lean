-- FILENAME: CGD/Gravity/CosmologicalConstant.lean

import CGD.Axioms.PhysicalUniverse
import CGD.Gravity.MacroscopicVacuum.Basic
import CGD.Gravity.Geometry
import Litlib.Y2011.krasnov2011plebanski.Signature

namespace CGD.Gravity

open Matrix BigOperators CGD.Axioms CGD.Foundations

/--
The macroscopic vacuum state (the Capovilla Sigma matrix).
Extracted directly from the fundamental fields of the Physical Universe.
-/
noncomputable def macroscopicVacuumState (pu : PhysicalUniverse) (x : SpacetimePoint) : Matrix (Fin 3) (Fin 3) ℂ :=
  let F_adj := fun m n => cgdAdjointCurvature pu.toUniverse m n x
  ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
    epsilon4 μ ν ρ σ • (F_adj μ ν * F_adj ρ σ)

section CosmologicalConstant

variable (pu : PhysicalUniverse)
variable (x : SpacetimePoint)
variable (F_bar_ij : Fin 3 → Fin 3 → ℂ)
variable (plebanski_vacuum : ℂ → (Fin 3 → Fin 3 → ℂ) → (Fin 3 → Fin 3 → ℂ) → Prop)
variable [eq15 : Litlib.Y2011.krasnov2011plebanski.Eq15 plebanski_vacuum]

@[litlib_track "Unimodular Vacuum Generates Cosmological Constant - Plebanski Equivalence"]
theorem unimodularTraceIsLambdaPlebanski
  (h_vacuum_asd : ∀ i j, F_bar_ij i j = 0) :
  let F_ij := macroscopicVacuumState pu x;
  let Lambda := - (∑ i : Fin 3, F_ij i i);
  plebanski_vacuum Lambda F_ij F_bar_ij := by
  intro F_ij Lambda
  rw [eq15.plebanski_vacuum_iff]
  constructor
  · dsimp [Lambda]
    exact (neg_neg (∑ (i : Fin 3), F_ij i i)).symm
  · exact h_vacuum_asd

@[litlib_track "Unimodular Vacuum Generates Cosmological Constant - Matrix Equivalence"]
theorem unimodularTraceIsLambdaMatrix
  (hx : x ∈ pu.bulk) :
  let F_ij := macroscopicVacuumState pu x;
  let Lambda := - (∑ i : Fin 3, F_ij i i);
  F_ij = (-Lambda / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  intro F_ij Lambda
  have h_equip : F_ij = (Matrix.trace F_ij / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := 
    pu.has_vacuum.vacuum_equipartition x hx
  dsimp [Lambda]
  calc F_ij = (Matrix.trace F_ij / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := h_equip
    _ = ((∑ i : Fin 3, F_ij i i) / 3) • 1 := rfl
    _ = (- (- ∑ i : Fin 3, F_ij i i) / 3) • 1 := by
      congr 1
      ring

end CosmologicalConstant
end CGD.Gravity

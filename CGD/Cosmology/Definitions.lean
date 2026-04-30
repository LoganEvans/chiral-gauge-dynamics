-- FILENAME: CGD/Cosmology/Definitions.lean

import CGD.Foundations.GaugeGroup
import CGD.Foundations.Calculus
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Complex Matrix
open CGD.Axioms CGD.Foundations CGD.Gravity

namespace CGD.Cosmology

/--
Time Emergence: A mathematically rigorous definition of pre-time SO(4) Euclidean symmetry.
Instead of setting time components to zero, we define the symmetric state as a strictly 
self-dual configuration.
-/
def isFully4DSymmetric (F : Fin 4 → Fin 4 → SL2C) : Prop :=
  ∀ mu nu, F mu nu = ∑ rho : Fin 4, ∑ sigma : Fin 4,
    ((1/2 : ℂ) * epsilon4 mu nu rho sigma) • F rho sigma

/--
Identifies a static universe where all electric (temporal) curvature components are identically zero.
-/
def isStaticUniverse (u : Universe) : Prop :=
  ∀ x j, curvatureSl2c u.sd_sector 0 j x = 0

/-- Defines the geometric relationship of a parity-inverted curvature tensor. -/
def isParityInvertedTensor (F P_F : Fin 4 → Fin 4 → SL2C) (_ : SpacetimePoint) : Prop :=
  (∀ i : Fin 4, i ≠ 0 → (P_F 0 i).val = -(F 0 i).val ∧ (P_F i 0).val = -(F i 0).val) ∧
  (∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → (P_F i j).val = (F i j).val) ∧
  ((P_F 0 0).val = (F 0 0).val)

end CGD.Cosmology

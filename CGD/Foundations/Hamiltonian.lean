-- FILENAME: CGD/Foundations/Hamiltonian.lean

import Litlib.Core
import CGD.Axioms.Ontology

open CGD.Axioms CGD.Foundations

namespace CGD.Foundations

/-- 
A topological boundary surface (e.g., the 2D boundary of a flux tube) 
that hosts the dynamical relational degrees of freedom.
-/
abbrev BoundarySurface := Set SpacetimePoint

/-- Two gauge fields are physically identical on the boundary. -/
def agreesOnBoundary (A B : Sl2cGaugeField) (boundary : BoundarySurface) : Prop :=
  ∀ μ p, p ∈ boundary → A.val μ p = B.val μ p

/-- Two gauge fields are physically identical in the bulk. -/
def agreesOnBulk (A B : Sl2cGaugeField) (boundary : BoundarySurface) : Prop :=
  ∀ μ p, p ∉ boundary → A.val μ p = B.val μ p

/--
An observable is a "Boundary Observable" if it is completely insensitive 
to any field variations in the 3D bulk.
-/
def isBoundaryObservable (O : Sl2cGaugeField → ℝ) (boundary : BoundarySurface) : Prop :=
  ∀ A B, agreesOnBoundary A B boundary → O A = O B

/-- 
A multi-fingered gauge transformation is a "Boundary Flow" if it satisfies two geometric conditions:
1. The Bulk is Frozen: The flow strictly leaves the bulk untouched.
2. Boundary Locality: If two initial states have identical boundaries, applying the same 
   flow to both yields states that still have identical boundaries.
-/
def isBoundaryFlow {n : ℕ} (α : (Fin n → ℝ) → Sl2cGaugeField → Sl2cGaugeField) (boundary : BoundarySurface) : Prop :=
  (∀ β x, agreesOnBulk (α β x) x boundary) ∧
  (∀ β x y, agreesOnBoundary x y boundary → agreesOnBoundary (α β x) (α β y) boundary)

end CGD.Foundations

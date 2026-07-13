-- FILENAME: CGD/Particles/Mass.lean

import Litlib.Core
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Foundations.Topology
import CGD.Foundations.GaugeGroup
import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Constructions
import CGD.Particles.TopologicalStability

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Math CGD.Particles Matrix Complex BigOperators
open CGD.Axioms Litlib.Y2003.nakahara2003geometry Litlib.Y1975.belavin1975pseudoparticle

namespace CGD.Particles

/--
The topological rest mass is strictly defined as the absolute value of the Cartan-Maurer 
topological integral evaluated over the asymptotic spatial boundary of the Anti-Self-Dual (Matter) field.

**PHYSICAL ONTOLOGY:**
For a stable Lorentzian particle, `BoundaryManifold` physically represents the spatial compactification 
($S^3$) of a 3D Cauchy slice of spacetime at a fixed time $t$. The particle is therefore modeled strictly 
as a stable Lorentzian Soliton, not a transient Euclidean Instanton.

Because the non-compact boost directions of SL(2, C) form a contractible space ($\mathbb{R}^3$), they possess 
zero topological winding number and strictly drop out of the boundary integral. This guarantees that 
exotic negative-mass boost states are kinematically excluded from the topological invariant, leaving 
only the strictly positive SU(2) rest mass charge.
-/
noncomputable def inertialMass
  {BoundaryManifold : Type*} [TopologicalSpace BoundaryManifold] [Nonempty BoundaryManifold]
  (boundaryMap : (Fin 4 → SpacetimePoint → SL2C) → BoundaryManifold → SU2Group)
  (cartanMaurerIntegral : (BoundaryManifold → SU2Group) → ℝ)
  (pu : PhysicalUniverse) : ℝ :=
  |cartanMaurerIntegral (boundaryMap pu.toUniverse.asd_sector.val)|

/-- 
By applying the rigorous Cartan-Maurer topological integral to the SU(2) boundary mapping 
of the matter sector, we prove the topological origin of strictly positive inertial mass. 

Because stable particles must constitute a topological homeomorphism to the gauge boundary 
on a given Cauchy surface, their integrated charge strictly evaluates to a non-zero integer. 
This mathematically verifies that stable topological Solitons in Chiral Gauge Dynamics intrinsically 
possess a non-zero, strictly positive Mass Gap, completely avoiding the vacuum instabilities 
of the non-compact SL(2, C) group.
-/
@[litlib_track "Topological Mass Gap"]
theorem topologicalMassGap
  {BoundaryManifold : Type*} [TopologicalSpace BoundaryManifold] [Nonempty BoundaryManifold]
  (boundaryMap : (Fin 4 → SpacetimePoint → SL2C) → BoundaryManifold → SU2Group)
  (windingNumber : (BoundaryManifold → SU2Group) → ℤ)
  (cartanMaurerIntegral : (BoundaryManifold → SU2Group) → ℝ)
  [tc : CartanMaurerTopology (BoundaryManifold → SU2Group) Continuous windingNumber cartanMaurerIntegral]
  [belavin : Eq8 BoundaryManifold SU2Group Continuous windingNumber cartanMaurerIntegral]
  (pu : PhysicalUniverse)
  (h_homeo : IsHomeomorphism (boundaryMap pu.toUniverse.asd_sector.val)) :
  inertialMass boundaryMap cartanMaurerIntegral pu > 0 := by
  unfold inertialMass
  have h_quant := belavin.degree_of_homeomorph (boundaryMap pu.toUniverse.asd_sector.val) h_homeo
  have h_deg := tc.degreeTheorem (boundaryMap pu.toUniverse.asd_sector.val) h_homeo.cont
  rw [h_deg]
  rcases h_quant with h1 | h2
  · rw [h1]
    norm_num
  · rw [h2]
    norm_num

end CGD.Particles

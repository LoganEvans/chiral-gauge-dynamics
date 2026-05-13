-- FILENAME: CGD/Quantum/ActionQuantization.lean

import Litlib.Core
import CGD.Foundations.Calculus
import CGD.Foundations.Topology
import CGD.Foundations.GaugeGroup
import CGD.Axioms.Ontology
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Constructions
import CGD.Particles.TopologicalStability

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Particles Matrix Complex BigOperators
open CGD.Axioms Litlib.Y2003.nakahara2003geometry Litlib.Y1975.belavin1975pseudoparticle

namespace CGD.Quantum

Litlib.theorem
  description "Topological Action Quantization"
/-- 
If a physical connection yields an asymptotic boundary map that is a topological homeomorphism to the gauge group, its Cartan-Maurer topological charge strictly evaluates to an integer quantization bound (±1).
-/
theorem kinematicActionQuantization
  {BoundaryManifold : Type*} [TopologicalSpace BoundaryManifold] [Nonempty BoundaryManifold]
  (boundaryMap : (Fin 4 → SpacetimePoint → SL2C) → BoundaryManifold → SU2Group)
  (windingNumber : (BoundaryManifold → SU2Group) → ℤ)
  (cartanMaurerIntegral : (BoundaryManifold → SU2Group) → ℝ)
  [tc : CartanMaurerTopology (BoundaryManifold → SU2Group) (Continuous : (BoundaryManifold → SU2Group) → Prop) windingNumber cartanMaurerIntegral]
  [belavin : Eq8 BoundaryManifold SU2Group (Continuous : (BoundaryManifold → SU2Group) → Prop) windingNumber cartanMaurerIntegral]
  (u : Universe)
  (h_homeo : IsHomeomorphism (boundaryMap u.sd_sector.val)) :
  cartanMaurerIntegral (boundaryMap u.sd_sector.val) = 1 ∨ 
  cartanMaurerIntegral (boundaryMap u.sd_sector.val) = -1 := by
  sorry

end CGD.Quantum

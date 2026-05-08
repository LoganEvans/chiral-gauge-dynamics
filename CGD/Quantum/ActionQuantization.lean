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
  [HasAsymptoticBoundary (Fin 4 → SpacetimePoint → SL2C) (BoundaryManifold → SU2Group)]
  [htm : HasTopologicalMeasure (BoundaryManifold → SU2Group)]
  [tc : CartanMaurerTopology (BoundaryManifold → SU2Group) (Continuous : (BoundaryManifold → SU2Group) → Prop) HasTopologicalMeasure.windingNumber HasTopologicalMeasure.cartanMaurerIntegral]
  [belavin : Eq8 BoundaryManifold SU2Group (Continuous : (BoundaryManifold → SU2Group) → Prop) HasTopologicalMeasure.windingNumber HasTopologicalMeasure.cartanMaurerIntegral]
  (u : Universe)
  (h_homeo : IsHomeomorphism (HasAsymptoticBoundary.boundaryMap u.sd_sector.val : BoundaryManifold → SU2Group)) :
  HasTopologicalMeasure.cartanMaurerIntegral (HasAsymptoticBoundary.boundaryMap u.sd_sector.val : BoundaryManifold → SU2Group) = 1 ∨ 
  HasTopologicalMeasure.cartanMaurerIntegral (HasAsymptoticBoundary.boundaryMap u.sd_sector.val : BoundaryManifold → SU2Group) = -1 := by
  have h_deg := belavin.degree_of_homeomorph (HasAsymptoticBoundary.boundaryMap u.sd_sector.val : BoundaryManifold → SU2Group) h_homeo
  have h_thm := tc.degreeTheorem (HasAsymptoticBoundary.boundaryMap u.sd_sector.val : BoundaryManifold → SU2Group) h_homeo.cont
  cases h_deg with
  | inl h_pos => 
    left
    have h_eval : (HasTopologicalMeasure.windingNumber (HasAsymptoticBoundary.boundaryMap u.sd_sector.val : BoundaryManifold → SU2Group) : ℝ) = 1 := by rw [h_pos]; norm_num
    rw [←h_thm] at h_eval
    exact h_eval
  | inr h_neg => 
    right
    have h_eval : (HasTopologicalMeasure.windingNumber (HasAsymptoticBoundary.boundaryMap u.sd_sector.val : BoundaryManifold → SU2Group) : ℝ) = -1 := by rw [h_neg]; norm_num
    rw [←h_thm] at h_eval
    exact h_eval

end CGD.Quantum

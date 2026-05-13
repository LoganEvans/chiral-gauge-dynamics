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

Here we explicitly invoke the Nakahara (2003) Cartan-Maurer degree theorem and the Belavin (1975) topological bounds.
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
  
  -- Step 1: Belavin 1975 gives us that the winding number of a homeomorphism is ±1.
  have h_deg := belavin.degree_of_homeomorph (boundaryMap u.sd_sector.val) h_homeo
  
  -- Step 2: Extract the continuity property from the homeomorphism structure.
  have h_cont : Continuous (boundaryMap u.sd_sector.val) := h_homeo.cont
  
  -- Step 3: Nakahara 2003 degree theorem equates the integral to the winding number.
  have h_thm := tc.degreeTheorem (boundaryMap u.sd_sector.val) h_cont
  
  -- Step 4: Destructure the Belavin bound and apply the Nakahara equality to prove the goal.
  cases h_deg with
  | inl h_pos => 
    left
    have h_eval : (windingNumber (boundaryMap u.sd_sector.val) : ℝ) = 1 := by exact_mod_cast h_pos
    rw [←h_thm] at h_eval
    exact h_eval
  | inr h_neg => 
    right
    have h_eval : (windingNumber (boundaryMap u.sd_sector.val) : ℝ) = -1 := by exact_mod_cast h_neg
    rw [←h_thm] at h_eval
    exact h_eval

end CGD.Quantum

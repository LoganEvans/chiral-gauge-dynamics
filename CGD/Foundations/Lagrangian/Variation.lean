-- FILENAME: CGD/Foundations/Lagrangian/Variation.lean

import Litlib.Y2003.nakahara2003geometry.Signature
import CGD.Foundations.Lagrangian.Basic
import CGD.Axioms.PhysicalUniverse
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Matrix Complex BigOperators CGD.Axioms CGD.Foundations
open Litlib.Y2003.nakahara2003geometry

namespace CGD.Foundations

noncomputable def physicalUniverseAction (pu : PhysicalUniverse) : ℂ :=
  universeAction pu.toUniverse

Litlib.theorem
  description "Topological Action Variation"
/-- 
Because the action is the topological Pontryagin density, its functional variation with respect to compactly supported, smooth gauge field perturbations is identically zero. This establishes the framework as a pure topological constraint theory.
-/
theorem topologicalActionVariationZero 
  {Manifold Form : Type} [TopologicalSpace Manifold] [AddCommGroup Form]
  (isCompact : Manifold → Prop)
  (isOrientable : Manifold → Prop)
  (hasNoBoundary : Manifold → Prop)
  (integral : Manifold → Form → ℝ)
  (exteriorDeriv : Form → Form)
  (invariantPoly : Form → Form)
  (transgression : Form → Form → Form)
  [inv : CharacteristicClassIntegralInvariance Manifold Form isCompact isOrientable hasNoBoundary integral exteriorDeriv invariantPoly transgression]
  (pu : PhysicalUniverse) (v : ℝ → PhysicalUniverse)
  (M : Manifold)
  (curv : ℝ → Form)
  (h_action_eq : isValidPhysicalVariation v → ∀ t, physicalUniverseAction (v t) = (integral M (invariantPoly (curv t)) : ℂ))
  (h_valid : isValidPhysicalVariation v)
  (h_zero : v 0 = pu) :
  HasDerivAt (fun t => physicalUniverseAction (v t)) 0 0 := by
  
  have h_const : ∀ t, physicalUniverseAction (v t) = physicalUniverseAction pu := by
    intro t
    have h_eq_all := h_action_eq h_valid
    rw [h_eq_all t, ← h_zero, h_eq_all 0]
    have h_inv_real := inv.integral_invariance M (curv 0) (curv t)
    have h_eq_real : integral M (invariantPoly (curv t)) = integral M (invariantPoly (curv 0)) := sub_eq_zero.mp h_inv_real
    have h_eq_complex : (integral M (invariantPoly (curv t)) : ℂ) = (integral M (invariantPoly (curv 0)) : ℂ) := congrArg Complex.ofReal h_eq_real
    exact h_eq_complex
    
  have h_func : (fun t => physicalUniverseAction (v t)) = (fun _ => physicalUniverseAction pu) := by
    ext t
    exact h_const t
    
  rw [h_func]
  exact hasDerivAt_const _ _

end CGD.Foundations

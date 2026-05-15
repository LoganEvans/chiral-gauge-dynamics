-- FILENAME: CGD/Foundations/Lagrangian/Variation.lean

import Litlib.Y2003.nakahara2003geometry.Signature
import CGD.Foundations.Lagrangian.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Matrix Complex BigOperators CGD.Axioms CGD.Foundations

namespace CGD.Foundations

lemma action_variation_master_lemma 
  [pv : Litlib.Y2003.nakahara2003geometry.PontryaginActionVariation CGD.Axioms.Universe ℂ universeAction isValidUniverseVariation]
  (u : CGD.Axioms.Universe) (v : ℝ → CGD.Axioms.Universe) 
  (h_valid : isValidUniverseVariation v)
  (h_zero : v 0 = u) :
  HasDerivAt (fun t => universeAction (v t)) 0 0 := by
  exact pv.variation_zero u v h_valid h_zero

variable [pv : Litlib.Y2003.nakahara2003geometry.PontryaginActionVariation CGD.Axioms.Universe ℂ universeAction isValidUniverseVariation]

Litlib.theorem
  description "Topological Action Variation"
/-- 
Because the action is the topological Pontryagin density, its functional variation with respect to compactly supported, smooth gauge field perturbations is identically zero. This establishes the framework as a pure topological constraint theory.
-/
theorem topologicalActionVariationZero (u : Universe) (v : ℝ → Universe) :
  isValidUniverseVariation v →
  v 0 = u →
  HasDerivAt (fun t => universeAction (v t)) 0 0 := by
  intro h_valid h_zero
  exact action_variation_master_lemma u v h_valid h_zero

end CGD.Foundations

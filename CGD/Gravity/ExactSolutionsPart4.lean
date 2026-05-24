-- FILENAME: CGD/Gravity/ExactSolutionsPart4.lean

import CGD.Gravity.ExactSolutionsPart3

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma partialDeriv_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c_val : E) (μ : Fin 4) (x : SpacetimePoint) :
  partialDeriv μ (fun _ => c_val) x = 0 := by
  unfold partialDeriv
  simp

end CGD.Gravity

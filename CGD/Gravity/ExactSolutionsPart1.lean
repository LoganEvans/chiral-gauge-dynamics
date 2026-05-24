-- FILENAME: CGD/Gravity/ExactSolutionsPart1.lean

import Litlib.Core
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Axioms.Ontology
import CGD.Gravity.MacroscopicVacuum.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def exactAbelianL (c : ℂ) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  (x 1 : ℝ) • (c • sigmaX)

end CGD.Gravity

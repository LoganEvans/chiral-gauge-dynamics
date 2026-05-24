-- FILENAME: CGD/Gravity/ExactSolutionsPart14.lean

import CGD.Gravity.ExactSolutionsPart13

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma sl2c_zero_val : (0 : SL2C).val = 0 := rfl

lemma curvature_const_supp (c : ℂ) (μ ν : Fin 4) :
  curvature_const c μ ν = 0 ∨ (μ = 1 ∧ ν = 2) ∨ (μ = 2 ∧ ν = 1) := by
  unfold curvature_const
  split_ifs with h1 h2
  · right; left; exact h1
  · right; right; exact h2
  · left; rfl

lemma epsilon4_1212 : epsilon4 1 2 1 2 = 0 := by
  unfold epsilon4 epsilon4_int
  exact Int.cast_zero

lemma epsilon4_1221 : epsilon4 1 2 2 1 = 0 := by
  unfold epsilon4 epsilon4_int
  exact Int.cast_zero

lemma epsilon4_2112 : epsilon4 2 1 1 2 = 0 := by
  unfold epsilon4 epsilon4_int
  exact Int.cast_zero

lemma epsilon4_2121 : epsilon4 2 1 2 1 = 0 := by
  unfold epsilon4 epsilon4_int
  exact Int.cast_zero

end CGD.Gravity

-- FILENAME: CGD/Gravity/ExactSolutionsPart13.lean

import CGD.Gravity.ExactSolutionsPart12

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma extractAdjoint_zero : extractAdjoint (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  unfold extractAdjoint
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.trace, Matrix.diag]

end CGD.Gravity

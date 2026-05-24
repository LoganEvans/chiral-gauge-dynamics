-- FILENAME: CGD/Gravity/ExactSolutionsPart3.lean

import CGD.Gravity.ExactSolutionsPart2

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def curvature_const (c : ℂ) (beta gamma : Fin 4) : SL2C :=
  if beta = 1 ∧ gamma = 2 then toSl2c (c • sigmaX)
  else if beta = 2 ∧ gamma = 1 then toSl2c ((-c) • sigmaX)
  else 0

end CGD.Gravity

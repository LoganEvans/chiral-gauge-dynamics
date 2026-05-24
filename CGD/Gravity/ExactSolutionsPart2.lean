-- FILENAME: CGD/Gravity/ExactSolutionsPart2.lean

import CGD.Gravity.ExactSolutionsPart1

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def exactAbelianField (c : ℂ) (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  if mu = 2 then toSl2c (exactAbelianL c x) else 0

end CGD.Gravity

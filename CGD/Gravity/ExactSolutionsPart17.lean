-- FILENAME: CGD/Gravity/ExactSolutionsPart17.lean

import CGD.Gravity.ExactSolutionsPart16

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def exactLorentzianField (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  toSl2c (exactLorentzianL mu x)

end CGD.Gravity

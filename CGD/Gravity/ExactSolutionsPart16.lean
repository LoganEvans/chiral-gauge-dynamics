-- FILENAME: CGD/Gravity/ExactSolutionsPart16.lean

import CGD.Gravity.ExactSolutionsPart15

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def exactLorentzianL (mu : Fin 4) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  if mu = 1 then - (x 0 : ℝ) • sigmaX + (x 3 : ℝ) • ((Complex.I / 2) • sigmaY) - (x 2 : ℝ) • ((Complex.I / 2) • sigmaZ)
  else if mu = 2 then - (x 0 : ℝ) • sigmaY + (x 1 : ℝ) • ((Complex.I / 2) • sigmaZ) - (x 3 : ℝ) • ((Complex.I / 2) • sigmaX)
  else if mu = 3 then - (x 0 : ℝ) • sigmaZ + (x 2 : ℝ) • ((Complex.I / 2) • sigmaX) - (x 1 : ℝ) • ((Complex.I / 2) • sigmaY)
  else 0

end CGD.Gravity

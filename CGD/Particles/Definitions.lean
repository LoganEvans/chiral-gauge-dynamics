-- FILENAME: CGD/Particles/Definitions.lean

import CGD.Foundations.Spacetime
import CGD.Gravity.Geometry
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import Mathlib.Data.Complex.Basic
import Litlib.Core
import CGD.Axioms.Ontology


open CGD.Axioms CGD.Foundations CGD.Math Matrix Complex

namespace CGD.Particles

/--
The 4D BPST Instanton in the regular gauge.
Topologically localizes in both space and time via the 't Hooft symbols.
Multiplied by Complex.I to map into the strictly anti-Hermitian su(2) Lie algebra.
-/
noncomputable def bpstInstanton (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  let r2 : ℂ := (x 0 : ℂ)^2 + (x 1 : ℂ)^2 + (x 2 : ℂ)^2 + (x 3 : ℂ)^2
  let D : ℂ := r2 + 1
  if mu = 0 then (Complex.I / D) • ((x 1 : ℂ) • sigma1 + (x 2 : ℂ) • sigma2 + (x 3 : ℂ) • sigma3)
  else if mu = 1 then (Complex.I / D) • (-(x 0 : ℂ) • sigma1 - (x 3 : ℂ) • sigma2 + (x 2 : ℂ) • sigma3)
  else if mu = 2 then (Complex.I / D) • ((x 3 : ℂ) • sigma1 - (x 0 : ℂ) • sigma2 - (x 1 : ℂ) • sigma3)
  else if mu = 3 then (Complex.I / D) • (-(x 2 : ℂ) • sigma1 + (x 1 : ℂ) • sigma2 - (x 0 : ℂ) • sigma3)
  else 0

noncomputable def homogeneousChaosAnsatz (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  if mu = 1 then (Complex.I * (x 1 : ℂ)) • sigma1
  else if mu = 2 then (Complex.I * (x 2 : ℂ)) • sigma2
  else 0

/--
Defines a single-color (Abelian) condensate where all components of the curvature tensor commute, constraining the field to a single U(1) Cartan subalgebra.
-/
def isSingleColor (F : Fin 4 -> Fin 4 -> SL2C) : Prop :=
  ∀ mu nu rho sigma, ⁅F mu nu, F rho sigma⁆ = 0

end CGD.Particles

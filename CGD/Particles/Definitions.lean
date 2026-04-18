-- FILENAME: CGD/Particles/Definitions.lean

import CGD.Axioms.Spacetime
import CGD.Gravity.Geometry
import CGD.Foundations.Calculus
import Mathlib.Data.Complex.Basic
import Litlib.Core
import CGD.Axioms.Ontology

set_option linter.unusedVariables false

open CGD.Axioms CGD.Foundations Matrix Complex

namespace CGD.Particles

noncomputable def solitonCore : SpacetimePoint := fun i => if i ≠ 0 then 1 else 0

/-- 
The true W=1 Topological Hedgehog (Physical su(2) mapping).
Utilizes the strictly winding 't Hooft Levi-Civita tensor (ε_{ijk} x_j σ_k), 
the 1/(r^2+1) finite-energy topological boundary envelope, and the 
imaginary factor `Complex.I` to map the Hermitian Pauli observables 
into the anti-Hermitian su(2) physical phase space.
-/
noncomputable def hedgehogBps (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  let r2 : ℂ := (x 1 : ℂ)^2 + (x 2 : ℂ)^2 + (x 3 : ℂ)^2
  let decay : ℂ := 1 / (r2 + 1)
  if mu = 1 then (Complex.I * decay) • ((x 2 : ℂ) • sigma3 - (x 3 : ℂ) • sigma2)
  else if mu = 2 then (Complex.I * decay) • ((x 3 : ℂ) • sigma1 - (x 1 : ℂ) • sigma3)
  else if mu = 3 then (Complex.I * decay) • ((x 1 : ℂ) • sigma2 - (x 2 : ℂ) • sigma1)
  else 0

/-- A translationally invariant representation of the W=1 topological boundary state -/
noncomputable def shiftedHedgehog (center : SpacetimePoint) : Fin 4 → SpacetimePoint → SL2C :=
  fun mu p => hedgehogBps mu (fun i => p i - center i)

/-- 
The true 4D BPST Instanton (regular gauge, lambda=1). 
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
Mathematically enforces that a 1D string is defined by a geometric vector-tensor outer product,
rather than trivially hardcoding matrix elements to zero.
-/
def isCrushedString (E : Matrix (Fin 3) (Fin 3) ℂ) (E_z : ℂ) : Prop :=
  ∃ (v : Fin 3 → ℂ), (∀ i j, E i j = E_z * v i * v j) ∧ (v 0 * v 0 + v 1 * v 1 + v 2 * v 2 = 1)

/--
Hypothesis: Single Color Condensate.
Instead of forcing generators to zero, we define an Abelian reduction formally:
all components of the curvature tensor commute. This means the field lies entirely
within a single U(1) Cartan subalgebra, organically destroying the 3D SU(2) volume.
-/
def isSingleColor (F : Fin 4 -> Fin 4 -> SL2C) : Prop :=
  ∀ mu nu rho sigma, ⁅F mu nu, F rho sigma⁆ = 0

end CGD.Particles

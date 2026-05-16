-- FILENAME: CGD/Quantum/Definitions.lean

import Litlib.Core
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Axioms.Ontology
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

set_option linter.unusedVariables false

open CGD.Axioms CGD.Foundations Matrix Complex

namespace CGD.Quantum

/-- 
The baseline unbroken topology of a 1D string defect along the z-axis.
-/
noncomputable def fluxTubeFrame (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  toSl2c (if mu = 0 then 0 else if mu = 1 then (Complex.I:ℂ) • sigma3.val else if mu = 2 then (Complex.I:ℂ) • sigma1.val else (Complex.I:ℂ) • sigma2.val)

/-- 
A multi-fingered gauge rotation applied to a background connection.
-/
noncomputable def rotateYAxis (A : Fin 4 → SpacetimePoint → SL2C) (theta : Real) (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  let R := Matrix.of ![![Complex.cos (theta/2), -Complex.sin (theta/2)], ![Complex.sin (theta/2), Complex.cos (theta/2)]]
  let R_inv := Matrix.of ![![Complex.cos (theta/2), Complex.sin (theta/2)], ![-Complex.sin (theta/2), Complex.cos (theta/2)]]
  toSl2c (R * (A mu x).val * R_inv)

/-- 
Mathematically identifies a local defect as an unbroken flux tube.
-/
def isFluxTube (A : Fin 4 → SpacetimePoint → SL2C) (x : SpacetimePoint) : Prop :=
  (∀ mu, A mu x = fluxTubeFrame mu x) ∧
  (∀ mu nu, partialDerivSl2c nu (A mu) x = partialDerivSl2c nu (fluxTubeFrame mu) x)

/-- 
Identifies an ER=EPR entangled bridge. Two spatial boundaries are entangled 
if there exists a continuous topological flux tube connecting them, twisted 
by a relative gauge holonomy `theta`.
-/
def areEntangled (A : Fin 4 → SpacetimePoint → SL2C) (x y : SpacetimePoint) (theta : ℝ) : Prop :=
  ∃ (γ : ℝ → SpacetimePoint) (θ : ℝ → ℝ),
    γ 0 = x ∧ γ 1 = y ∧
    θ 0 = 0 ∧ θ 1 = theta ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∀ mu, A mu (γ t) = rotateYAxis fluxTubeFrame (θ t) mu (γ t)) ∧
      (∀ mu nu, partialDerivSl2c nu (A mu) (γ t) = partialDerivSl2c nu (rotateYAxis fluxTubeFrame (θ t) mu) (γ t))

end CGD.Quantum

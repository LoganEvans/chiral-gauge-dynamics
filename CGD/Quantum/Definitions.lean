-- FILENAME: CGD/Quantum/Definitions.lean

import Litlib.Core
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Axioms.Ontology
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

open CGD.Axioms CGD.Foundations Matrix Complex

namespace CGD.Quantum

/-- Re-engineered to explicitly embed the strictly anti-Hermitian generator via Complex.I -/
noncomputable def fluxTubeFrame (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  if mu = 1 then (Complex.I * (x 1 : ℂ)) • sigma2
  else if mu = 2 then (Complex.I * (x 1 : ℂ)) • sigma2
  else if mu = 3 then (Complex.I * (x 1 : ℂ)) • sigma3
  else 0

noncomputable def rotateZ (A : Fin 4 → SpacetimePoint → SL2C) (theta : Real) (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  if mu = 1 then
    (Complex.cos (theta : Complex)) • A 1 x + (Complex.I * Complex.sin (theta : Complex) * (x 1 : ℂ)) • sigma1
  else A mu x

def areEntangled (A : Fin 4 → SpacetimePoint → SL2C) (x y : SpacetimePoint) (theta : ℝ) : Prop :=
  ∃ (γ : ℝ → SpacetimePoint) (θ : ℝ → ℝ),
    γ 0 = x ∧ γ 1 = y ∧
    θ 0 = 0 ∧ θ 1 = theta ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∀ mu, A mu (γ t) = rotateZ fluxTubeFrame (θ t) mu (γ t)) ∧
      (∀ mu nu, partialDerivSl2c nu (A mu) (γ t) = partialDerivSl2c nu (rotateZ fluxTubeFrame (θ t) mu) (γ t))

def isFluxTube (A : Fin 4 → SpacetimePoint → SL2C) (x : SpacetimePoint) : Prop :=
  (∀ mu, A mu x = fluxTubeFrame mu x) ∧
  (∀ mu nu, partialDerivSl2c nu (A mu) x = partialDerivSl2c nu (fluxTubeFrame mu) x)

def isHeisenbergLimit (u : Universe) (x : SpacetimePoint) : Prop :=
  (∀ i, i ≠ 0 → curvatureSl2c u.sd_sector 0 i x = 0) ∧
  (∀ i, i ≠ 0 → partialDerivSl2c i (fun p => u.sd_sector 0 p) x = 0)

variable (integral1d : (ℝ → ℝ) → ℝ → ℝ → ℝ)

noncomputable def clickProbabilityCore (hbar E_threshold : ℝ) (pdf : ℝ → ℝ) : ℝ :=
  integral1d pdf E_threshold hbar

noncomputable def macroscopicObservable
  (holonomy : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
  (A : Fin 4 → SpacetimePoint → SL2C) (mu : Fin 4) (L : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := 
  (-Complex.I) • holonomy (fun s => (A mu (fun i => if i = mu then s else 0)).val) 0 L

def isCoherentSuperpositionState (u : Universe) (x : SpacetimePoint) 
  (E0 phi_avg delta_phi : ℂ) (sig : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (curvatureSl2c u.sd_sector 1 2 x).val = (E0 * Complex.cos (phi_avg + delta_phi / 2)) • sig + (E0 * Complex.cos (phi_avg - delta_phi / 2)) • sig

def isOrthogonalDecoherenceLimit (u : Universe) (x : SpacetimePoint) 
  (theta M : ℂ) (sigX sigZ : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  M ≠ 0 ∧
  (curvatureSl2c u.sd_sector 1 2 x).val = (Complex.cos theta) • sigZ + (Complex.sin theta) • sigX ∧
  (curvatureSl2c u.asd_sector 1 2 x).val = M • sigX

def mkMat (m00 m01 m10 m11 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then m00
    else if i.val = 0 ∧ j.val = 1 then m01
    else if i.val = 1 ∧ j.val = 0 then m10
    else m11

noncomputable def idMat : Matrix (Fin 2) (Fin 2) ℂ := mkMat 1 0 0 1
noncomputable def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := mkMat 0 1 1 0
noncomputable def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := mkMat 0 (-Complex.I) Complex.I 0
noncomputable def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := mkMat 1 0 0 (-1)

noncomputable def a1Opt : Matrix (Fin 2) (Fin 2) ℂ := sigmaZ
noncomputable def a2Opt : Matrix (Fin 2) (Fin 2) ℂ := sigmaX
noncomputable def b1Opt (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := c • (sigmaZ + sigmaX)
noncomputable def b2Opt (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := c • (sigmaZ - sigmaX)

noncomputable def measurementFrame (theta : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.cos theta • sigmaZ + Complex.sin theta • sigmaX

noncomputable def bellCorrelationBell (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (1 / 2 : ℂ) * Matrix.trace (A * B)

noncomputable def chshSumBell (A1 A2 B1 B2 : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  bellCorrelationBell A1 B1 + bellCorrelationBell A1 B2 + bellCorrelationBell A2 B1 - bellCorrelationBell A2 B2

end CGD.Quantum

-- FILENAME: CGD/Quantum/Dirac/Vacuum.lean

import CGD.Quantum.Dirac.Emergence
import CGD.Foundations.Bianchi
import CGD.Axioms.Ontology

open Matrix Complex BigOperators Litlib.Math.Dirac
open CGD.Foundations CGD.Axioms

namespace CGD.Quantum.Dirac

/--
Tier 1: Pure Math
The algebraic structure of the Vacuum Dirac Equation.
-/
@[litlib_track "Algebraic Vacuum Dirac Equation"]
theorem algebraicVacuumDiracEquation (D_F : Fin 4 → Fin 4 → Fin 4 → ℂ)
  (h_anti : ∀ c a b, D_F c a b = - D_F c b a)
  (h_bianchi : ∀ c a b, D_F c a b + D_F a b c + D_F b c a = 0)
  (h_vacuum : ∀ b, yangMillsCurrent D_F b = 0) :
  (∑ c : Fin 4, gammaVec c * (∑ a : Fin 4, ∑ b : Fin 4, D_F c a b • (gammaVec a * gammaVec b))) = 0 := by
  rw [kaehlerDiracEmergence D_F h_anti h_bianchi]
  have h_zero : (∑ b : Fin 4, yangMillsCurrent D_F b • gammaVec b) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    rw [h_vacuum b, zero_smul]
  rw [h_zero, smul_zero]

/--
Tier 2: Physical Emergence
The Vacuum Dirac Equation (Physical Realization).
By binding the Dirac mode strictly to the actual Sl2cGaugeField, the arbitrary 
algebraic hypothesis of the Bianchi identity is eradicated. The native differential 
Bianchi identity (dF = 0) of the physical continuous geometry mathematically enforces 
the spinor constraints.

If the macroscopic geometry satisfies the source-free vacuum equations (J = 0), 
the geometric spinor mode mathematically and strictly obeys the massless Dirac equation.
-/
@[litlib_track "Physical Vacuum Dirac Equation"]
theorem physicalVacuumDiracEquation
  [clairaut : Litlib.Y1976.rudin1976principles.ClairautTheoremNDimensional]
  (A : Sl2cGaugeField)
  (x : SpacetimePoint)
  (Lambda : SL2C → ℂ)
  (h_linear : ∀ m1 m2, Lambda (m1 + m2) = Lambda m1 + Lambda m2)
  (h_zero : Lambda 0 = 0)
  (h_anti : ∀ c a b, Lambda (covariantDeriv A.val c a b x) = - Lambda (covariantDeriv A.val c b a x))
  (h_vacuum : ∀ b, yangMillsCurrent (fun c a b => Lambda (covariantDeriv A.val c a b x)) b = 0) :
  let D_F := fun c a b => Lambda (covariantDeriv A.val c a b x);
  (∑ c : Fin 4, gammaVec c * (∑ a : Fin 4, ∑ b : Fin 4, D_F c a b • (gammaVec a * gammaVec b))) = 0 := by
  let D_F := fun c a b => Lambda (covariantDeriv A.val c a b x)
  apply algebraicVacuumDiracEquation D_F
  · exact h_anti
  · intros c a b
    dsimp [D_F]
    have h_sum : Lambda (covariantDeriv A.val c a b x + covariantDeriv A.val a b c x) = Lambda (covariantDeriv A.val c a b x) + Lambda (covariantDeriv A.val a b c x) := h_linear _ _
    have h_sum2 : Lambda (covariantDeriv A.val c a b x + covariantDeriv A.val a b c x + covariantDeriv A.val b c a x) = Lambda (covariantDeriv A.val c a b x + covariantDeriv A.val a b c x) + Lambda (covariantDeriv A.val b c a x) := h_linear _ _
    have h_B := kinematicBianchiIdentity A c a b x
    rw [h_B] at h_sum2
    rw [h_zero] at h_sum2
    rw [h_sum] at h_sum2
    exact h_sum2.symm
  · exact h_vacuum

end CGD.Quantum.Dirac

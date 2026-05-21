-- FILENAME: CGD/Quantum/Dirac.lean

import Litlib.Core
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Axioms.Ontology
import Litlib.Math.Dirac
import Mathlib.Tactic.FinCases

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators Litlib.Math.Dirac
open CGD.Axioms

namespace CGD.Quantum

noncomputable def extractSpinorMode (u : Universe) (x : SpacetimePoint) : Matrix (Fin 4) (Fin 4) Complex :=
  u.spin4c_connection 0 x

noncomputable def extractSpinorDeriv (u : Universe) (x : SpacetimePoint) (mu : Fin 4) : Matrix (Fin 4) (Fin 4) Complex :=
  partialDerivChiral mu (fun p => u.spin4c_connection 0 p) x

noncomputable def diracOperatorCore (dPsi : Fin 4 → SpacetimePoint → Matrix (Fin 4) (Fin 4) Complex) (x : SpacetimePoint) : Matrix (Fin 4) (Fin 4) Complex :=
  ∑ mu, gammaVec mu * dPsi mu x

lemma isOdd_sum (f : Fin 4 → Matrix (Fin 4) (Fin 4) Complex) 
  (hf : ∀ mu, isOdd (f mu)) : isOdd (∑ mu, f mu) := by
  intros i j hij
  rw [Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intros mu _
  exact hf mu i j hij

lemma isEven_embedSelfDual (M : SL2C) : isEven (embedSelfDual M) := by
  intros i j hij
  unfold embedSelfDual
  change (match CGD.Foundations.chiralIso.symm i, CGD.Foundations.chiralIso.symm j with
          | Sum.inl i', Sum.inl j' => M.val i' j'
          | _, _ => 0) = 0
  have h_symm_i_eq : CGD.Foundations.chiralIso.symm i = Litlib.Math.Dirac.chiralIsoInv i := by
    fin_cases i <;> rfl
  have h_symm_j_eq : CGD.Foundations.chiralIso.symm j = Litlib.Math.Dirac.chiralIsoInv j := by
    fin_cases j <;> rfl
  rw [h_symm_i_eq, h_symm_j_eq]
  cases h_i : Litlib.Math.Dirac.chiralIsoInv i <;> cases h_j : Litlib.Math.Dirac.chiralIsoInv j
  · have h_light_i : isLight i = true := by unfold isLight; rw [h_i]
    have h_light_j : isLight j = true := by unfold isLight; rw [h_j]
    rw [h_light_i, h_light_j] at hij
    contradiction
  · rfl
  · rfl
  · rfl

lemma isEven_embedAntiSelfDual (M : SL2C) : isEven (embedAntiSelfDual M) := by
  intros i j hij
  unfold embedAntiSelfDual
  change (match CGD.Foundations.chiralIso.symm i, CGD.Foundations.chiralIso.symm j with
          | Sum.inr i', Sum.inr j' => M.val i' j'
          | _, _ => 0) = 0
  have h_symm_i_eq : CGD.Foundations.chiralIso.symm i = Litlib.Math.Dirac.chiralIsoInv i := by
    fin_cases i <;> rfl
  have h_symm_j_eq : CGD.Foundations.chiralIso.symm j = Litlib.Math.Dirac.chiralIsoInv j := by
    fin_cases j <;> rfl
  rw [h_symm_i_eq, h_symm_j_eq]
  cases h_i : Litlib.Math.Dirac.chiralIsoInv i <;> cases h_j : Litlib.Math.Dirac.chiralIsoInv j
  · rfl
  · rfl
  · rfl
  · have h_light_i : isLight i = false := by unfold isLight; rw [h_i]
    have h_light_j : isLight j = false := by unfold isLight; rw [h_j]
    rw [h_light_i, h_light_j] at hij
    contradiction

lemma isEven_extractSpinorMode (u : Universe) (x : SpacetimePoint) : isEven (extractSpinorMode u x) := by
  intros i j hij
  unfold extractSpinorMode
  rw [spin4c_connection_eq_embed]
  have h1 := isEven_embedSelfDual (u.sd_sector 0 x) i j hij
  have h2 := isEven_embedAntiSelfDual (u.asd_sector 0 x) i j hij
  change (embedSelfDual (u.sd_sector 0 x) + embedAntiSelfDual (u.asd_sector 0 x)) i j = 0
  rw [Matrix.add_apply, h1, h2, zero_add]

lemma isEven_extractSpinorDeriv (u : Universe) (x : SpacetimePoint) (mu : Fin 4) : isEven (extractSpinorDeriv u x mu) := by
  intros i j hij
  unfold extractSpinorDeriv partialDerivChiral
  have h1 := isEven_embedSelfDual (partialDerivSl2c mu (fun p => toSl2c (fun i j => (u.spin4c_connection 0 p) (CGD.Foundations.chiralIso (Sum.inl i)) (CGD.Foundations.chiralIso (Sum.inl j)))) x) i j hij
  have h2 := isEven_embedAntiSelfDual (partialDerivSl2c mu (fun p => toSl2c (fun i j => (u.spin4c_connection 0 p) (CGD.Foundations.chiralIso (Sum.inr i)) (CGD.Foundations.chiralIso (Sum.inr j)))) x) i j hij
  change (embedSelfDual _ + embedAntiSelfDual _) i j = 0
  rw [Matrix.add_apply, h1, h2, zero_add]

lemma isOdd_smul (c : Complex) (M : Matrix (Fin 4) (Fin 4) Complex) (hM : isOdd M) : isOdd (c • M) := by
  intros i j hij
  rw [Matrix.smul_apply, hM i j hij, smul_zero]

Litlib.theorem
  description "Geometric Dirac Operator Grading"
/--
The Dirac operator geometrically emerges as an evaluation of the temporal gauge connection acting on the 4D Spin(4,C) multiplet, natively preserving the odd/even grading of the spinor operator.
-/
theorem kinematicDiracOperatorGrading (u : Universe) :
  ∀ (m : Complex) (x : SpacetimePoint),
    isOdd (diracOperatorCore (fun mu p => extractSpinorDeriv u p mu) x) ∧ 
    isOdd (m • (extractSpinorMode u x * gamma0)) := by
  intros m x
  constructor
  · unfold diracOperatorCore
    apply isOdd_sum
    intros mu
    apply Litlib.Math.Dirac.odd_mul_even
    · exact Litlib.Math.Dirac.hestenesIsomorphism mu
    · exact isEven_extractSpinorDeriv u x mu
  · apply isOdd_smul
    apply Litlib.Math.Dirac.even_mul_odd
    · exact isEven_extractSpinorMode u x
    · exact Litlib.Math.Dirac.is_odd_gamma0

end CGD.Quantum

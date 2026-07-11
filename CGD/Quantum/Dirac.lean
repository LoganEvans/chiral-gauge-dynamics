-- FILENAME: CGD/Quantum/Dirac.lean

import Litlib.Core
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse
import CGD.Gravity.Geometry
import Litlib.Math.Dirac
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations CGD.Math CGD.Gravity Matrix Complex BigOperators Litlib.Math.Dirac
open CGD.Axioms

namespace CGD.Quantum

noncomputable def extractSpinorMode (u : Universe) (x : SpacetimePoint) (nu : Fin 4) : Matrix (Fin 4) (Fin 4) Complex :=
  u.spin4c_connection nu x

noncomputable def extractSpinorDeriv (u : Universe) (x : SpacetimePoint) (mu nu : Fin 4) : Matrix (Fin 4) (Fin 4) Complex :=
  partialDerivChiral mu (fun p => u.spin4c_connection nu p) x

/--
The exact gauge-covariant derivative of the spinor matter mode.
Defined geometrically as D_mu A_nu = \partial_mu A_nu + [A_mu, A_nu].
-/
noncomputable def covariantSpinorDeriv (u : Universe) (x : SpacetimePoint) (mu nu : Fin 4) : Matrix (Fin 4) (Fin 4) Complex :=
  let dA_nu := extractSpinorDeriv u x mu nu
  let comm := bracket (u.spin4c_connection mu x) (extractSpinorMode u x nu)
  dA_nu + (embedSelfDual (chiralProject comm).self_dual + embedAntiSelfDual (chiralProject comm).anti_self_dual)

/--
The true background-independent Emergent Dirac Operator.
It strictly contracts the local covariant spinor derivatives using the dynamically
emergent macroscopic TetradField (Vielbein) rather than assuming a flat-space metric.
-/
@[litlib_track "Emergent Dirac Operator"]
noncomputable def emergentDiracOperator (u : Universe) (e : TetradField) (x : SpacetimePoint) (nu : Fin 4) : Matrix (Fin 4) (Fin 4) Complex :=
  ∑ mu, ∑ a, (e a mu x) • (gammaVec a * covariantSpinorDeriv u x mu nu)

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

lemma isEven_extractSpinorMode (u : Universe) (x : SpacetimePoint) (nu : Fin 4) : isEven (extractSpinorMode u x nu) := by
  intros i j hij
  unfold extractSpinorMode
  rw [spin4c_connection_eq_embed]
  have h1 := isEven_embedSelfDual (u.sd_sector nu x) i j hij
  have h2 := isEven_embedAntiSelfDual (u.asd_sector nu x) i j hij
  change (embedSelfDual (u.sd_sector nu x) + embedAntiSelfDual (u.asd_sector nu x)) i j = 0
  rw [Matrix.add_apply, h1, h2, zero_add]

lemma isEven_extractSpinorDeriv (u : Universe) (x : SpacetimePoint) (mu nu : Fin 4) : isEven (extractSpinorDeriv u x mu nu) := by
  intros i j hij
  unfold extractSpinorDeriv partialDerivChiral
  have h1 := isEven_embedSelfDual (partialDerivSl2c mu (fun p => toSl2c (fun i j => (u.spin4c_connection nu p) (CGD.Foundations.chiralIso (Sum.inl i)) (CGD.Foundations.chiralIso (Sum.inl j)))) x) i j hij
  have h2 := isEven_embedAntiSelfDual (partialDerivSl2c mu (fun p => toSl2c (fun i j => (u.spin4c_connection nu p) (CGD.Foundations.chiralIso (Sum.inr i)) (CGD.Foundations.chiralIso (Sum.inr j)))) x) i j hij
  change (embedSelfDual _ + embedAntiSelfDual _) i j = 0
  rw [Matrix.add_apply, h1, h2, zero_add]

lemma isEven_covariantSpinorDeriv (u : Universe) (x : SpacetimePoint) (mu nu : Fin 4) : isEven (covariantSpinorDeriv u x mu nu) := by
  intros i j hij
  unfold covariantSpinorDeriv
  rw [Matrix.add_apply]
  have h1 := isEven_extractSpinorDeriv u x mu nu i j hij
  rw [h1, zero_add]
  have h2 := isEven_embedSelfDual (chiralProject (bracket (u.spin4c_connection mu x) (extractSpinorMode u x nu))).self_dual i j hij
  have h3 := isEven_embedAntiSelfDual (chiralProject (bracket (u.spin4c_connection mu x) (extractSpinorMode u x nu))).anti_self_dual i j hij
  rw [Matrix.add_apply, h2, h3, zero_add]

lemma isOdd_smul (c : Complex) (M : Matrix (Fin 4) (Fin 4) Complex) (hM : isOdd M) : isOdd (c • M) := by
  intros i j hij
  rw [Matrix.smul_apply, hM i j hij, smul_zero]

/--
The covariant Dirac operator mathematically preserves the strict odd/even grading of the spinor algebra for any orientation vector.
-/
@[litlib_track "Kinematic Dirac Operator Grading"]
theorem kinematicDiracOperatorGrading (pu : PhysicalUniverse) :
  ∀ (m : Complex) (e : TetradField) (x : SpacetimePoint) (nu : Fin 4),
    isOdd (emergentDiracOperator pu.toUniverse e x nu) ∧
    isOdd (m • (extractSpinorMode pu.toUniverse x nu * gammaVec nu)) := by
  intros m e x nu
  constructor
  · unfold emergentDiracOperator
    apply isOdd_sum; intro mu
    apply isOdd_sum; intro a
    apply isOdd_smul
    apply Litlib.Math.Dirac.odd_mul_even
    · exact Litlib.Math.Dirac.hestenesIsomorphism a
    · exact isEven_covariantSpinorDeriv pu.toUniverse x mu nu
  · apply isOdd_smul
    apply Litlib.Math.Dirac.even_mul_odd
    · exact isEven_extractSpinorMode pu.toUniverse x nu
    · exact Litlib.Math.Dirac.hestenesIsomorphism nu

@[litlib_track "Gauge-Covariant Spinor Derivative Identity"]
lemma covariantSpinorDeriv_eq_curvature_plus_deriv (u : Universe) (x : SpacetimePoint) (mu nu : Fin 4) :
  covariantSpinorDeriv u x mu nu =
  curvature (fun m p => u.spin4c_connection m p) mu nu x + partialDerivChiral nu (fun p => u.spin4c_connection mu p) x := by
  unfold covariantSpinorDeriv extractSpinorDeriv extractSpinorMode curvature
  dsimp only
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply]
  ring

/--
The fully covariant Dirac operator natively equals the macroscopic Yang-Mills curvature trace,
plus a geometric inertial term (\partial_nu A_mu) reflecting the dynamical evolution of the background geometry.
Matter actively responds to the bubbling and expansion of spacetime without requiring a fixed coordinate frame.
-/
@[litlib_track "Generalized Dynamic Dirac Equation"]
theorem generalizedDynamicDiracEquation
  (pu : PhysicalUniverse) (e : TetradField) (x : SpacetimePoint) (nu : Fin 4) :
  emergentDiracOperator pu.toUniverse e x nu =
  ∑ mu, ∑ a, (e a mu x) • (gammaVec a * curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x) +
  ∑ mu, ∑ a, (e a mu x) • (gammaVec a * partialDerivChiral nu (fun p => pu.toUniverse.spin4c_connection mu p) x) := by
  unfold emergentDiracOperator
  have h_sub : ∀ mu a, (e a mu x) • (gammaVec a * covariantSpinorDeriv pu.toUniverse x mu nu) =
                       (e a mu x) • (gammaVec a * curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x) +
                       (e a mu x) • (gammaVec a * partialDerivChiral nu (fun p => pu.toUniverse.spin4c_connection mu p) x) := by
    intro mu a
    rw [covariantSpinorDeriv_eq_curvature_plus_deriv]
    rw [Matrix.mul_add, smul_add]

  have h_congr : (∑ mu : Fin 4, ∑ a : Fin 4, (e a mu x) • (gammaVec a * covariantSpinorDeriv pu.toUniverse x mu nu)) =
                 ∑ mu : Fin 4, ∑ a : Fin 4, ((e a mu x) • (gammaVec a * curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x) +
                                             (e a mu x) • (gammaVec a * partialDerivChiral nu (fun p => pu.toUniverse.spin4c_connection mu p) x)) := by
    apply Finset.sum_congr rfl
    intro mu _
    apply Finset.sum_congr rfl
    intro a _
    exact h_sub mu a

  rw [h_congr]

  have h_inner : ∀ mu, (∑ a : Fin 4, ((e a mu x) • (gammaVec a * curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x) +
                                      (e a mu x) • (gammaVec a * partialDerivChiral nu (fun p => pu.toUniverse.spin4c_connection mu p) x))) =
                       (∑ a : Fin 4, (e a mu x) • (gammaVec a * curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x)) +
                       (∑ a : Fin 4, (e a mu x) • (gammaVec a * partialDerivChiral nu (fun p => pu.toUniverse.spin4c_connection mu p) x)) := by
    intro mu
    exact Finset.sum_add_distrib

  have h_outer : (∑ mu : Fin 4, ∑ a : Fin 4, ((e a mu x) • (gammaVec a * curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x) +
                                              (e a mu x) • (gammaVec a * partialDerivChiral nu (fun p => pu.toUniverse.spin4c_connection mu p) x))) =
                 ∑ mu : Fin 4, ((∑ a : Fin 4, (e a mu x) • (gammaVec a * curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x)) +
                                (∑ a : Fin 4, (e a mu x) • (gammaVec a * partialDerivChiral nu (fun p => pu.toUniverse.spin4c_connection mu p) x))) := by
    apply Finset.sum_congr rfl
    intro mu _
    exact h_inner mu

  rw [h_outer]
  exact Finset.sum_add_distrib

/--
Recovers the standard textbook Dirac-Yang-Mills equivalence under the physical assumption that
the spacetime background is locally stationary with respect to the mode propagation direction.
-/
@[litlib_track "Familiar Dynamic Dirac Equation Limit"]
theorem familiarDynamicDiracEquation
  (pu : PhysicalUniverse) (e : TetradField) (x : SpacetimePoint) (nu : Fin 4)
  (h_stationary : ∀ mu, partialDerivChiral nu (fun p => pu.toUniverse.spin4c_connection mu p) x = 0) :
  emergentDiracOperator pu.toUniverse e x nu =
  ∑ mu, ∑ a, (e a mu x) • (gammaVec a * curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x) := by
  rw [generalizedDynamicDiracEquation]
  have h_zero : (∑ mu : Fin 4, ∑ a : Fin 4, (e a mu x) • (gammaVec a * partialDerivChiral nu (fun p => pu.toUniverse.spin4c_connection mu p) x)) = 0 := by
    apply Finset.sum_eq_zero; intro mu _
    apply Finset.sum_eq_zero; intro a _
    rw [h_stationary mu, Matrix.mul_zero, smul_zero]
  rw [h_zero, add_zero]

end CGD.Quantum

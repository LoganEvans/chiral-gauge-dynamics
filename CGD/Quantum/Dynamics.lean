-- FILENAME: CGD/Quantum/Dynamics.lean

import Litlib.Core
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Calculus
import CGD.Particles.Definitions
import CGD.Quantum.Definitions
import CGD.Axioms.Ontology
import Litlib.Math.Dirac
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Particles Matrix Complex BigOperators Litlib.Math.Dirac
open CGD.Axioms

namespace CGD.Quantum

noncomputable def gaugeCommutator (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := A * B - B * A

noncomputable def classicalElectricField (u : Universe) (i : Fin 4) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  partialDerivMat 0 (fun p => (u.sd_sector i p).val) x -
  partialDerivMat i (fun p => (u.sd_sector 0 p).val) x +
  gaugeCommutator (u.sd_sector 0 x).val (u.sd_sector i x).val

/-- 🟡 KINEMATIC: Temporal Evolution (Vacuum Commutator) -/
theorem kinematicTemporalEvolution (u : Universe) (x : SpacetimePoint) :
  isHeisenbergLimit u x →
  partialDerivSl2c 0 (fun p => u.sd_sector 1 p) x = - ⁅u.sd_sector 0 x, u.sd_sector 1 x⁆ := by
  intro h_lim
  have h_curv := h_lim.1 1 (by decide)
  have h_deriv := h_lim.2 1 (by decide)
  unfold curvatureSl2c at h_curv
  rw [h_deriv] at h_curv
  simp only [sub_zero] at h_curv
  exact add_eq_zero_iff_eq_neg.mp h_curv

lemma trace_2x2 (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace A = A 0 0 + A 1 1 := by simp[Matrix.trace, Fin.sum_univ_two]
lemma mul_2x2 (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by rw[Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma s1_00 : sigma1.val 0 0 = 0 := rfl
@[simp] lemma s1_01 : sigma1.val 0 1 = 1 := rfl
@[simp] lemma s1_10 : sigma1.val 1 0 = 1 := rfl
@[simp] lemma s1_11 : sigma1.val 1 1 = 0 := rfl

@[simp] lemma s2_00 : sigma2.val 0 0 = 0 := rfl
@[simp] lemma s2_01 : sigma2.val 0 1 = -I := rfl
@[simp] lemma s2_10 : sigma2.val 1 0 = I := rfl
@[simp] lemma s2_11 : sigma2.val 1 1 = 0 := rfl

/-- 🔵 KINEMATIC: Yang-Mills Chaos (Non-Abelian cross terms yield x^2 y^2 potential) -/
theorem kinematicYangMillsChaos (u : Universe) :
  ∀ (x : SpacetimePoint),
    Matrix.trace (⁅homogeneousChaosAnsatz 1 x, homogeneousChaosAnsatz 2 x⁆.val *
                  ⁅homogeneousChaosAnsatz 1 x, homogeneousChaosAnsatz 2 x⁆.val) =
    -8 * (x 1 : ℂ)^2 * (x 2 : ℂ)^2 := by
  intro x
  have h_comm : ⁅homogeneousChaosAnsatz 1 x, homogeneousChaosAnsatz 2 x⁆.val =
    (Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val := rfl
  rw [h_comm]

  have h_eval_00 : ((Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val) 0 0 = -2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ) := by
    rw [Matrix.sub_apply, mul_2x2, mul_2x2]
    change ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 0) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 0 0) + ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 1) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 1 0) - (((Complex.I * (x 2 : ℂ)) * sigma2.val 0 0) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 0) + ((Complex.I * (x 2 : ℂ)) * sigma2.val 0 1) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 0)) = _
    rw [s1_00, s1_01, s1_10, s2_00, s2_01, s2_10]
    have step : ((Complex.I * (x 1 : ℂ)) * 0) * ((Complex.I * (x 2 : ℂ)) * 0) + ((Complex.I * (x 1 : ℂ)) * 1) * ((Complex.I * (x 2 : ℂ)) * Complex.I) - (((Complex.I * (x 2 : ℂ)) * 0) * ((Complex.I * (x 1 : ℂ)) * 0) + ((Complex.I * (x 2 : ℂ)) * -Complex.I) * ((Complex.I * (x 1 : ℂ)) * 1)) = 2 * Complex.I^2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ) := by ring
    rw [step, Complex.I_sq]
    ring

  have h_eval_01 : ((Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val) 0 1 = 0 := by
    rw [Matrix.sub_apply, mul_2x2, mul_2x2]
    change ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 0) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 0 1) + ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 1) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 1 1) - (((Complex.I * (x 2 : ℂ)) * sigma2.val 0 0) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 1) + ((Complex.I * (x 2 : ℂ)) * sigma2.val 0 1) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 1)) = 0
    rw [s1_00, s1_01, s1_11, s2_00, s2_01, s2_11]
    ring

  have h_eval_10 : ((Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val) 1 0 = 0 := by
    rw [Matrix.sub_apply, mul_2x2, mul_2x2]
    change ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 0) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 0 0) + ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 1) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 1 0) - (((Complex.I * (x 2 : ℂ)) * sigma2.val 1 0) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 0) + ((Complex.I * (x 2 : ℂ)) * sigma2.val 1 1) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 0)) = 0
    rw [s1_10, s1_11, s1_00, s2_10, s2_11, s2_00]
    ring

  have h_eval_11 : ((Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val) 1 1 = 2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ) := by
    rw [Matrix.sub_apply, mul_2x2, mul_2x2]
    change ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 0) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 0 1) + ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 1) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 1 1) - (((Complex.I * (x 2 : ℂ)) * sigma2.val 1 0) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 1) + ((Complex.I * (x 2 : ℂ)) * sigma2.val 1 1) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 1)) = _
    rw [s1_10, s1_11, s1_01, s2_10, s2_11, s2_01]
    have step : ((Complex.I * (x 1 : ℂ)) * 1) * ((Complex.I * (x 2 : ℂ)) * -Complex.I) + ((Complex.I * (x 1 : ℂ)) * 0) * ((Complex.I * (x 2 : ℂ)) * 0) - (((Complex.I * (x 2 : ℂ)) * Complex.I) * ((Complex.I * (x 1 : ℂ)) * 1) + ((Complex.I * (x 2 : ℂ)) * 0) * ((Complex.I * (x 1 : ℂ)) * 0)) = -2 * Complex.I^2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ) := by ring
    rw [step, Complex.I_sq]
    ring

  change Matrix.trace (((Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val) * ((Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val)) = -8 * (x 1 : ℂ)^2 * (x 2 : ℂ)^2
  rw [trace_2x2, mul_2x2, mul_2x2]
  rw [h_eval_00, h_eval_01, h_eval_10, h_eval_11]
  have h_final : (-2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ)) * (-2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ)) + 0 * 0 + (0 * 0 + (2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ)) * (2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ))) = 8 * Complex.I^2 * (x 1 : ℂ)^2 * (x 2 : ℂ)^2 := by ring
  rw [h_final, Complex.I_sq]
  ring

noncomputable def extractSpinorMode (u : Universe) (x : SpacetimePoint) : Matrix (Fin 4) (Fin 4) Complex :=
  u.spin4c_connection 0 x

noncomputable def extractSpinorDeriv (u : Universe) (x : SpacetimePoint) (mu : Fin 4) : Matrix (Fin 4) (Fin 4) Complex :=
  partialDerivChiral mu (fun p => u.spin4c_connection 0 p) x

noncomputable def diracOperatorCore (dPsi : Fin 4 → SpacetimePoint → Matrix (Fin 4) (Fin 4) Complex) (x : SpacetimePoint) : Matrix (Fin 4) (Fin 4) Complex :=
  ∑ mu, gammaVec mu * dPsi mu x

@[simp] lemma chiralIso_symm_eval_0 : CGD.Foundations.chiralIso.symm 0 = Sum.inl 0 := rfl
@[simp] lemma chiralIso_symm_eval_1 : CGD.Foundations.chiralIso.symm 1 = Sum.inl 1 := rfl
@[simp] lemma chiralIso_symm_eval_2 : CGD.Foundations.chiralIso.symm 2 = Sum.inr 0 := rfl
@[simp] lemma chiralIso_symm_eval_3 : CGD.Foundations.chiralIso.symm 3 = Sum.inr 1 := rfl

lemma isEven_embedSelfDual_add_embedAntiSelfDual (A B : SL2C) : isEven (embedSelfDual A + embedAntiSelfDual B) := by
  intro i j hij
  revert hij
  change isLight i ≠ isLight j → (embedSelfDual A + embedAntiSelfDual B) i j = 0
  refine match i, j with
  | 0, 0 => fun h => False.elim (h rfl)
  | 0, 1 => fun h => False.elim (h rfl)
  | 0, 2 => fun _ => by simp [embedSelfDual, embedAntiSelfDual]
  | 0, 3 => fun _ => by simp [embedSelfDual, embedAntiSelfDual]
  | 1, 0 => fun h => False.elim (h rfl)
  | 1, 1 => fun h => False.elim (h rfl)
  | 1, 2 => fun _ => by simp [embedSelfDual, embedAntiSelfDual]
  | 1, 3 => fun _ => by simp [embedSelfDual, embedAntiSelfDual]
  | 2, 0 => fun _ => by simp [embedSelfDual, embedAntiSelfDual]
  | 2, 1 => fun _ => by simp [embedSelfDual, embedAntiSelfDual]
  | 2, 2 => fun h => False.elim (h rfl)
  | 2, 3 => fun h => False.elim (h rfl)
  | 3, 0 => fun _ => by simp [embedSelfDual, embedAntiSelfDual]
  | 3, 1 => fun _ => by simp [embedSelfDual, embedAntiSelfDual]
  | 3, 2 => fun h => False.elim (h rfl)
  | 3, 3 => fun h => False.elim (h rfl)

/-- 🟡 KINEMATIC: Dirac Parity (Hestenes Mapping) -/
theorem kinematicDiracEquation (u : Universe) :
  ∀ (m : Complex) (x : SpacetimePoint),
    isOdd (diracOperatorCore (fun mu p => extractSpinorDeriv u p mu) x) ∧ 
    isOdd (m • (extractSpinorMode u x * gamma0)) := by
  intros m x
  have h_even_psi : ∀ p, isEven (extractSpinorMode u p) := by
    intro p; unfold extractSpinorMode Universe.spin4c_connection; exact isEven_embedSelfDual_add_embedAntiSelfDual (u.sd_sector 0 p) (u.asd_sector 0 p)
  have h_even_dpsi : ∀ mu p, isEven (extractSpinorDeriv u p mu) := by
    intros mu p; unfold extractSpinorDeriv partialDerivChiral; exact isEven_embedSelfDual_add_embedAntiSelfDual _ _
  constructor
  · intros i j hij
    unfold diracOperatorCore
    change (∑ mu, (gammaVec mu * extractSpinorDeriv u x mu) i j) = 0
    apply Finset.sum_eq_zero
    intro mu _
    have h_odd : isOdd (gammaVec mu * extractSpinorDeriv u x mu) := by
      apply odd_mul_even
      · exact hestenesIsomorphism mu
      · exact h_even_dpsi mu x
    exact h_odd i j hij
  · intros i j hij
    have : (m • (extractSpinorMode u x * gamma0)) i j = m * (extractSpinorMode u x * gamma0) i j := rfl
    rw [this]
    have h_odd : isOdd (extractSpinorMode u x * gamma0) := by
      apply even_mul_odd
      · exact h_even_psi x
      · exact is_odd_gamma0
    have hz : (extractSpinorMode u x * gamma0) i j = 0 := h_odd i j hij
    rw [hz, mul_zero]

end CGD.Quantum

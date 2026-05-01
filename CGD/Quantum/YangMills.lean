-- FILENAME: CGD/Quantum/YangMills.lean

import Litlib.Core
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Math
import CGD.Particles.Definitions
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations CGD.Particles Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Quantum

Litlib.theorem
  description "Yang-Mills Chaos Bound"
/--
Evaluates the chaotic non-linear self-interaction of the homogenous gauge field ansatz.
-/
theorem kinematicYangMillsChaos (u : Universe) :
  ∀ (x : SpacetimePoint),
    Matrix.trace (⁅homogeneousChaosAnsatz 1 x, homogeneousChaosAnsatz 2 x⁆.val *
                  ⁅homogeneousChaosAnsatz 1 x, homogeneousChaosAnsatz 2 x⁆.val) =
    -8 * (x 1 : ℂ)^2 * (x 2 : ℂ)^2 := by
  intro x
  unfold homogeneousChaosAnsatz
  have h1 : (if (1 : Fin 4) = 1 then (Complex.I * ↑(x 1)) • sigma1 else if (1 : Fin 4) = 2 then (Complex.I * ↑(x 2)) • sigma2 else 0) = (Complex.I * ↑(x 1)) • sigma1 := by exact if_pos rfl
  have h2 : (if (2 : Fin 4) = 1 then (Complex.I * ↑(x 1)) • sigma1 else if (2 : Fin 4) = 2 then (Complex.I * ↑(x 2)) • sigma2 else 0) = (Complex.I * ↑(x 2)) • sigma2 := by
    have h_neq : (2 : Fin 4) ≠ 1 := by decide
    rw [if_neg h_neq, if_pos rfl]
  rw [h1, h2]
  have hb : ⁅(Complex.I * ↑(x 1)) • sigma1, (Complex.I * ↑(x 2)) • sigma2⁆.val = 
            ((Complex.I * ↑(x 1)) * (Complex.I * ↑(x 2))) • (sigma1.val * sigma2.val - sigma2.val * sigma1.val) := by
    change ((Complex.I * ↑(x 1)) • sigma1.val) * ((Complex.I * ↑(x 2)) • sigma2.val) - ((Complex.I * ↑(x 2)) • sigma2.val) * ((Complex.I * ↑(x 1)) • sigma1.val) = _
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have h_comm_C : (Complex.I * ↑(x 2)) * (Complex.I * ↑(x 1)) = (Complex.I * ↑(x 1)) * (Complex.I * ↑(x 2)) := by ring
    rw [h_comm_C, ← smul_sub]
  rw [hb]
  have h_mat_smul (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) : (c • M) * (c • M) = (c^2) • (M * M) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
  rw [h_mat_smul]
  have h_trace_smul (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace (c • M) = c * Matrix.trace M := by
    unfold Matrix.trace Matrix.diag
    rw [sum_fin_2_expand]
    simp only [Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [h_trace_smul]
  have hc_sq : ((Complex.I * ↑(x 1)) * (Complex.I * ↑(x 2)))^2 = (↑(x 1))^2 * (↑(x 2))^2 := by
    calc ((Complex.I * ↑(x 1)) * (Complex.I * ↑(x 2)))^2
      _ = Complex.I^2 * Complex.I^2 * (x 1)^2 * (x 2)^2 := by ring
      _ = (-1) * (-1) * (x 1)^2 * (x 2)^2 := by rw [Complex.I_sq]
      _ = (x 1)^2 * (x 2)^2 := by ring
  rw [hc_sq]
  have h_trace_8 : Matrix.trace ((sigma1.val * sigma2.val - sigma2.val * sigma1.val) * (sigma1.val * sigma2.val - sigma2.val * sigma1.val)) = -8 := by
    rw [val_sigma1, val_sigma2]
    have eq_comm : sigmaX * sigmaY - sigmaY * sigmaX = (2 * Complex.I) • sigmaZ := by
      ext i j
      unfold sigmaX sigmaY sigmaZ mkMat
      fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply, Matrix.mul_apply, sum_fin_2_expand, Matrix.smul_apply] <;> ring
    rw [eq_comm]
    have eq_sq : ((2 * Complex.I) • sigmaZ) * ((2 * Complex.I) • sigmaZ) = (2 * Complex.I)^2 • (sigmaZ * sigmaZ) := by
      ext i j; simp [Matrix.mul_apply, sum_fin_2_expand, Matrix.smul_apply]; ring
    rw [eq_sq]
    have eq_z_sq : sigmaZ * sigmaZ = 1 := by
      ext i j
      unfold sigmaZ mkMat
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, sum_fin_2_expand, Matrix.one_apply] <;> ring
    rw [eq_z_sq]
    have eq_tr : Matrix.trace ((2 * Complex.I) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = (2 * Complex.I)^2 * 2 := by
      unfold Matrix.trace Matrix.diag
      simp [sum_fin_2_expand, Matrix.smul_apply, Matrix.one_apply]
      ring
    rw [eq_tr]
    calc (2 * Complex.I) ^ 2 * 2 = 4 * Complex.I ^ 2 * 2 := by ring
      _ = 4 * (-1) * 2 := by rw [Complex.I_sq]
      _ = -8 := by ring
  rw [h_trace_8]
  ring

end CGD.Quantum

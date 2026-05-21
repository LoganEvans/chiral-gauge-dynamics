-- FILENAME: CGD/Foundations/TensorCalculus/GaugeTransform/AlgebraHelpers.lean

import Litlib.Core
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option linter.unusedSimpArgs false

open Matrix Complex BigOperators

namespace CGD.Foundations

lemma matrix_gauge_mul (U V A_mu A_nu dV_mu dV_nu dU_mu : Matrix (Fin 2) (Fin 2) ℂ)
  (hVU : V * U = 1) (hdV : U * dV_mu = - dU_mu * V) :
  (U * A_mu * V + U * dV_mu) * (U * A_nu * V + U * dV_nu) =
  U * (A_mu * A_nu) * V + U * A_mu * dV_nu - dU_mu * A_nu * V - dU_mu * dV_nu := by
  simp only [add_mul, mul_add]
  have h1 : U * A_mu * V * (U * A_nu * V) = U * (A_mu * A_nu) * V := by
    calc U * A_mu * V * (U * A_nu * V)
      _ = U * A_mu * (V * U) * A_nu * V := by simp only [Matrix.mul_assoc]
      _ = U * A_mu * 1 * A_nu * V := by rw [hVU]
      _ = U * (A_mu * A_nu) * V := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  have h2 : U * A_mu * V * (U * dV_nu) = U * A_mu * dV_nu := by
    calc U * A_mu * V * (U * dV_nu)
      _ = U * A_mu * (V * U) * dV_nu := by simp only [Matrix.mul_assoc]
      _ = U * A_mu * 1 * dV_nu := by rw [hVU]
      _ = U * A_mu * dV_nu := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  have h3 : U * dV_mu * (U * A_nu * V) = - (dU_mu * A_nu * V) := by
    calc U * dV_mu * (U * A_nu * V)
      _ = (U * dV_mu) * U * A_nu * V := by simp only [Matrix.mul_assoc]
      _ = (- dU_mu * V) * U * A_nu * V := by rw [hdV]
      _ = - (dU_mu * V) * U * A_nu * V := by simp only [neg_mul]
      _ = - (dU_mu * (V * U) * A_nu * V) := by simp only [neg_mul, Matrix.mul_assoc]
      _ = - (dU_mu * 1 * A_nu * V) := by rw [hVU]
      _ = - (dU_mu * A_nu * V) := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  have h4 : U * dV_mu * (U * dV_nu) = - (dU_mu * dV_nu) := by
    calc U * dV_mu * (U * dV_nu)
      _ = (U * dV_mu) * U * dV_nu := by simp only [Matrix.mul_assoc]
      _ = (- dU_mu * V) * U * dV_nu := by rw [hdV]
      _ = - (dU_mu * V) * U * dV_nu := by simp only [neg_mul]
      _ = - (dU_mu * (V * U) * dV_nu) := by simp only [neg_mul, Matrix.mul_assoc]
      _ = - (dU_mu * 1 * dV_nu) := by rw [hVU]
      _ = - (dU_mu * dV_nu) := by simp only [Matrix.mul_one]
  rw [h1, h2, h3, h4]
  simp only [sub_eq_add_neg, neg_mul]
  abel

lemma gauge_algebra_simplify (U V A_mu A_nu dA_nu dU_mu dV_mu dV_nu ddV : Matrix (Fin 2) (Fin 2) ℂ) :
  (dU_mu * A_nu * V + U * dA_nu * V + U * A_nu * dV_mu + (dU_mu * dV_nu + U * ddV)) +
  (U * (A_mu * A_nu) * V + U * A_mu * dV_nu - dU_mu * A_nu * V - dU_mu * dV_nu)
  =
  U * dA_nu * V + U * A_nu * dV_mu + U * ddV + U * (A_mu * A_nu) * V + U * A_mu * dV_nu := by
  abel

lemma gauge_algebra_antisymm (U V dA_nu dA_mu dV_mu dV_nu ddV A_mu A_nu : Matrix (Fin 2) (Fin 2) ℂ) :
  (U * dA_nu * V + U * A_nu * dV_mu + U * ddV + U * (A_mu * A_nu) * V + U * A_mu * dV_nu) -
  (U * dA_mu * V + U * A_mu * dV_nu + U * ddV + U * (A_nu * A_mu) * V + U * A_nu * dV_mu)
  =
  U * (dA_nu - dA_mu + (A_mu * A_nu - A_nu * A_mu)) * V := by
  simp only [mul_add, add_mul, mul_sub, sub_mul]
  abel

end CGD.Foundations

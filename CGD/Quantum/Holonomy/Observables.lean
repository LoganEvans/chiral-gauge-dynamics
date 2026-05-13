-- FILENAME: CGD/Quantum/Holonomy/Observables.lean

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import CGD.Quantum.Holonomy.Basic
import CGD.Quantum.Holonomy.Pauli
import CGD.Foundations.GaugeGroup

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations Matrix Complex BigOperators

namespace CGD.Quantum

noncomputable def obs_M (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.cos (θ:ℂ)) • sigma3.val + (Complex.sin (θ:ℂ)) • sigma1.val

noncomputable def obs_integral (θ : ℝ) (t0 t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I * ((t:ℂ) - (t0:ℂ))) • obs_M θ

lemma M_sq (θ : ℝ) :
  obs_M θ * obs_M θ = 1 := by
  unfold obs_M
  ext i j
  fin_cases i <;> fin_cases j
  · simp [sigma1_val_eq_mat, sigma3_val_eq_mat, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    have h1 : Complex.cos ↑θ * Complex.cos ↑θ = Complex.cos ↑θ ^ 2 := by ring
    have h2 : Complex.sin ↑θ * Complex.sin ↑θ = Complex.sin ↑θ ^ 2 := by ring
    rw [h1, h2, add_comm]
    exact Complex.sin_sq_add_cos_sq (θ:ℂ)
  · simp [sigma1_val_eq_mat, sigma3_val_eq_mat, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    ring
  · simp [sigma1_val_eq_mat, sigma3_val_eq_mat, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    ring
  · simp [sigma1_val_eq_mat, sigma3_val_eq_mat, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    have h1 : Complex.sin ↑θ * Complex.sin ↑θ = Complex.sin ↑θ ^ 2 := by ring
    have h2 : Complex.cos ↑θ * Complex.cos ↑θ = Complex.cos ↑θ ^ 2 := by ring
    rw [h1, h2]
    exact Complex.sin_sq_add_cos_sq (θ:ℂ)

lemma hol_toSl2c_val_eq (M : Matrix (Fin 2) (Fin 2) ℂ) (h_tr : Matrix.trace M = 0) : (toSl2c M).val = M := by
  unfold toSl2c; dsimp
  rw [h_tr]
  have hz : (0:ℂ) / 2 = 0 := by ring
  rw [hz, zero_smul, sub_zero]

lemma trace_obs_M (θ : ℝ) : Matrix.trace (Complex.I • obs_M θ) = 0 := by
  have h_sigma3_tr : Matrix.trace sigma3.val = 0 := trace_sigma3
  have h_sigma1_tr : Matrix.trace sigma1.val = 0 := trace_sigma1
  unfold obs_M
  have h_mul : Complex.I • (Complex.cos ↑θ • sigma3.val + Complex.sin ↑θ • sigma1.val) =
    (Complex.I * Complex.cos ↑θ) • sigma3.val + (Complex.I * Complex.sin ↑θ) • sigma1.val := by
    ext i j; simp [Matrix.add_apply, Matrix.smul_apply]; ring
  rw [h_mul]
  have h_tr : Matrix.trace ((Complex.I * Complex.cos ↑θ) • sigma3.val + (Complex.I * Complex.sin ↑θ) • sigma1.val) =
    (Complex.I * Complex.cos ↑θ) * Matrix.trace sigma3.val + (Complex.I * Complex.sin ↑θ) * Matrix.trace sigma1.val := by
    simp [Matrix.trace, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply]; ring
  rw [h_tr, h_sigma3_tr, h_sigma1_tr]
  ring

lemma toSl2c_obs_M (θ : ℝ) : (toSl2c (Complex.I • obs_M θ)).val = Complex.I • obs_M θ :=
  hol_toSl2c_val_eq _ (trace_obs_M θ)

lemma R_sigma3_Rinv_eq_obs_M (θ : ℝ) :
  Matrix.of ![![Complex.cos ↑(θ / 2), -Complex.sin ↑(θ / 2)], ![Complex.sin ↑(θ / 2), Complex.cos ↑(θ / 2)]] *
  (Complex.I • sigma3.val) *
  Matrix.of ![![Complex.cos ↑(θ / 2), Complex.sin ↑(θ / 2)], ![-Complex.sin ↑(θ / 2), Complex.cos ↑(θ / 2)]] = Complex.I • obs_M θ := by
  
  let R := Matrix.of ![![Complex.cos ↑(θ / 2), -Complex.sin ↑(θ / 2)], ![Complex.sin ↑(θ / 2), Complex.cos ↑(θ / 2)]]
  have hR00 : R 0 0 = Complex.cos ↑(θ / 2) := rfl
  have hR01 : R 0 1 = -Complex.sin ↑(θ / 2) := rfl
  have hR10 : R 1 0 = Complex.sin ↑(θ / 2) := rfl
  have hR11 : R 1 1 = Complex.cos ↑(θ / 2) := rfl

  let M := Complex.I • sigma3.val
  have hM00 : M 0 0 = Complex.I := by 
    have h : sigma3.val 0 0 = 1 := by rw [sigma3_val_eq_mat]; rfl
    calc M 0 0 = Complex.I * sigma3.val 0 0 := rfl
    _ = Complex.I * 1 := by rw [h]
    _ = Complex.I := mul_one _
  
  have hM01 : M 0 1 = 0 := by 
    have h : sigma3.val 0 1 = 0 := by rw [sigma3_val_eq_mat]; rfl
    calc M 0 1 = Complex.I * sigma3.val 0 1 := rfl
    _ = Complex.I * 0 := by rw [h]
    _ = 0 := mul_zero _

  have hM10 : M 1 0 = 0 := by 
    have h : sigma3.val 1 0 = 0 := by rw [sigma3_val_eq_mat]; rfl
    calc M 1 0 = Complex.I * sigma3.val 1 0 := rfl
    _ = Complex.I * 0 := by rw [h]
    _ = 0 := mul_zero _

  have hM11 : M 1 1 = -Complex.I := by 
    have h : sigma3.val 1 1 = -1 := by rw [sigma3_val_eq_mat]; rfl
    calc M 1 1 = Complex.I * sigma3.val 1 1 := rfl
    _ = Complex.I * -1 := by rw [h]
    _ = -Complex.I := mul_neg_one _

  let Rinv := Matrix.of ![![Complex.cos ↑(θ / 2), Complex.sin ↑(θ / 2)], ![-Complex.sin ↑(θ / 2), Complex.cos ↑(θ / 2)]]
  have hRinv00 : Rinv 0 0 = Complex.cos ↑(θ / 2) := rfl
  have hRinv01 : Rinv 0 1 = Complex.sin ↑(θ / 2) := rfl
  have hRinv10 : Rinv 1 0 = -Complex.sin ↑(θ / 2) := rfl
  have hRinv11 : Rinv 1 1 = Complex.cos ↑(θ / 2) := rfl

  let RM := R * M
  
  have hRM00 : RM 0 0 = Complex.cos ↑(θ / 2) * Complex.I := by
    calc RM 0 0 = R 0 0 * M 0 0 + R 0 1 * M 1 0 := matrix_mul_2x2_00 _ _
    _ = Complex.cos ↑(θ / 2) * Complex.I + (-Complex.sin ↑(θ / 2)) * 0 := by rw [hR00, hM00, hR01, hM10]
    _ = Complex.cos ↑(θ / 2) * Complex.I := by ring

  have hRM01 : RM 0 1 = Complex.sin ↑(θ / 2) * Complex.I := by
    calc RM 0 1 = R 0 0 * M 0 1 + R 0 1 * M 1 1 := matrix_mul_2x2_01 _ _
    _ = Complex.cos ↑(θ / 2) * 0 + (-Complex.sin ↑(θ / 2)) * (-Complex.I) := by rw [hR00, hM01, hR01, hM11]
    _ = Complex.sin ↑(θ / 2) * Complex.I := by ring

  have hRM10 : RM 1 0 = Complex.sin ↑(θ / 2) * Complex.I := by
    calc RM 1 0 = R 1 0 * M 0 0 + R 1 1 * M 1 0 := matrix_mul_2x2_10 _ _
    _ = Complex.sin ↑(θ / 2) * Complex.I + Complex.cos ↑(θ / 2) * 0 := by rw [hR10, hM00, hR11, hM10]
    _ = Complex.sin ↑(θ / 2) * Complex.I := by ring

  have hRM11 : RM 1 1 = -Complex.cos ↑(θ / 2) * Complex.I := by
    calc RM 1 1 = R 1 0 * M 0 1 + R 1 1 * M 1 1 := matrix_mul_2x2_11 _ _
    _ = Complex.sin ↑(θ / 2) * 0 + Complex.cos ↑(θ / 2) * (-Complex.I) := by rw [hR10, hM01, hR11, hM11]
    _ = -Complex.cos ↑(θ / 2) * Complex.I := by ring

  let RMRinv := RM * Rinv

  have hRMRinv00 : RMRinv 0 0 = Complex.I * (Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2)) := by
    calc RMRinv 0 0 = RM 0 0 * Rinv 0 0 + RM 0 1 * Rinv 1 0 := matrix_mul_2x2_00 _ _
    _ = (Complex.cos ↑(θ / 2) * Complex.I) * Complex.cos ↑(θ / 2) + (Complex.sin ↑(θ / 2) * Complex.I) * (-Complex.sin ↑(θ / 2)) := by rw [hRM00, hRinv00, hRM01, hRinv10]
    _ = Complex.I * (Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2)) := by ring

  have hRMRinv01 : RMRinv 0 1 = Complex.I * (Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2)) := by
    calc RMRinv 0 1 = RM 0 0 * Rinv 0 1 + RM 0 1 * Rinv 1 1 := matrix_mul_2x2_01 _ _
    _ = (Complex.cos ↑(θ / 2) * Complex.I) * Complex.sin ↑(θ / 2) + (Complex.sin ↑(θ / 2) * Complex.I) * Complex.cos ↑(θ / 2) := by rw [hRM00, hRinv01, hRM01, hRinv11]
    _ = Complex.I * (Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2)) := by ring

  have hRMRinv10 : RMRinv 1 0 = Complex.I * (Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) + Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2)) := by
    calc RMRinv 1 0 = RM 1 0 * Rinv 0 0 + RM 1 1 * Rinv 1 0 := matrix_mul_2x2_10 _ _
    _ = (Complex.sin ↑(θ / 2) * Complex.I) * Complex.cos ↑(θ / 2) + (-Complex.cos ↑(θ / 2) * Complex.I) * (-Complex.sin ↑(θ / 2)) := by rw [hRM10, hRinv00, hRM11, hRinv10]
    _ = Complex.I * (Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) + Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2)) := by ring

  have hRMRinv11 : RMRinv 1 1 = -Complex.I * (Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2)) := by
    calc RMRinv 1 1 = RM 1 0 * Rinv 0 1 + RM 1 1 * Rinv 1 1 := matrix_mul_2x2_11 _ _
    _ = (Complex.sin ↑(θ / 2) * Complex.I) * Complex.sin ↑(θ / 2) + (-Complex.cos ↑(θ / 2) * Complex.I) * Complex.cos ↑(θ / 2) := by rw [hRM10, hRinv01, hRM11, hRinv11]
    _ = -Complex.I * (Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2)) := by ring

  have h_cos_eq := complex_double_angle_cos θ
  have h_sin_eq := complex_double_angle_sin θ

  have hRMRinv00_final : RMRinv 0 0 = Complex.I * Complex.cos ↑θ := by
    calc RMRinv 0 0 = Complex.I * (Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2)) := hRMRinv00
    _ = Complex.I * Complex.cos ↑θ := by rw [h_cos_eq]

  have hRMRinv01_final : RMRinv 0 1 = Complex.I * Complex.sin ↑θ := by
    calc RMRinv 0 1 = Complex.I * (Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2)) := hRMRinv01
    _ = Complex.I * Complex.sin ↑θ := by rw [h_sin_eq]

  have hRMRinv10_final : RMRinv 1 0 = Complex.I * Complex.sin ↑θ := by
    have eq_symm : Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) + Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) = Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) := by ring
    calc RMRinv 1 0 = Complex.I * (Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) + Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2)) := hRMRinv10
    _ = Complex.I * (Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2)) := by rw [eq_symm]
    _ = Complex.I * Complex.sin ↑θ := by rw [h_sin_eq]

  have hRMRinv11_final : RMRinv 1 1 = -Complex.I * Complex.cos ↑θ := by
    calc RMRinv 1 1 = -Complex.I * (Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2)) := hRMRinv11
    _ = -Complex.I * Complex.cos ↑θ := by rw [h_cos_eq]

  have hTarget00 : (Complex.I • obs_M θ) 0 0 = Complex.I * Complex.cos ↑θ := by
    have hs3 : sigma3.val 0 0 = 1 := by rw [sigma3_val_eq_mat]; rfl
    have hs1 : sigma1.val 0 0 = 0 := by rw [sigma1_val_eq_mat]; rfl
    have h_obs : obs_M θ 0 0 = Complex.cos ↑θ := by
      calc obs_M θ 0 0 = (Complex.cos ↑θ) * sigma3.val 0 0 + (Complex.sin ↑θ) * sigma1.val 0 0 := rfl
      _ = (Complex.cos ↑θ) * 1 + (Complex.sin ↑θ) * 0 := by rw [hs3, hs1]
      _ = Complex.cos ↑θ := by ring
    calc (Complex.I • obs_M θ) 0 0 = Complex.I * obs_M θ 0 0 := rfl
    _ = Complex.I * Complex.cos ↑θ := by rw [h_obs]

  have hTarget01 : (Complex.I • obs_M θ) 0 1 = Complex.I * Complex.sin ↑θ := by
    have hs3 : sigma3.val 0 1 = 0 := by rw [sigma3_val_eq_mat]; rfl
    have hs1 : sigma1.val 0 1 = 1 := by rw [sigma1_val_eq_mat]; rfl
    have h_obs : obs_M θ 0 1 = Complex.sin ↑θ := by
      calc obs_M θ 0 1 = (Complex.cos ↑θ) * sigma3.val 0 1 + (Complex.sin ↑θ) * sigma1.val 0 1 := rfl
      _ = (Complex.cos ↑θ) * 0 + (Complex.sin ↑θ) * 1 := by rw [hs3, hs1]
      _ = Complex.sin ↑θ := by ring
    calc (Complex.I • obs_M θ) 0 1 = Complex.I * obs_M θ 0 1 := rfl
    _ = Complex.I * Complex.sin ↑θ := by rw [h_obs]

  have hTarget10 : (Complex.I • obs_M θ) 1 0 = Complex.I * Complex.sin ↑θ := by
    have hs3 : sigma3.val 1 0 = 0 := by rw [sigma3_val_eq_mat]; rfl
    have hs1 : sigma1.val 1 0 = 1 := by rw [sigma1_val_eq_mat]; rfl
    have h_obs : obs_M θ 1 0 = Complex.sin ↑θ := by
      calc obs_M θ 1 0 = (Complex.cos ↑θ) * sigma3.val 1 0 + (Complex.sin ↑θ) * sigma1.val 1 0 := rfl
      _ = (Complex.cos ↑θ) * 0 + (Complex.sin ↑θ) * 1 := by rw [hs3, hs1]
      _ = Complex.sin ↑θ := by ring
    calc (Complex.I • obs_M θ) 1 0 = Complex.I * obs_M θ 1 0 := rfl
    _ = Complex.I * Complex.sin ↑θ := by rw [h_obs]

  have hTarget11 : (Complex.I • obs_M θ) 1 1 = -Complex.I * Complex.cos ↑θ := by
    have hs3 : sigma3.val 1 1 = -1 := by rw [sigma3_val_eq_mat]; rfl
    have hs1 : sigma1.val 1 1 = 0 := by rw [sigma1_val_eq_mat]; rfl
    have h_obs : obs_M θ 1 1 = -Complex.cos ↑θ := by
      calc obs_M θ 1 1 = (Complex.cos ↑θ) * sigma3.val 1 1 + (Complex.sin ↑θ) * sigma1.val 1 1 := rfl
      _ = (Complex.cos ↑θ) * -1 + (Complex.sin ↑θ) * 0 := by rw [hs3, hs1]
      _ = -Complex.cos ↑θ := by ring
    calc (Complex.I • obs_M θ) 1 1 = Complex.I * obs_M θ 1 1 := rfl
    _ = Complex.I * (-Complex.cos ↑θ) := by rw [h_obs]
    _ = -Complex.I * Complex.cos ↑θ := by ring

  have h_eq : R * M * Rinv = RMRinv := rfl
  rw [h_eq]
  ext i j
  fin_cases i <;> fin_cases j
  · exact Eq.trans hRMRinv00_final (Eq.symm hTarget00)
  · exact Eq.trans hRMRinv01_final (Eq.symm hTarget01)
  · exact Eq.trans hRMRinv10_final (Eq.symm hTarget10)
  · exact Eq.trans hRMRinv11_final (Eq.symm hTarget11)

lemma obs_integral_eval (θ : ℝ) :
  obs_integral θ 0 (Real.pi / 2) = (Complex.I * (Real.pi / 2 : ℂ)) • obs_M θ := by
  unfold obs_integral
  
  have h_div : (↑(Real.pi / 2) : ℂ) = ↑Real.pi / 2 := by
    have h2 : (2 : ℂ) = ↑(2 : ℝ) := rfl
    rw [h2, ← Complex.ofReal_div]
  
  have hz : (↑(0 : ℝ) : ℂ) = 0 := Complex.ofReal_zero
  
  calc (Complex.I * (↑(Real.pi / 2) - ↑(0 : ℝ))) • obs_M θ
    _ = (Complex.I * (↑Real.pi / 2 - 0)) • obs_M θ := by rw [h_div, hz]
    _ = (Complex.I * (↑Real.pi / 2)) • obs_M θ := by rw [sub_zero]

end CGD.Quantum

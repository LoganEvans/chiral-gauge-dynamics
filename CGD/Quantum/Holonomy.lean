-- FILENAME: CGD/Quantum/Holonomy.lean

import Litlib.Core
import CGD.Quantum.Definitions
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.MeanValue
import Litlib.Y2000.hall2000elementary.Signature

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms
open Litlib.Y2000.hall2000elementary

namespace CGD.Quantum

def straightLinePath (t : ℝ) : SpacetimePoint := fun i => if i = 1 then t else 0

lemma straightLinePath_prop (t : ℝ) : straightLinePath t 1 = t ∧ straightLinePath t 0 = 0 ∧ straightLinePath t 2 = 0 ∧ straightLinePath t 3 = 0 := by
  unfold straightLinePath
  have h0 : (0 : Fin 4) ≠ 1 := by decide
  have h1 : (1 : Fin 4) = 1 := rfl
  have h2 : (2 : Fin 4) ≠ 1 := by decide
  have h3 : (3 : Fin 4) ≠ 1 := by decide
  simp [h0, h1, h2, h3]

lemma sigma1_val_eq_mat : sigma1.val = Matrix.of ![![0, 1], ![1, 0]] := by rw [val_sigma1]; rfl
lemma sigma3_val_eq_mat : sigma3.val = Matrix.of ![![1, 0], ![0, -1]] := by rw [val_sigma3]; rfl

noncomputable def bellCorrelationDeg (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (1 / 2 : ℂ) * Matrix.trace (A * B)

lemma pauli_algebra_sigma1_sq : sigma1.val ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  rw [sigma1_val_eq_mat]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

lemma M_sq (θ : ℝ) :
  ((Complex.cos (θ:ℂ)) • sigma3.val + (Complex.sin (θ:ℂ)) • sigma1.val) * 
  ((Complex.cos (θ:ℂ)) • sigma3.val + (Complex.sin (θ:ℂ)) • sigma1.val) = 1 := by
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

lemma hasDerivAt_ofReal (t : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
  have h1 := hasDerivAt_id t
  have h2 := HasDerivAt.smul_const h1 (1 : ℂ)
  have eq1 : (fun (y : ℝ) => id y • (1 : ℂ)) = fun (s : ℝ) => (s : ℂ) := by ext x; simp
  have eq2 : (1 : ℝ) • (1 : ℂ) = 1 := by simp
  rw [eq1, eq2] at h2
  exact h2

lemma scalar_integral_deriv (t0 t : ℝ) :
  HasDerivAt (fun s : ℝ => Complex.I * ((s:ℂ) - (t0:ℂ))) Complex.I t := by
  have hd1 : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 t := hasDerivAt_ofReal t
  have hd2 : HasDerivAt (fun s : ℝ => (s:ℂ) - (t0:ℂ)) 1 t := hd1.sub_const (t0:ℂ)
  have hd3 := HasDerivAt.const_mul Complex.I hd2
  have h_eq : Complex.I * 1 = Complex.I := mul_one _
  rw [h_eq] at hd3
  exact hd3

lemma integral_t_M (M : Matrix (Fin 2) (Fin 2) ℂ) (t0 t : ℝ) :
  HasDerivAt (fun s : ℝ => (Complex.I * ((s:ℂ) - (t0:ℂ))) • M)
             (Complex.I • M) t :=
  HasDerivAt.smul_const (scalar_integral_deriv t0 t) M

lemma trace_sigma1 : Matrix.trace sigma1.val = 0 := by
  rw [sigma1_val_eq_mat]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.zero_apply]

lemma trace_sigma3 : Matrix.trace sigma3.val = 0 := by
  rw [sigma3_val_eq_mat]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.zero_apply]

lemma trace_sigma3_sigma1 : Matrix.trace (sigma3.val * sigma1.val) = 0 := by
  rw [sigma3_val_eq_mat, sigma1_val_eq_mat]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, Matrix.zero_apply]

lemma trace_sigma1_sigma3 : Matrix.trace (sigma1.val * sigma3.val) = 0 := by
  rw [sigma1_val_eq_mat, sigma3_val_eq_mat]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, Matrix.zero_apply]

lemma pauli_algebra_sigma3_sq : sigma3.val ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  rw [sigma3_val_eq_mat]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

lemma trace_sigma3_sq : Matrix.trace (sigma3.val * sigma3.val) = 2 := by
  have eq : sigma3.val * sigma3.val = 1 := by
    have h := pauli_algebra_sigma3_sq
    rw [pow_two] at h
    exact h
  rw [eq]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.one_apply]

lemma trace_sigma1_sq : Matrix.trace (sigma1.val * sigma1.val) = 2 := by
  have eq : sigma1.val * sigma1.val = 1 := by
    have h := pauli_algebra_sigma1_sq
    rw [pow_two] at h
    exact h
  rw [eq]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.one_apply]

noncomputable def obs_M (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.cos (θ:ℂ)) • sigma3.val + (Complex.sin (θ:ℂ)) • sigma1.val

noncomputable def obs_integral (θ : ℝ) (t0 t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I * ((t:ℂ) - (t0:ℂ))) • obs_M θ

lemma complex_double_angle_cos (θ : ℝ) : Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) = Complex.cos ↑θ := by
  have h_add : Real.cos (θ / 2 + θ / 2) = Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2) := Real.cos_add (θ / 2) (θ / 2)
  have hz : θ / 2 + θ / 2 = θ := by ring
  have h_subst : Real.cos (θ / 2 + θ / 2) = Real.cos θ := congr_arg Real.cos hz
  have h_real : Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2) = Real.cos θ := Eq.trans (Eq.symm h_add) h_subst
  
  have c1 : (↑(Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) = 
            (↑(Real.cos (θ / 2) * Real.cos (θ / 2)) : ℂ) - (↑(Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) := Complex.ofReal_sub _ _
  have c2 : (↑(Real.cos (θ / 2) * Real.cos (θ / 2)) : ℂ) = (↑(Real.cos (θ / 2)) : ℂ) * (↑(Real.cos (θ / 2)) : ℂ) := Complex.ofReal_mul _ _
  have c3 : (↑(Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) = (↑(Real.sin (θ / 2)) : ℂ) * (↑(Real.sin (θ / 2)) : ℂ) := Complex.ofReal_mul _ _
  
  have c4 : (↑(Real.cos (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) := Complex.ofReal_cos _
  have c4_mul : (↑(Real.cos (θ / 2)) : ℂ) * (↑(Real.cos (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) := congr_arg₂ (· * ·) c4 c4
  have c5 : (↑(Real.sin (θ / 2)) : ℂ) = Complex.sin ↑(θ / 2) := Complex.ofReal_sin _
  have c5_mul : (↑(Real.sin (θ / 2)) : ℂ) * (↑(Real.sin (θ / 2)) : ℂ) = Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) := congr_arg₂ (· * ·) c5 c5
  
  have c6 : (↑(Real.cos (θ / 2) * Real.cos (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) := Eq.trans c2 c4_mul
  have c7 : (↑(Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) = Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) := Eq.trans c3 c5_mul
  
  have c8 : (↑(Real.cos (θ / 2) * Real.cos (θ / 2)) : ℂ) - (↑(Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) := congr_arg₂ (· - ·) c6 c7
  
  have c9 : (↑(Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) := Eq.trans c1 c8
  have c10 : (↑(Real.cos θ) : ℂ) = Complex.cos ↑θ := Complex.ofReal_cos _
  
  have h_complex : (↑(Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) = ↑(Real.cos θ) := congr_arg Complex.ofReal h_real
  have h_final1 : Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) = (↑(Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) := Eq.symm c9
  have h_final2 : Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) = ↑(Real.cos θ) := Eq.trans h_final1 h_complex
  exact Eq.trans h_final2 c10

lemma complex_double_angle_sin (θ : ℝ) : Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) = Complex.sin ↑θ := by
  have h_add : Real.sin (θ / 2 + θ / 2) = Real.sin (θ / 2) * Real.cos (θ / 2) + Real.cos (θ / 2) * Real.sin (θ / 2) := Real.sin_add (θ / 2) (θ / 2)
  have hz : θ / 2 + θ / 2 = θ := by ring
  have hc : Real.sin (θ / 2) * Real.cos (θ / 2) + Real.cos (θ / 2) * Real.sin (θ / 2) = Real.cos (θ / 2) * Real.sin (θ / 2) + Real.sin (θ / 2) * Real.cos (θ / 2) := by ring
  have h_subst : Real.sin (θ / 2 + θ / 2) = Real.sin θ := congr_arg Real.sin hz
  have h_real1 : Real.sin (θ / 2) * Real.cos (θ / 2) + Real.cos (θ / 2) * Real.sin (θ / 2) = Real.sin θ := Eq.trans (Eq.symm h_add) h_subst
  have h_real : Real.cos (θ / 2) * Real.sin (θ / 2) + Real.sin (θ / 2) * Real.cos (θ / 2) = Real.sin θ := Eq.trans (Eq.symm hc) h_real1
  
  have c1 : (↑(Real.cos (θ / 2) * Real.sin (θ / 2) + Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) = 
            (↑(Real.cos (θ / 2) * Real.sin (θ / 2)) : ℂ) + (↑(Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) := Complex.ofReal_add _ _
  have c2 : (↑(Real.cos (θ / 2) * Real.sin (θ / 2)) : ℂ) = (↑(Real.cos (θ / 2)) : ℂ) * (↑(Real.sin (θ / 2)) : ℂ) := Complex.ofReal_mul _ _
  have c3 : (↑(Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) = (↑(Real.sin (θ / 2)) : ℂ) * (↑(Real.cos (θ / 2)) : ℂ) := Complex.ofReal_mul _ _
  
  have c4 : (↑(Real.cos (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) := Complex.ofReal_cos _
  have c5 : (↑(Real.sin (θ / 2)) : ℂ) = Complex.sin ↑(θ / 2) := Complex.ofReal_sin _
  have c2_mul : (↑(Real.cos (θ / 2)) : ℂ) * (↑(Real.sin (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) := congr_arg₂ (· * ·) c4 c5
  have c3_mul : (↑(Real.sin (θ / 2)) : ℂ) * (↑(Real.cos (θ / 2)) : ℂ) = Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) := congr_arg₂ (· * ·) c5 c4
  
  have c6 : (↑(Real.cos (θ / 2) * Real.sin (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) := Eq.trans c2 c2_mul
  have c7 : (↑(Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) = Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) := Eq.trans c3 c3_mul
  
  have c8 : (↑(Real.cos (θ / 2) * Real.sin (θ / 2)) : ℂ) + (↑(Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) := congr_arg₂ (· + ·) c6 c7
  have c9 : (↑(Real.cos (θ / 2) * Real.sin (θ / 2) + Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) := Eq.trans c1 c8
  
  have c10 : (↑(Real.sin θ) : ℂ) = Complex.sin ↑θ := Complex.ofReal_sin _
  
  have h_complex : (↑(Real.cos (θ / 2) * Real.sin (θ / 2) + Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) = ↑(Real.sin θ) := congr_arg Complex.ofReal h_real
  have h_final1 : Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) = (↑(Real.cos (θ / 2) * Real.sin (θ / 2) + Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) := Eq.symm c9
  have h_final2 : Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) = ↑(Real.sin θ) := Eq.trans h_final1 h_complex
  exact Eq.trans h_final2 c10

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

lemma matrix_mul_2x2_00 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 := by
  have eq : (A * B) 0 0 = ∑ k : Fin 2, A 0 k * B k 0 := rfl
  rw [eq, Fin.sum_univ_two]

lemma matrix_mul_2x2_01 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 := by
  have eq : (A * B) 0 1 = ∑ k : Fin 2, A 0 k * B k 1 := rfl
  rw [eq, Fin.sum_univ_two]

lemma matrix_mul_2x2_10 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 := by
  have eq : (A * B) 1 0 = ∑ k : Fin 2, A 1 k * B k 0 := rfl
  rw [eq, Fin.sum_univ_two]

lemma matrix_mul_2x2_11 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  have eq : (A * B) 1 1 = ∑ k : Fin 2, A 1 k * B k 1 := rfl
  rw [eq, Fin.sum_univ_two]

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

noncomputable def gen_A_path (u : Universe) (alpha : ℝ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 (fun i => if i = 1 then s else 0)).val

lemma gen_A_path_eq (u : Universe) (alpha : ℝ) (γ : ℝ → SpacetimePoint) 
  (h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0)
  (h_field : ∀ t, u.sd_sector 1 (γ t) = fluxTubeFrame 1 (γ t)) 
  (s : ℝ) : 
  gen_A_path u alpha s = Complex.I • obs_M alpha := by
  have h_gamma_s : (fun i : Fin 4 => if i = 1 then s else 0) = γ s := by
    ext k
    have h0 := (h_path s).2.1
    have h1 := (h_path s).1
    have h2 := (h_path s).2.2.1
    have h3 := (h_path s).2.2.2
    fin_cases k
    · simp [h0]
    · simp [h1]
    · simp [h2]
    · simp [h3]
  
  unfold gen_A_path
  have eq_eval : ((fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 (fun i => if i = 1 then s else 0)).val = 
                 ((fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 (γ s)).val := by
    rw [h_gamma_s]
  rw [eq_eval]
  
  unfold rotateYAxis
  have h11 : (1 : Fin 4) = 1 := rfl
  simp only [h11, ite_true]
  
  rw [h_field s]
  have h_f : fluxTubeFrame 1 (γ s) = toSl2c (Complex.I • sigma3.val) := by
    unfold fluxTubeFrame
    have h_neq : (1 : Fin 4) ≠ 0 := by decide
    have h_eq : (1 : Fin 4) = 1 := rfl
    rw [if_neg h_neq, if_pos h_eq]
  rw [h_f]

  have h_toSl2c : (toSl2c (Complex.I • sigma3.val)).val = Complex.I • sigma3.val := by
    apply hol_toSl2c_val_eq
    unfold Matrix.trace Matrix.diag
    rw [Fin.sum_univ_two]
    have h00 : (Complex.I • sigma3.val) 0 0 = Complex.I := by
      have hs : sigma3.val 0 0 = 1 := by rw [sigma3_val_eq_mat]; rfl
      calc (Complex.I • sigma3.val) 0 0 = Complex.I * sigma3.val 0 0 := rfl
      _ = Complex.I * 1 := by rw [hs]
      _ = Complex.I := mul_one _
    have h11 : (Complex.I • sigma3.val) 1 1 = -Complex.I := by
      have hs : sigma3.val 1 1 = -1 := by rw [sigma3_val_eq_mat]; rfl
      calc (Complex.I • sigma3.val) 1 1 = Complex.I * sigma3.val 1 1 := rfl
      _ = Complex.I * -1 := by rw [hs]
      _ = -Complex.I := mul_neg_one _
    rw [h00, h11]
    ring

  rw [h_toSl2c]
  
  have h_rot := R_sigma3_Rinv_eq_obs_M alpha
  
  have h_alpha_div : (↑alpha / 2 : ℂ) = ↑(alpha / 2) := by
    have h2 : (2 : ℂ) = ↑(2 : ℝ) := rfl
    rw [h2, ← Complex.ofReal_div]

  have h_cos_eq : Complex.cos (↑alpha / 2) = Complex.cos ↑(alpha / 2) := by rw [h_alpha_div]
  have h_sin_eq : Complex.sin (↑alpha / 2) = Complex.sin ↑(alpha / 2) := by rw [h_alpha_div]

  have h_R_eq : Matrix.of ![![Complex.cos (↑alpha / 2), -Complex.sin (↑alpha / 2)], ![Complex.sin (↑alpha / 2), Complex.cos (↑alpha / 2)]] =
                Matrix.of ![![Complex.cos ↑(alpha / 2), -Complex.sin ↑(alpha / 2)], ![Complex.sin ↑(alpha / 2), Complex.cos ↑(alpha / 2)]] := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact h_cos_eq
    · calc -Complex.sin (↑alpha / 2) = -(Complex.sin ↑(alpha / 2)) := by rw [h_sin_eq]
      _ = -Complex.sin ↑(alpha / 2) := rfl
    · exact h_sin_eq
    · exact h_cos_eq

  have h_Rinv_eq : Matrix.of ![![Complex.cos (↑alpha / 2), Complex.sin (↑alpha / 2)], ![-Complex.sin (↑alpha / 2), Complex.cos (↑alpha / 2)]] =
                   Matrix.of ![![Complex.cos ↑(alpha / 2), Complex.sin ↑(alpha / 2)], ![-Complex.sin ↑(alpha / 2), Complex.cos ↑(alpha / 2)]] := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact h_cos_eq
    · exact h_sin_eq
    · calc -Complex.sin (↑alpha / 2) = -(Complex.sin ↑(alpha / 2)) := by rw [h_sin_eq]
      _ = -Complex.sin ↑(alpha / 2) := rfl
    · exact h_cos_eq

  have h_inner_eq :
    Matrix.of ![![Complex.cos (↑alpha / 2), -Complex.sin (↑alpha / 2)], ![Complex.sin (↑alpha / 2), Complex.cos (↑alpha / 2)]] *
    (Complex.I • sigma3.val) *
    Matrix.of ![![Complex.cos (↑alpha / 2), Complex.sin (↑alpha / 2)], ![-Complex.sin (↑alpha / 2), Complex.cos (↑alpha / 2)]] =
    Complex.I • obs_M alpha := by
    rw [h_R_eq, h_Rinv_eq]
    exact h_rot

  have h_toSl2c_M : (toSl2c (Complex.I • obs_M alpha)).val = Complex.I • obs_M alpha := toSl2c_obs_M alpha
  
  have h_goal : (toSl2c (
    Matrix.of ![![Complex.cos (↑alpha / 2), -Complex.sin (↑alpha / 2)], ![Complex.sin (↑alpha / 2), Complex.cos (↑alpha / 2)]] *
    (Complex.I • sigma3.val) *
    Matrix.of ![![Complex.cos (↑alpha / 2), Complex.sin (↑alpha / 2)], ![-Complex.sin (↑alpha / 2), Complex.cos (↑alpha / 2)]]
  )).val = Complex.I • obs_M alpha := by
    rw [h_inner_eq]
    exact h_toSl2c_M

  exact h_goal

lemma gen_A_path_comm (u : Universe) (alpha : ℝ) (γ : ℝ → SpacetimePoint) 
  (h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0)
  (h_field : ∀ t, u.sd_sector 1 (γ t) = fluxTubeFrame 1 (γ t)) 
  (s1 s2 : ℝ) :
  gen_A_path u alpha s1 * gen_A_path u alpha s2 = gen_A_path u alpha s2 * gen_A_path u alpha s1 := by
  rw [gen_A_path_eq u alpha γ h_path h_field s1, gen_A_path_eq u alpha γ h_path h_field s2]

lemma gen_A_path_cont (u : Universe) (alpha : ℝ) (γ : ℝ → SpacetimePoint) 
  (h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0)
  (h_field : ∀ t, u.sd_sector 1 (γ t) = fluxTubeFrame 1 (γ t)) : 
  Continuous (gen_A_path u alpha) := by
  have h_eq : gen_A_path u alpha = (fun _ : ℝ => Complex.I • obs_M alpha) := by
    funext s
    exact gen_A_path_eq u alpha γ h_path h_field s
  rw [h_eq]
  exact continuous_const

lemma eval_obs
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (holonomy integral : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
  [mc : MatrixCalculus (Fin 2) matrixExp holonomy integral] 
  (u : Universe) (alpha : ℝ) (γ : ℝ → SpacetimePoint)
  (h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0)
  (h_field : ∀ t, u.sd_sector 1 (γ t) = fluxTubeFrame 1 (γ t)) :
  macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 (Real.pi / 2) =
  obs_M alpha := by
  
  let L := Real.pi / 2

  have h_hol_eq := mc.holonomySelfCommuting 
    (gen_A_path u alpha) 
    0 L 
    (gen_A_path_comm u alpha γ h_path h_field)

  have h_int_eval : integral (gen_A_path u alpha) 0 L = obs_integral alpha 0 L := by
    have hd : ∀ t, HasDerivAt (fun s => integral (gen_A_path u alpha) 0 s - obs_integral alpha 0 s) 0 t := by
      intro t
      have h1 := mc.hIntegralDeriv (gen_A_path u alpha) 0 t (gen_A_path_cont u alpha γ h_path h_field)
      have h2 : HasDerivAt (obs_integral alpha 0) (gen_A_path u alpha t) t := by
        have heq : gen_A_path u alpha t = Complex.I • obs_M alpha := gen_A_path_eq u alpha γ h_path h_field t
        rw [heq]
        exact integral_t_M (obs_M alpha) 0 t
      have h3 := HasDerivAt.sub h1 h2
      simp only [sub_self] at h3
      exact h3
    have hd_diff : Differentiable ℝ (fun s => integral (gen_A_path u alpha) 0 s - obs_integral alpha 0 s) := fun t => (hd t).differentiableAt
    have hd_zero : ∀ t, deriv (fun s => integral (gen_A_path u alpha) 0 s - obs_integral alpha 0 s) t = 0 := fun t => (hd t).deriv
    have h_eq : integral (gen_A_path u alpha) 0 L - obs_integral alpha 0 L = integral (gen_A_path u alpha) 0 0 - obs_integral alpha 0 0 :=
      is_const_of_deriv_eq_zero hd_diff hd_zero L 0
    have h_init1 := mc.hIntegralInit (gen_A_path u alpha) 0
    have h_init2 : obs_integral alpha 0 0 = 0 := by
      unfold obs_integral
      have hz : (↑(0:ℝ):ℂ) = 0 := Complex.ofReal_zero
      simp [hz]
    rw [h_init1, h_init2] at h_eq
    simp only [sub_zero] at h_eq
    exact sub_eq_zero.mp h_eq

  have h_hol_eq2 : holonomy (gen_A_path u alpha) 0 L = matrixExp (obs_integral alpha 0 L) := by
    rw [← h_int_eval]
    exact h_hol_eq

  have h_integral_eval := obs_integral_eval alpha
  have h_hol_eq3 : holonomy (gen_A_path u alpha) 0 L = matrixExp ((Complex.I * (Real.pi / 2 : ℂ)) • obs_M alpha) := by
    rw [h_integral_eval] at h_hol_eq2
    exact h_hol_eq2
  
  have h_M_sq : obs_M alpha * obs_M alpha = 1 := by
    have h_def : obs_M alpha = (Complex.cos ↑alpha) • sigma3.val + (Complex.sin ↑alpha) • sigma1.val := rfl
    rw [h_def]
    exact M_sq alpha

  have h_euler := mc.involutoryEulerFormula (obs_M alpha) h_M_sq (Real.pi / 2)
  
  have h_div : (↑(Real.pi / 2) : ℂ) = ↑Real.pi / 2 := by
    have h2 : (2 : ℂ) = ↑(2 : ℝ) := rfl
    rw [h2, ← Complex.ofReal_div]

  rw [h_div] at h_euler

  have h_cos : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
  have h_sin : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  
  have h_euler_simp : matrixExp ((Complex.I * (Real.pi / 2 : ℂ)) • obs_M alpha) = Complex.I • obs_M alpha := by
    have eq_cos : (Real.cos (Real.pi / 2) : ℂ) = ↑(Real.cos (Real.pi / 2)) := by push_cast; rfl
    rw [eq_cos, h_cos, Complex.ofReal_zero] at h_euler
    have eq_sin : (Real.sin (Real.pi / 2) : ℂ) = ↑(Real.sin (Real.pi / 2)) := by push_cast; rfl
    rw [eq_sin, h_sin, Complex.ofReal_one] at h_euler
    calc matrixExp ((Complex.I * (Real.pi / 2 : ℂ)) • obs_M alpha)
      _ = (0 : ℂ) • 1 + (Complex.I * 1) • obs_M alpha := h_euler
      _ = 0 + Complex.I • obs_M alpha := by rw [zero_smul, mul_one]
      _ = Complex.I • obs_M alpha := zero_add _

  have h_hol_eq4 : holonomy (gen_A_path u alpha) 0 L = Complex.I • obs_M alpha := Eq.trans h_hol_eq3 h_euler_simp
  
  unfold macroscopicObservable
  have h_A_path : (fun s => ((fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 (fun i => if i = 1 then s else 0)).val) = gen_A_path u alpha := by rfl
  rw [h_A_path]
  rw [h_hol_eq4]
  have h_final : (-Complex.I) • Complex.I • obs_M alpha = obs_M alpha := by
    have eq1 : (-Complex.I) • Complex.I • obs_M alpha = ((-Complex.I) * Complex.I) • obs_M alpha := by rw [smul_smul]
    rw [eq1]
    have eq2 : (-Complex.I) * Complex.I = 1 := by
      calc (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := by ring
        _ = -(-1) := by rw [Complex.I_mul_I]
        _ = 1 := by ring
    rw [eq2, one_smul]
  exact h_final

lemma bell_A1_B1 (s22 : ℂ) (A1 B1 : Matrix (Fin 2) (Fin 2) ℂ)
  (hA1 : A1 = sigma3.val) (hB1 : B1 = s22 • sigma3.val + s22 • sigma1.val) :
  bellCorrelationBell A1 B1 = -s22 := by
  unfold bellCorrelationBell
  rw [hA1, hB1]
  have h_mul : sigma3.val * (s22 • sigma3.val + s22 • sigma1.val) = s22 • (sigma3.val * sigma3.val) + s22 • (sigma3.val * sigma1.val) := by ext i j; simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply]; ring
  rw [h_mul]
  have h_trace_add : Matrix.trace (s22 • (sigma3.val * sigma3.val) + s22 • (sigma3.val * sigma1.val)) = s22 * Matrix.trace (sigma3.val * sigma3.val) + s22 * Matrix.trace (sigma3.val * sigma1.val) := by simp [Matrix.trace, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply]; ring
  rw [h_trace_add, trace_sigma3_sq, trace_sigma3_sigma1]; ring

lemma bell_A1_B2 (s22 : ℂ) (A1 B2 : Matrix (Fin 2) (Fin 2) ℂ)
  (hA1 : A1 = sigma3.val) (hB2 : B2 = s22 • sigma3.val - s22 • sigma1.val) :
  bellCorrelationBell A1 B2 = -s22 := by
  unfold bellCorrelationBell
  rw [hA1, hB2]
  have h_mul : sigma3.val * (s22 • sigma3.val - s22 • sigma1.val) = s22 • (sigma3.val * sigma3.val) - s22 • (sigma3.val * sigma1.val) := by ext i j; simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply]; ring
  rw [h_mul]
  have h_trace : Matrix.trace (s22 • (sigma3.val * sigma3.val) - s22 • (sigma3.val * sigma1.val)) = s22 * Matrix.trace (sigma3.val * sigma3.val) - s22 * Matrix.trace (sigma3.val * sigma1.val) := by simp [Matrix.trace, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply]; ring
  rw [h_trace, trace_sigma3_sq, trace_sigma3_sigma1]; ring

lemma bell_A2_B1 (s22 : ℂ) (A2 B1 : Matrix (Fin 2) (Fin 2) ℂ)
  (hA2 : A2 = sigma1.val) (hB1 : B1 = s22 • sigma3.val + s22 • sigma1.val) :
  bellCorrelationBell A2 B1 = -s22 := by
  unfold bellCorrelationBell
  rw [hA2, hB1]
  have h_mul : sigma1.val * (s22 • sigma3.val + s22 • sigma1.val) = s22 • (sigma1.val * sigma3.val) + s22 • (sigma1.val * sigma1.val) := by ext i j; simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply]; ring
  rw [h_mul]
  have h_trace : Matrix.trace (s22 • (sigma1.val * sigma3.val) + s22 • (sigma1.val * sigma1.val)) = s22 * Matrix.trace (sigma1.val * sigma3.val) + s22 * Matrix.trace (sigma1.val * sigma1.val) := by simp [Matrix.trace, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply]; ring
  rw [h_trace, trace_sigma1_sq, trace_sigma1_sigma3]; ring

lemma bell_A2_B2 (s22 : ℂ) (A2 B2 : Matrix (Fin 2) (Fin 2) ℂ)
  (hA2 : A2 = sigma1.val) (hB2 : B2 = s22 • sigma3.val - s22 • sigma1.val) :
  bellCorrelationBell A2 B2 = s22 := by
  unfold bellCorrelationBell
  rw [hA2, hB2]
  have h_mul : sigma1.val * (s22 • sigma3.val - s22 • sigma1.val) = s22 • (sigma1.val * sigma3.val) - s22 • (sigma1.val * sigma1.val) := by ext i j; simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply]; ring
  rw [h_mul]
  have h_trace : Matrix.trace (s22 • (sigma1.val * sigma3.val) - s22 • (sigma1.val * sigma1.val)) = s22 * Matrix.trace (sigma1.val * sigma3.val) - s22 * Matrix.trace (sigma1.val * sigma1.val) := by simp [Matrix.trace, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply]; ring
  rw [h_trace, trace_sigma1_sq, trace_sigma1_sigma3]; ring

Litlib.theorem
  description "Holonomic Bell Violation (Tsirelson Bound)"
/-- 
Macroscopic SU(2) string holonomies fundamentally violate classical Bell inequalities, structurally bounding at the Tsirelson limit.
-/
theorem kinematicHolonomicBellViolation 
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (holonomy integral : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
  [mc : MatrixCalculus (Fin 2) matrixExp holonomy integral] 
  (u : Universe) (D : ℝ) :
  (∀ t, u.sd_sector 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t)) →
  D > 0 →
  (CGD.Gravity.urbantkeMetric (fun m n => CGD.Foundations.curvatureSl2c u.sd_sector m n (straightLinePath 0)) 1 1).re > D →
  let L := Real.pi / 2;
  let A1 := macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) 0 mu p) 1 L;
  let A2 := macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (Real.pi / 2) mu p) 1 L;
  let B1 := macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (Real.pi / 4) mu p) 1 L;
  let B2 := macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (- (Real.pi / 4)) mu p) 1 L;
  A1^2 = 1 ∧ A2^2 = 1 ∧ B1^2 = 1 ∧ B2^2 = 1 ∧
  (chshSumBell A1 A2 B1 B2)^2 = 8 := by
  intros h_field h_D h_urb L A1 A2 B1 B2
  
  have h_path : ∀ t, straightLinePath t 1 = t ∧ straightLinePath t 0 = 0 ∧ straightLinePath t 2 = 0 ∧ straightLinePath t 3 = 0 := straightLinePath_prop

  have hA1 : A1 = sigma3.val := by
    have heval := eval_obs matrixExp holonomy integral u 0 straightLinePath h_path h_field
    change macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) 0 mu p) 1 L = _
    unfold obs_M at heval
    have h_cos : Complex.cos ↑(0 : ℝ) = 1 := by simp
    have h_sin : Complex.sin ↑(0 : ℝ) = 0 := by simp
    rw [h_cos, h_sin] at heval; simp at heval; exact heval
    
  have hA2 : A2 = sigma1.val := by
    have heval := eval_obs matrixExp holonomy integral u (Real.pi / 2) straightLinePath h_path h_field
    change macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (Real.pi / 2) mu p) 1 L = _
    unfold obs_M at heval
    have hcos : Complex.cos ↑(Real.pi / 2 : ℝ) = 0 := by
      have eq : Complex.cos ↑(Real.pi / 2 : ℝ) = ↑(Real.cos (Real.pi / 2)) := (Complex.ofReal_cos _).symm
      rw [eq, Real.cos_pi_div_two, Complex.ofReal_zero]
    have hsin : Complex.sin ↑(Real.pi / 2 : ℝ) = 1 := by
      have eq : Complex.sin ↑(Real.pi / 2 : ℝ) = ↑(Real.sin (Real.pi / 2)) := (Complex.ofReal_sin _).symm
      rw [eq, Real.sin_pi_div_two, Complex.ofReal_one]
    rw [hcos, hsin] at heval; simp at heval; exact heval

  let s22 : ℂ := ↑(Real.sqrt 2 / 2)

  have h_cos_pi4 : Complex.cos ↑(Real.pi / 4 : ℝ) = s22 := by
    have eq : Complex.cos ↑(Real.pi / 4 : ℝ) = ↑(Real.cos (Real.pi / 4)) := (Complex.ofReal_cos _).symm
    rw [eq, Real.cos_pi_div_four]

  have h_sin_pi4 : Complex.sin ↑(Real.pi / 4 : ℝ) = s22 := by
    have eq : Complex.sin ↑(Real.pi / 4 : ℝ) = ↑(Real.sin (Real.pi / 4)) := (Complex.ofReal_sin _).symm
    rw [eq, Real.sin_pi_div_four]

  have h_cos_neg_pi4 : Complex.cos ↑(- (Real.pi / 4) : ℝ) = s22 := by
    have eq : Complex.cos ↑(- (Real.pi / 4) : ℝ) = ↑(Real.cos (- (Real.pi / 4))) := (Complex.ofReal_cos _).symm
    rw [eq, Real.cos_neg, Real.cos_pi_div_four]

  have h_sin_neg_pi4 : Complex.sin ↑(- (Real.pi / 4) : ℝ) = -s22 := by
    have eq : Complex.sin ↑(- (Real.pi / 4) : ℝ) = ↑(Real.sin (- (Real.pi / 4))) := (Complex.ofReal_sin _).symm
    rw [eq, Real.sin_neg, Real.sin_pi_div_four]
    dsimp [s22]
    push_cast
    rfl

  have hB1 : B1 = s22 • sigma3.val + s22 • sigma1.val := by
    have heval := eval_obs matrixExp holonomy integral u (Real.pi / 4) straightLinePath h_path h_field
    change macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (Real.pi / 4) mu p) 1 L = _
    unfold obs_M at heval
    rw [h_cos_pi4, h_sin_pi4] at heval; exact heval

  have hB2 : B2 = s22 • sigma3.val - s22 • sigma1.val := by
    have heval := eval_obs matrixExp holonomy integral u (- (Real.pi / 4)) straightLinePath h_path h_field
    change macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (- (Real.pi / 4)) mu p) 1 L = _
    unfold obs_M at heval
    rw [h_cos_neg_pi4, h_sin_neg_pi4] at heval
    have eq_sub : s22 • sigma3.val + (-s22) • sigma1.val = s22 • sigma3.val - s22 • sigma1.val := by
      ext i j
      have h1 : (s22 • sigma3.val + (-s22) • sigma1.val) i j = s22 * sigma3.val i j + (-s22) * sigma1.val i j := by simp [Matrix.add_apply, Matrix.smul_apply]
      have h2 : (s22 • sigma3.val - s22 • sigma1.val) i j = s22 * sigma3.val i j - s22 * sigma1.val i j := by simp [Matrix.sub_apply, Matrix.smul_apply]
      rw [h1, h2]
      ring
    rw [eq_sub] at heval
    exact heval

  have hA1_sq : A1 ^ 2 = 1 := by rw [hA1]; exact pauli_algebra_sigma3_sq
  have hA2_sq : A2 ^ 2 = 1 := by rw [hA2]; exact pauli_algebra_sigma1_sq
  
  have hB1_sq : B1 ^ 2 = 1 := by
    change (macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (Real.pi / 4) mu p) 1 L) ^ 2 = 1
    rw [eval_obs matrixExp holonomy integral u (Real.pi / 4) straightLinePath h_path h_field]
    have h_pow : obs_M (Real.pi / 4) ^ 2 = obs_M (Real.pi / 4) * obs_M (Real.pi / 4) := by rw [pow_two]
    rw [h_pow]
    exact M_sq (Real.pi / 4)
    
  have hB2_sq : B2 ^ 2 = 1 := by
    change (macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (- (Real.pi / 4)) mu p) 1 L) ^ 2 = 1
    rw [eval_obs matrixExp holonomy integral u (- (Real.pi / 4)) straightLinePath h_path h_field]
    have h_pow : obs_M (-(Real.pi / 4)) ^ 2 = obs_M (-(Real.pi / 4)) * obs_M (-(Real.pi / 4)) := by rw [pow_two]
    rw [h_pow]
    exact M_sq (- (Real.pi / 4))

  have h_chsh : chshSumBell A1 A2 B1 B2 = -4 * s22 := by
    unfold chshSumBell
    rw [bell_A1_B1 s22 A1 B1 hA1 hB1, bell_A1_B2 s22 A1 B2 hA1 hB2, bell_A2_B1 s22 A2 B1 hA2 hB1, bell_A2_B2 s22 A2 B2 hA2 hB2]
    ring

  have h_sq : (chshSumBell A1 A2 B1 B2) ^ 2 = 8 := by
    rw [h_chsh]
    have h_s22_sq : s22 ^ 2 = 1 / 2 := by
      dsimp [s22]
      have h_pos : 0 ≤ (2 : ℝ) := by norm_num
      have h_sqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt h_pos
      have h_real : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 1 / 2 := by
        calc (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (Real.sqrt 2 * Real.sqrt 2) / 4 := by ring
             _ = 2 / 4 := by rw [h_sqrt]
             _ = 1 / 2 := by norm_num
      calc (↑(Real.sqrt 2 / 2) : ℂ) ^ 2 
        _ = ↑(Real.sqrt 2 / 2) * ↑(Real.sqrt 2 / 2) := by ring
        _ = ↑((Real.sqrt 2 / 2) * (Real.sqrt 2 / 2)) := by rw [← Complex.ofReal_mul]
        _ = ↑(1 / 2 : ℝ) := by rw [h_real]
        _ = 1 / 2 := by norm_num
    calc (-4 * s22) ^ 2 = 16 * (s22 ^ 2) := by ring
         _ = 16 * (1 / 2) := by rw [h_s22_sq]
         _ = 8 := by ring
  exact ⟨hA1_sq, hA2_sq, hB1_sq, hB2_sq, h_sq⟩

Litlib.theorem
  description "Singlet Correlation Emergence"
/-- 
Without the artificial twist of entanglement, the exact quantum singlet correlation (-cos(a-b)) natively emerges from the pure classical SU(2) geometry of the intact macroscopic string.
-/
theorem kinematicHolonomicDegeneracy 
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (holonomy integral : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
  [mc : MatrixCalculus (Fin 2) matrixExp holonomy integral] 
  (u : Universe) :
  ∀ (alpha beta D : ℝ),
    (∀ t, u.sd_sector 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t)) →
    D > 0 →
    (CGD.Gravity.urbantkeMetric (fun m n => CGD.Foundations.curvatureSl2c u.sd_sector m n (straightLinePath 0)) 1 1).re > D →
    let L := Real.pi / 2;
    let obs_x := macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 L;
    let obs_y := macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) beta mu p) 1 L;
    bellCorrelationDeg obs_x (- obs_y)
      = - Complex.cos ((alpha : ℂ) - (beta : ℂ)) := by
  intros alpha beta D h_field h_D h_urb L obs_x obs_y
  
  have h_path : ∀ t, straightLinePath t 1 = t ∧ straightLinePath t 0 = 0 ∧ straightLinePath t 2 = 0 ∧ straightLinePath t 3 = 0 := straightLinePath_prop
  
  have h_obs_x : obs_x = Complex.cos (alpha : ℂ) • sigma3.val + Complex.sin (alpha : ℂ) • sigma1.val := by
    change macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 L = _
    have h_eval := eval_obs matrixExp holonomy integral u alpha straightLinePath h_path h_field
    unfold obs_M at h_eval
    exact h_eval
    
  have h_obs_y : obs_y = Complex.cos (beta : ℂ) • sigma3.val + Complex.sin (beta : ℂ) • sigma1.val := by
    change macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) beta mu p) 1 L = _
    have h_eval := eval_obs matrixExp holonomy integral u beta straightLinePath h_path h_field
    unfold obs_M at h_eval
    exact h_eval

  unfold bellCorrelationDeg
  
  have h_expand : obs_x * (-obs_y) =
    (- (Complex.cos (alpha : ℂ) * Complex.cos (beta : ℂ))) • (sigma3.val * sigma3.val) +
    (- (Complex.cos (alpha : ℂ) * Complex.sin (beta : ℂ))) • (sigma3.val * sigma1.val) +
    (- (Complex.sin (alpha : ℂ) * Complex.cos (beta : ℂ))) • (sigma1.val * sigma3.val) +
    (- (Complex.sin (alpha : ℂ) * Complex.sin (beta : ℂ))) • (sigma1.val * sigma1.val) := by
    rw [h_obs_x, h_obs_y]
    ext i j; simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.neg_apply]; ring
    
  rw [h_expand]
  have h_trace_add : Matrix.trace (
    (- (Complex.cos ↑alpha * Complex.cos ↑beta)) • (sigma3.val * sigma3.val) +
    (- (Complex.cos ↑alpha * Complex.sin ↑beta)) • (sigma3.val * sigma1.val) +
    (- (Complex.sin ↑alpha * Complex.cos ↑beta)) • (sigma1.val * sigma3.val) +
    (- (Complex.sin ↑alpha * Complex.sin ↑beta)) • (sigma1.val * sigma1.val)
  ) = 
    (- (Complex.cos ↑alpha * Complex.cos ↑beta)) * Matrix.trace (sigma3.val * sigma3.val) +
    (- (Complex.cos ↑alpha * Complex.sin ↑beta)) * Matrix.trace (sigma3.val * sigma1.val) +
    (- (Complex.sin ↑alpha * Complex.cos ↑beta)) * Matrix.trace (sigma1.val * sigma3.val) +
    (- (Complex.sin ↑alpha * Complex.sin ↑beta)) * Matrix.trace (sigma1.val * sigma1.val) := by
    simp [Matrix.trace, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply]; ring
    
  rw [h_trace_add, trace_sigma3_sq, trace_sigma3_sigma1, trace_sigma1_sigma3, trace_sigma1_sq]
  
  have h_cos_sub : Complex.cos ((alpha : ℂ) - (beta : ℂ)) = Complex.cos (alpha : ℂ) * Complex.cos (beta : ℂ) + Complex.sin (alpha : ℂ) * Complex.sin (beta : ℂ) := Complex.cos_sub (alpha : ℂ) (beta : ℂ)
  
  calc (1 / 2 : ℂ) * (
         (- (Complex.cos ↑alpha * Complex.cos ↑beta)) * 2 +
         (- (Complex.cos ↑alpha * Complex.sin ↑beta)) * 0 +
         (- (Complex.sin ↑alpha * Complex.cos ↑beta)) * 0 +
         (- (Complex.sin ↑alpha * Complex.sin ↑beta)) * 2
       )
    _ = - (Complex.cos ↑alpha * Complex.cos ↑beta + Complex.sin ↑alpha * Complex.sin ↑beta) := by ring
    _ = - Complex.cos (↑alpha - ↑beta) := by rw [← h_cos_sub]

end CGD.Quantum

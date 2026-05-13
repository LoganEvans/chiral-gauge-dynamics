-- FILENAME: CGD/Quantum/Holonomy/Bell.lean

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import CGD.Quantum.Holonomy.Basic
import CGD.Quantum.Holonomy.Pauli
import CGD.Quantum.Holonomy.Observables
import CGD.Quantum.Definitions
import CGD.Foundations.GaugeGroup

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations Matrix Complex BigOperators

namespace CGD.Quantum

noncomputable def bellCorrelationDeg (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (1 / 2 : ℂ) * Matrix.trace (A * B)

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

/-- Pure matrix algebra reduction for the Tsirelson bound over the parameterized holonomy matrices. -/
lemma chsh_obs_M_violation :
  (chshSumBell (obs_M 0) (obs_M (Real.pi / 2)) (obs_M (Real.pi / 4)) (obs_M (- (Real.pi / 4))))^2 = 8 := by
  have hA1_val : obs_M 0 = sigma3.val := by
    unfold obs_M
    have hz : (↑(0:ℝ) : ℂ) = 0 := Complex.ofReal_zero
    rw [hz, Complex.cos_zero, Complex.sin_zero]
    simp
    
  have hA2_val : obs_M (Real.pi / 2) = sigma1.val := by
    unfold obs_M
    have hc : Complex.cos ↑(Real.pi / 2) = 0 := by rw [←Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
    have hs : Complex.sin ↑(Real.pi / 2) = 1 := by rw [←Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one]
    rw [hc, hs]
    simp
    
  have hB1_val : obs_M (Real.pi / 4) = (↑(Real.sqrt 2 / 2) : ℂ) • sigma3.val + (↑(Real.sqrt 2 / 2) : ℂ) • sigma1.val := by
    unfold obs_M
    have hc : Complex.cos ↑(Real.pi / 4) = ↑(Real.sqrt 2 / 2) := by rw [←Complex.ofReal_cos, Real.cos_pi_div_four]
    have hs : Complex.sin ↑(Real.pi / 4) = ↑(Real.sqrt 2 / 2) := by rw [←Complex.ofReal_sin, Real.sin_pi_div_four]
    rw [hc, hs]
    
  have hB2_val : obs_M (-(Real.pi / 4)) = (↑(Real.sqrt 2 / 2) : ℂ) • sigma3.val - (↑(Real.sqrt 2 / 2) : ℂ) • sigma1.val := by
    unfold obs_M
    have hc : Complex.cos ↑(-(Real.pi / 4)) = ↑(Real.sqrt 2 / 2) := by rw [←Complex.ofReal_cos, Real.cos_neg, Real.cos_pi_div_four]
    have hs : Complex.sin ↑(-(Real.pi / 4)) = -↑(Real.sqrt 2 / 2) := by rw [←Complex.ofReal_sin, Real.sin_neg, Real.sin_pi_div_four, Complex.ofReal_neg]
    rw [hc, hs]
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]
    ring
    
  have hb11 := bell_A1_B1 (↑(Real.sqrt 2 / 2) : ℂ) (obs_M 0) (obs_M (Real.pi / 4)) hA1_val hB1_val
  have hb12 := bell_A1_B2 (↑(Real.sqrt 2 / 2) : ℂ) (obs_M 0) (obs_M (-(Real.pi / 4))) hA1_val hB2_val
  have hb21 := bell_A2_B1 (↑(Real.sqrt 2 / 2) : ℂ) (obs_M (Real.pi / 2)) (obs_M (Real.pi / 4)) hA2_val hB1_val
  have hb22 := bell_A2_B2 (↑(Real.sqrt 2 / 2) : ℂ) (obs_M (Real.pi / 2)) (obs_M (-(Real.pi / 4))) hA2_val hB2_val
  
  unfold chshSumBell
  rw [hb11, hb12, hb21, hb22]
  
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt h2
  have h_complex_sq : (↑(Real.sqrt 2 / 2) : ℂ) * (↑(Real.sqrt 2 / 2) : ℂ) = 1 / 2 := by
    rw [←Complex.ofReal_mul]
    have h_mul : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 1 / 2 := by
      calc (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (Real.sqrt 2 * Real.sqrt 2) / 4 := by ring
      _ = 2 / 4 := by rw [hsq]
      _ = 1 / 2 := by norm_num
    rw [h_mul]
    norm_num

  calc (- (↑(Real.sqrt 2 / 2) : ℂ) + - (↑(Real.sqrt 2 / 2) : ℂ) + - (↑(Real.sqrt 2 / 2) : ℂ) - (↑(Real.sqrt 2 / 2) : ℂ)) ^ 2 
    _ = (- 4 * (↑(Real.sqrt 2 / 2) : ℂ)) ^ 2 := by ring
    _ = 16 * ((↑(Real.sqrt 2 / 2) : ℂ) * (↑(Real.sqrt 2 / 2) : ℂ)) := by ring
    _ = 16 * (1 / 2) := by rw [h_complex_sq]
    _ = 8 := by norm_num

/-- Pure matrix algebra reduction for the singlet correlation over the parameterized holonomy matrices. -/
lemma obs_M_correlation (alpha beta : ℝ) : 
  bellCorrelationDeg (obs_M alpha) (- obs_M beta) = - Complex.cos ↑(alpha - beta) := by
  unfold bellCorrelationDeg
  
  have h_neg_mul : obs_M alpha * (- obs_M beta) = - (obs_M alpha * obs_M beta) := by
    ext i j
    simp [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h_neg_mul]
  
  have h_trace_neg : Matrix.trace (- (obs_M alpha * obs_M beta)) = - Matrix.trace (obs_M alpha * obs_M beta) := by
    simp [Matrix.trace, Fin.sum_univ_two, Matrix.neg_apply]
  rw [h_trace_neg]
  
  have h_mul : obs_M alpha * obs_M beta = 
    (Complex.cos ↑alpha * Complex.cos ↑beta) • (sigma3.val * sigma3.val) + 
    (Complex.cos ↑alpha * Complex.sin ↑beta) • (sigma3.val * sigma1.val) + 
    (Complex.sin ↑alpha * Complex.cos ↑beta) • (sigma1.val * sigma3.val) + 
    (Complex.sin ↑alpha * Complex.sin ↑beta) • (sigma1.val * sigma1.val) := by
    unfold obs_M
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [h_mul]
  
  have h_trace : Matrix.trace (
    (Complex.cos ↑alpha * Complex.cos ↑beta) • (sigma3.val * sigma3.val) + 
    (Complex.cos ↑alpha * Complex.sin ↑beta) • (sigma3.val * sigma1.val) + 
    (Complex.sin ↑alpha * Complex.cos ↑beta) • (sigma1.val * sigma3.val) + 
    (Complex.sin ↑alpha * Complex.sin ↑beta) • (sigma1.val * sigma1.val)
  ) = 
    (Complex.cos ↑alpha * Complex.cos ↑beta) * Matrix.trace (sigma3.val * sigma3.val) +
    (Complex.cos ↑alpha * Complex.sin ↑beta) * Matrix.trace (sigma3.val * sigma1.val) +
    (Complex.sin ↑alpha * Complex.cos ↑beta) * Matrix.trace (sigma1.val * sigma3.val) +
    (Complex.sin ↑alpha * Complex.sin ↑beta) * Matrix.trace (sigma1.val * sigma1.val) := by
    simp [Matrix.trace, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply]
    ring
  rw [h_trace]
  
  rw [trace_sigma3_sq, trace_sigma1_sq, trace_sigma3_sigma1, trace_sigma1_sigma3]
  
  have h_cos_sub : Complex.cos (↑alpha - ↑beta) = Complex.cos ↑alpha * Complex.cos ↑beta + Complex.sin ↑alpha * Complex.sin ↑beta := Complex.cos_sub ↑alpha ↑beta
  have h_sub_real : (↑alpha - ↑beta : ℂ) = ↑(alpha - beta) := Eq.symm (Complex.ofReal_sub alpha beta)
  
  calc (1 / 2 : ℂ) * -((Complex.cos ↑alpha * Complex.cos ↑beta) * 2 +
    (Complex.cos ↑alpha * Complex.sin ↑beta) * 0 +
    (Complex.sin ↑alpha * Complex.cos ↑beta) * 0 +
    (Complex.sin ↑alpha * Complex.sin ↑beta) * 2) 
    _ = -(Complex.cos ↑alpha * Complex.cos ↑beta + Complex.sin ↑alpha * Complex.sin ↑beta) := by ring
    _ = -Complex.cos (↑alpha - ↑beta) := by rw [← h_cos_sub]
    _ = -Complex.cos ↑(alpha - beta) := by rw [h_sub_real]

end CGD.Quantum

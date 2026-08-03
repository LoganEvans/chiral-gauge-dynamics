-- FILENAME: CGD/Gravity/FLRW/Curvature.lean

import CGD.Gravity.FLRW.Derivatives

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000

open CGD.Foundations CGD.Math Complex Matrix BigOperators

namespace CGD.Gravity.FLRW

/-- Evaluates the [A_1, A_2] commutator, establishing the F_12 magnetic field component. -/
lemma flrw_L_comm_1_2 (a : ℝ → ℂ) (x : SpacetimePoint) :
  flrw_L a 1 x * flrw_L a 2 x - flrw_L a 2 x * flrw_L a 1 x = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val := by
  have h1 : flrw_L a 1 x = a (x 0) • sigma1.val := by unfold flrw_L; simp
  have h2 : flrw_L a 2 x = a (x 0) • sigma2.val := by unfold flrw_L; simp
  rw [h1, h2]
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
  fin_cases i <;> fin_cases j
  · change a (x 0) * sigma1.val 0 0 * (a (x 0) * sigma2.val 0 0) + a (x 0) * sigma1.val 0 1 * (a (x 0) * sigma2.val 1 0) - (a (x 0) * sigma2.val 0 0 * (a (x 0) * sigma1.val 0 0) + a (x 0) * sigma2.val 0 1 * (a (x 0) * sigma1.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma3.val 0 0
    simp only [hs1_00, hs1_01, hs1_10, hs2_00, hs2_01, hs2_10, hs3_00]
    ring
  · change a (x 0) * sigma1.val 0 0 * (a (x 0) * sigma2.val 0 1) + a (x 0) * sigma1.val 0 1 * (a (x 0) * sigma2.val 1 1) - (a (x 0) * sigma2.val 0 0 * (a (x 0) * sigma1.val 0 1) + a (x 0) * sigma2.val 0 1 * (a (x 0) * sigma1.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma3.val 0 1
    simp only [hs1_00, hs1_01, hs1_11, hs2_00, hs2_01, hs2_11, hs3_01]
    ring
  · change a (x 0) * sigma1.val 1 0 * (a (x 0) * sigma2.val 0 0) + a (x 0) * sigma1.val 1 1 * (a (x 0) * sigma2.val 1 0) - (a (x 0) * sigma2.val 1 0 * (a (x 0) * sigma1.val 0 0) + a (x 0) * sigma2.val 1 1 * (a (x 0) * sigma1.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma3.val 1 0
    simp only [hs1_00, hs1_10, hs1_11, hs2_00, hs2_10, hs2_11, hs3_10]
    ring
  · change a (x 0) * sigma1.val 1 0 * (a (x 0) * sigma2.val 0 1) + a (x 0) * sigma1.val 1 1 * (a (x 0) * sigma2.val 1 1) - (a (x 0) * sigma2.val 1 0 * (a (x 0) * sigma1.val 0 1) + a (x 0) * sigma2.val 1 1 * (a (x 0) * sigma1.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma3.val 1 1
    simp only [hs1_01, hs1_10, hs1_11, hs2_01, hs2_10, hs2_11, hs3_11]
    ring

/-- Evaluates the [A_2, A_3] commutator, establishing the F_23 magnetic field component. -/
lemma flrw_L_comm_2_3 (a : ℝ → ℂ) (x : SpacetimePoint) :
  flrw_L a 2 x * flrw_L a 3 x - flrw_L a 3 x * flrw_L a 2 x = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val := by
  have h2 : flrw_L a 2 x = a (x 0) • sigma2.val := by unfold flrw_L; simp
  have h3 : flrw_L a 3 x = a (x 0) • sigma3.val := by unfold flrw_L; simp
  rw [h2, h3]
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
  fin_cases i <;> fin_cases j
  · change a (x 0) * sigma2.val 0 0 * (a (x 0) * sigma3.val 0 0) + a (x 0) * sigma2.val 0 1 * (a (x 0) * sigma3.val 1 0) - (a (x 0) * sigma3.val 0 0 * (a (x 0) * sigma2.val 0 0) + a (x 0) * sigma3.val 0 1 * (a (x 0) * sigma2.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma1.val 0 0
    simp only [hs1_00, hs2_00, hs2_01, hs2_10, hs3_00, hs3_01, hs3_10]
    ring
  · change a (x 0) * sigma2.val 0 0 * (a (x 0) * sigma3.val 0 1) + a (x 0) * sigma2.val 0 1 * (a (x 0) * sigma3.val 1 1) - (a (x 0) * sigma3.val 0 0 * (a (x 0) * sigma2.val 0 1) + a (x 0) * sigma3.val 0 1 * (a (x 0) * sigma2.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma1.val 0 1
    simp only [hs1_01, hs2_00, hs2_01, hs2_11, hs3_00, hs3_01, hs3_11]
    ring
  · change a (x 0) * sigma2.val 1 0 * (a (x 0) * sigma3.val 0 0) + a (x 0) * sigma2.val 1 1 * (a (x 0) * sigma3.val 1 0) - (a (x 0) * sigma3.val 1 0 * (a (x 0) * sigma2.val 0 0) + a (x 0) * sigma3.val 1 1 * (a (x 0) * sigma2.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma1.val 1 0
    simp only [hs1_10, hs2_00, hs2_10, hs2_11, hs3_00, hs3_10, hs3_11]
    ring
  · change a (x 0) * sigma2.val 1 0 * (a (x 0) * sigma3.val 0 1) + a (x 0) * sigma2.val 1 1 * (a (x 0) * sigma3.val 1 1) - (a (x 0) * sigma3.val 1 0 * (a (x 0) * sigma2.val 0 1) + a (x 0) * sigma3.val 1 1 * (a (x 0) * sigma2.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma1.val 1 1
    simp only [hs1_11, hs2_01, hs2_10, hs2_11, hs3_01, hs3_10, hs3_11]
    ring

/-- Evaluates the [A_3, A_1] commutator, establishing the F_31 magnetic field component. -/
lemma flrw_L_comm_3_1 (a : ℝ → ℂ) (x : SpacetimePoint) :
  flrw_L a 3 x * flrw_L a 1 x - flrw_L a 1 x * flrw_L a 3 x = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val := by
  have h3 : flrw_L a 3 x = a (x 0) • sigma3.val := by unfold flrw_L; simp
  have h1 : flrw_L a 1 x = a (x 0) • sigma1.val := by unfold flrw_L; simp
  rw [h3, h1]
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases i <;> fin_cases j
  · change a (x 0) * sigma3.val 0 0 * (a (x 0) * sigma1.val 0 0) + a (x 0) * sigma3.val 0 1 * (a (x 0) * sigma1.val 1 0) - (a (x 0) * sigma1.val 0 0 * (a (x 0) * sigma3.val 0 0) + a (x 0) * sigma1.val 0 1 * (a (x 0) * sigma3.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma2.val 0 0
    simp only [hs1_00, hs1_01, hs1_10, hs2_00, hs3_00, hs3_01, hs3_10]
    ring
  · change a (x 0) * sigma3.val 0 0 * (a (x 0) * sigma1.val 0 1) + a (x 0) * sigma3.val 0 1 * (a (x 0) * sigma1.val 1 1) - (a (x 0) * sigma1.val 0 0 * (a (x 0) * sigma3.val 0 1) + a (x 0) * sigma1.val 0 1 * (a (x 0) * sigma3.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma2.val 0 1
    simp only [hs1_00, hs1_01, hs1_11, hs2_01, hs3_00, hs3_01, hs3_11]
    have h_eq : a (x 0) * 1 * (a (x 0) * 1) + a (x 0) * 0 * (a (x 0) * 0) - (a (x 0) * 0 * (a (x 0) * 0) + a (x 0) * 1 * (a (x 0) * -1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * -Complex.I := by
      calc
        a (x 0) * 1 * (a (x 0) * 1) + a (x 0) * 0 * (a (x 0) * 0) - (a (x 0) * 0 * (a (x 0) * 0) + a (x 0) * 1 * (a (x 0) * -1))
        _ = 2 * (a (x 0) * a (x 0)) := by ring
        _ = 2 * (a (x 0) * a (x 0)) * -(-1) := by ring
        _ = 2 * (a (x 0) * a (x 0)) * -(Complex.I ^ 2) := by rw [hI]
        _ = 2 * Complex.I * (a (x 0) * a (x 0)) * -Complex.I := by ring
    exact h_eq
  · change a (x 0) * sigma3.val 1 0 * (a (x 0) * sigma1.val 0 0) + a (x 0) * sigma3.val 1 1 * (a (x 0) * sigma1.val 1 0) - (a (x 0) * sigma1.val 1 0 * (a (x 0) * sigma3.val 0 0) + a (x 0) * sigma1.val 1 1 * (a (x 0) * sigma3.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma2.val 1 0
    simp only [hs1_00, hs1_10, hs1_11, hs2_10, hs3_00, hs3_10, hs3_11]
    have h_eq : a (x 0) * 0 * (a (x 0) * 0) + a (x 0) * -1 * (a (x 0) * 1) - (a (x 0) * 1 * (a (x 0) * 1) + a (x 0) * 0 * (a (x 0) * 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * Complex.I := by
      calc
        a (x 0) * 0 * (a (x 0) * 0) + a (x 0) * -1 * (a (x 0) * 1) - (a (x 0) * 1 * (a (x 0) * 1) + a (x 0) * 0 * (a (x 0) * 0))
        _ = -2 * (a (x 0) * a (x 0)) := by ring
        _ = 2 * (a (x 0) * a (x 0)) * (-1) := by ring
        _ = 2 * (a (x 0) * a (x 0)) * (Complex.I ^ 2) := by rw [hI]
        _ = 2 * Complex.I * (a (x 0) * a (x 0)) * Complex.I := by ring
    exact h_eq
  · change a (x 0) * sigma3.val 1 0 * (a (x 0) * sigma1.val 0 1) + a (x 0) * sigma3.val 1 1 * (a (x 0) * sigma1.val 1 1) - (a (x 0) * sigma1.val 1 0 * (a (x 0) * sigma3.val 0 1) + a (x 0) * sigma1.val 1 1 * (a (x 0) * sigma3.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma2.val 1 1
    simp only [hs1_01, hs1_10, hs1_11, hs2_11, hs3_01, hs3_10, hs3_11]
    ring

lemma curvatureSl2c_same (A : Fin 4 → SpacetimePoint → SL2C) (m : Fin 4) (x : SpacetimePoint) :
  (curvatureSl2c A m m x).val = 0 := by
  rw [curvatureSl2c_def]
  have h_comm : ⁅A m x, A m x⁆ = 0 := lie_self (A m x)
  rw [h_comm]
  simp

/-- The F_01 component of the FLRW curvature evaluates strictly to \dot{a} sigma_x. -/
lemma flrw_F_0_1 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (flrw_A a) 0 1 x).val = (fderiv ℝ a (x 0) 1) • sigma1.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (flrw_A a) 0 1 x (flrw_A_differentiable a 0 x ha) (flrw_A_differentiable a 1 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 0 (fun p => (flrw_A a 1 p).val i j) x = (fderiv ℝ a (x 0) 1 * sigma1.val i j) := by
    have h_mat := partialDerivMat_flrw_L_0_1 a x ha
    have h_eq : (fun p => (flrw_A a 1 p).val i j) = fun p => flrw_L a 1 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 0 (fun p => flrw_L a 1 p i j) x = partialDerivMat 0 (fun p => flrw_L a 1 p) x i j := rfl
    rw [h_eval, h_mat]
    simp only [Matrix.smul_apply, smul_eq_mul]
  have hd1 : partialDeriv 1 (fun p => (flrw_A a 0 p).val i j) x = 0 := by
    have h_mat := partialDerivMat_flrw_L_k_0 a 1 x
    have h_eq : (fun p => (flrw_A a 0 p).val i j) = fun p => flrw_L a 0 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 1 (fun p => flrw_L a 0 p i j) x = partialDerivMat 1 (fun p => flrw_L a 0 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((flrw_A a 0 x).val * (flrw_A a 1 x).val - (flrw_A a 1 x).val * (flrw_A a 0 x).val) i j = 0 := by
    have h0 : (flrw_A a 0 x).val = 0 := by rw [flrw_A_val_eq, flrw_L_0_eq]
    rw [h0]
    simp
  rw [hd0, hd1, h_comm]
  simp only [Matrix.smul_apply, smul_eq_mul, add_zero, sub_zero]

/-- The F_02 component of the FLRW curvature evaluates strictly to \dot{a} sigma_y. -/
lemma flrw_F_0_2 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (flrw_A a) 0 2 x).val = (fderiv ℝ a (x 0) 1) • sigma2.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (flrw_A a) 0 2 x (flrw_A_differentiable a 0 x ha) (flrw_A_differentiable a 2 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 0 (fun p => (flrw_A a 2 p).val i j) x = (fderiv ℝ a (x 0) 1 * sigma2.val i j) := by
    have h_mat := partialDerivMat_flrw_L_0_2 a x ha
    have h_eq : (fun p => (flrw_A a 2 p).val i j) = fun p => flrw_L a 2 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 0 (fun p => flrw_L a 2 p i j) x = partialDerivMat 0 (fun p => flrw_L a 2 p) x i j := rfl
    rw [h_eval, h_mat]
    simp only [Matrix.smul_apply, smul_eq_mul]
  have hd1 : partialDeriv 2 (fun p => (flrw_A a 0 p).val i j) x = 0 := by
    have h_mat := partialDerivMat_flrw_L_k_0 a 2 x
    have h_eq : (fun p => (flrw_A a 0 p).val i j) = fun p => flrw_L a 0 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 2 (fun p => flrw_L a 0 p i j) x = partialDerivMat 2 (fun p => flrw_L a 0 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((flrw_A a 0 x).val * (flrw_A a 2 x).val - (flrw_A a 2 x).val * (flrw_A a 0 x).val) i j = 0 := by
    have h0 : (flrw_A a 0 x).val = 0 := by rw [flrw_A_val_eq, flrw_L_0_eq]
    rw [h0]
    simp
  rw [hd0, hd1, h_comm]
  simp only [Matrix.smul_apply, smul_eq_mul, add_zero, sub_zero]

/-- The F_03 component of the FLRW curvature evaluates strictly to \dot{a} sigma_z. -/
lemma flrw_F_0_3 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (flrw_A a) 0 3 x).val = (fderiv ℝ a (x 0) 1) • sigma3.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (flrw_A a) 0 3 x (flrw_A_differentiable a 0 x ha) (flrw_A_differentiable a 3 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 0 (fun p => (flrw_A a 3 p).val i j) x = (fderiv ℝ a (x 0) 1 * sigma3.val i j) := by
    have h_mat := partialDerivMat_flrw_L_0_3 a x ha
    have h_eq : (fun p => (flrw_A a 3 p).val i j) = fun p => flrw_L a 3 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 0 (fun p => flrw_L a 3 p i j) x = partialDerivMat 0 (fun p => flrw_L a 3 p) x i j := rfl
    rw [h_eval, h_mat]
    simp only [Matrix.smul_apply, smul_eq_mul]
  have hd1 : partialDeriv 3 (fun p => (flrw_A a 0 p).val i j) x = 0 := by
    have h_mat := partialDerivMat_flrw_L_k_0 a 3 x
    have h_eq : (fun p => (flrw_A a 0 p).val i j) = fun p => flrw_L a 0 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 3 (fun p => flrw_L a 0 p i j) x = partialDerivMat 3 (fun p => flrw_L a 0 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((flrw_A a 0 x).val * (flrw_A a 3 x).val - (flrw_A a 3 x).val * (flrw_A a 0 x).val) i j = 0 := by
    have h0 : (flrw_A a 0 x).val = 0 := by rw [flrw_A_val_eq, flrw_L_0_eq]
    rw [h0]
    simp
  rw [hd0, hd1, h_comm]
  simp only [Matrix.smul_apply, smul_eq_mul, add_zero, sub_zero]

/-- The F_12 component of the FLRW curvature evaluates strictly to the [A_1, A_2] commutator. -/
lemma flrw_F_1_2 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (flrw_A a) 1 2 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (flrw_A a) 1 2 x (flrw_A_differentiable a 1 x ha) (flrw_A_differentiable a 2 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 1 (fun p => (flrw_A a 2 p).val i j) x = 0 := by
    have hk : (1 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_flrw_L_k_2 a 1 x hk ha
    have h_eq : (fun p => (flrw_A a 2 p).val i j) = fun p => flrw_L a 2 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 1 (fun p => flrw_L a 2 p i j) x = partialDerivMat 1 (fun p => flrw_L a 2 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have hd1 : partialDeriv 2 (fun p => (flrw_A a 1 p).val i j) x = 0 := by
    have hk : (2 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_flrw_L_k_1 a 2 x hk ha
    have h_eq : (fun p => (flrw_A a 1 p).val i j) = fun p => flrw_L a 1 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 2 (fun p => flrw_L a 1 p i j) x = partialDerivMat 2 (fun p => flrw_L a 1 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((flrw_A a 1 x).val * (flrw_A a 2 x).val - (flrw_A a 2 x).val * (flrw_A a 1 x).val) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val) i j := by
    have h1 : (flrw_A a 1 x).val = flrw_L a 1 x := flrw_A_val_eq a 1 x
    have h2 : (flrw_A a 2 x).val = flrw_L a 2 x := flrw_A_val_eq a 2 x
    rw [h1, h2]
    have h_comm_mat := flrw_L_comm_1_2 a x
    have h_eval : (flrw_L a 1 x * flrw_L a 2 x - flrw_L a 2 x * flrw_L a 1 x) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val) i j := by rw [h_comm_mat]
    exact h_eval
  rw [hd0, hd1, h_comm]
  simp only [sub_zero, zero_add]

/-- The F_23 component of the FLRW curvature evaluates strictly to the [A_2, A_3] commutator. -/
lemma flrw_F_2_3 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (flrw_A a) 2 3 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (flrw_A a) 2 3 x (flrw_A_differentiable a 2 x ha) (flrw_A_differentiable a 3 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 2 (fun p => (flrw_A a 3 p).val i j) x = 0 := by
    have hk : (2 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_flrw_L_k_3 a 2 x hk ha
    have h_eq : (fun p => (flrw_A a 3 p).val i j) = fun p => flrw_L a 3 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 2 (fun p => flrw_L a 3 p i j) x = partialDerivMat 2 (fun p => flrw_L a 3 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have hd1 : partialDeriv 3 (fun p => (flrw_A a 2 p).val i j) x = 0 := by
    have hk : (3 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_flrw_L_k_2 a 3 x hk ha
    have h_eq : (fun p => (flrw_A a 2 p).val i j) = fun p => flrw_L a 2 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 3 (fun p => flrw_L a 2 p i j) x = partialDerivMat 3 (fun p => flrw_L a 2 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((flrw_A a 2 x).val * (flrw_A a 3 x).val - (flrw_A a 3 x).val * (flrw_A a 2 x).val) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val) i j := by
    have h2 : (flrw_A a 2 x).val = flrw_L a 2 x := flrw_A_val_eq a 2 x
    have h3 : (flrw_A a 3 x).val = flrw_L a 3 x := flrw_A_val_eq a 3 x
    rw [h2, h3]
    have h_comm_mat := flrw_L_comm_2_3 a x
    have h_eval : (flrw_L a 2 x * flrw_L a 3 x - flrw_L a 3 x * flrw_L a 2 x) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val) i j := by rw [h_comm_mat]
    exact h_eval
  rw [hd0, hd1, h_comm]
  simp only [sub_zero, zero_add]

/-- The F_31 component of the FLRW curvature evaluates strictly to the [A_3, A_1] commutator. -/
lemma flrw_F_3_1 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (flrw_A a) 3 1 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (flrw_A a) 3 1 x (flrw_A_differentiable a 3 x ha) (flrw_A_differentiable a 1 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 3 (fun p => (flrw_A a 1 p).val i j) x = 0 := by
    have hk : (3 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_flrw_L_k_1 a 3 x hk ha
    have h_eq : (fun p => (flrw_A a 1 p).val i j) = fun p => flrw_L a 1 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 3 (fun p => flrw_L a 1 p i j) x = partialDerivMat 3 (fun p => flrw_L a 1 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have hd1 : partialDeriv 1 (fun p => (flrw_A a 3 p).val i j) x = 0 := by
    have hk : (1 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_flrw_L_k_3 a 1 x hk ha
    have h_eq : (fun p => (flrw_A a 3 p).val i j) = fun p => flrw_L a 3 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 1 (fun p => flrw_L a 3 p i j) x = partialDerivMat 1 (fun p => flrw_L a 3 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((flrw_A a 3 x).val * (flrw_A a 1 x).val - (flrw_A a 1 x).val * (flrw_A a 3 x).val) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val) i j := by
    have h3 : (flrw_A a 3 x).val = flrw_L a 3 x := flrw_A_val_eq a 3 x
    have h1 : (flrw_A a 1 x).val = flrw_L a 1 x := flrw_A_val_eq a 1 x
    rw [h3, h1]
    have h_comm_mat := flrw_L_comm_3_1 a x
    have h_eval : (flrw_L a 3 x * flrw_L a 1 x - flrw_L a 1 x * flrw_L a 3 x) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val) i j := by rw [h_comm_mat]
    exact h_eval
  rw [hd0, hd1, h_comm]
  simp only [sub_zero, zero_add]

/-- The exact analytically predicted values for the 16 F_{mu, nu} curvature components. -/
noncomputable def flrw_F_expected (adot a2 : ℂ) (mu nu : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if mu = 0 ∧ nu = 1 then adot • sigma1.val
  else if mu = 1 ∧ nu = 0 then -adot • sigma1.val
  else if mu = 0 ∧ nu = 2 then adot • sigma2.val
  else if mu = 2 ∧ nu = 0 then -adot • sigma2.val
  else if mu = 0 ∧ nu = 3 then adot • sigma3.val
  else if mu = 3 ∧ nu = 0 then -adot • sigma3.val
  else if mu = 1 ∧ nu = 2 then (2 * Complex.I * a2) • sigma3.val
  else if mu = 2 ∧ nu = 1 then -(2 * Complex.I * a2) • sigma3.val
  else if mu = 2 ∧ nu = 3 then (2 * Complex.I * a2) • sigma1.val
  else if mu = 3 ∧ nu = 2 then -(2 * Complex.I * a2) • sigma1.val
  else if mu = 3 ∧ nu = 1 then (2 * Complex.I * a2) • sigma2.val
  else if mu = 1 ∧ nu = 3 then -(2 * Complex.I * a2) • sigma2.val
  else 0

/-- Consolidates all 16 F_{mu, nu} tensors into a single rapid-access evaluation theorem. -/
lemma flrw_F_val_master (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) (mu nu : Fin 4) :
  (curvatureSl2c (flrw_A a) mu nu x).val = flrw_F_expected (fderiv ℝ a (x 0) 1) (a (x 0) * a (x 0)) mu nu := by
  have h_rev : ∀ m n, (curvatureSl2c (flrw_A a) n m x).val = - (curvatureSl2c (flrw_A a) m n x).val := by
    intro m n
    have h := curvatureSl2c_antisymm (flrw_A a) n m x
    calc (curvatureSl2c (flrw_A a) n m x).val
      _ = (- curvatureSl2c (flrw_A a) m n x).val := by rw [h]
      _ = - (curvatureSl2c (flrw_A a) m n x).val := rfl

  fin_cases mu <;> fin_cases nu
  · change (curvatureSl2c (flrw_A a) 0 0 x).val = flrw_F_expected _ _ 0 0
    rw [curvatureSl2c_same]; rfl
  · change (curvatureSl2c (flrw_A a) 0 1 x).val = flrw_F_expected _ _ 0 1
    rw [flrw_F_0_1 a x ha]; rfl
  · change (curvatureSl2c (flrw_A a) 0 2 x).val = flrw_F_expected _ _ 0 2
    rw [flrw_F_0_2 a x ha]; rfl
  · change (curvatureSl2c (flrw_A a) 0 3 x).val = flrw_F_expected _ _ 0 3
    rw [flrw_F_0_3 a x ha]; rfl
  · change (curvatureSl2c (flrw_A a) 1 0 x).val = flrw_F_expected _ _ 1 0
    rw [h_rev 0 1, flrw_F_0_1 a x ha]; dsimp [flrw_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (flrw_A a) 1 1 x).val = flrw_F_expected _ _ 1 1
    rw [curvatureSl2c_same]; rfl
  · change (curvatureSl2c (flrw_A a) 1 2 x).val = flrw_F_expected _ _ 1 2
    rw [flrw_F_1_2 a x ha]; rfl
  · change (curvatureSl2c (flrw_A a) 1 3 x).val = flrw_F_expected _ _ 1 3
    rw [h_rev 3 1, flrw_F_3_1 a x ha]; dsimp [flrw_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (flrw_A a) 2 0 x).val = flrw_F_expected _ _ 2 0
    rw [h_rev 0 2, flrw_F_0_2 a x ha]; dsimp [flrw_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (flrw_A a) 2 1 x).val = flrw_F_expected _ _ 2 1
    rw [h_rev 1 2, flrw_F_1_2 a x ha]; dsimp [flrw_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (flrw_A a) 2 2 x).val = flrw_F_expected _ _ 2 2
    rw [curvatureSl2c_same]; rfl
  · change (curvatureSl2c (flrw_A a) 2 3 x).val = flrw_F_expected _ _ 2 3
    rw [flrw_F_2_3 a x ha]; rfl
  · change (curvatureSl2c (flrw_A a) 3 0 x).val = flrw_F_expected _ _ 3 0
    rw [h_rev 0 3, flrw_F_0_3 a x ha]; dsimp [flrw_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (flrw_A a) 3 1 x).val = flrw_F_expected _ _ 3 1
    rw [flrw_F_3_1 a x ha]; rfl
  · change (curvatureSl2c (flrw_A a) 3 2 x).val = flrw_F_expected _ _ 3 2
    rw [h_rev 2 3, flrw_F_2_3 a x ha]; dsimp [flrw_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (flrw_A a) 3 3 x).val = flrw_F_expected _ _ 3 3
    rw [curvatureSl2c_same]; rfl

end CGD.Gravity.FLRW

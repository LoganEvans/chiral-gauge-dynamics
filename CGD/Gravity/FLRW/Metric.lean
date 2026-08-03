-- FILENAME: CGD/Gravity/FLRW/Metric.lean

import CGD.Gravity.FLRW.Curvature

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000

open CGD.Foundations CGD.Math CGD.Gravity Complex Matrix BigOperators

namespace CGD.Gravity.FLRW

/-- Extracts the a=0 adjoint projection from the F_01 curvature matrix. Evaluates to \dot{a}. -/
lemma flrw_project_0_0_1 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 0 0 1 = fderiv ℝ a (x 0) 1 := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (flrw_A a) 0 1 x).val = (fderiv ℝ a (x 0) 1) • sigma1.val := flrw_F_0_1 a x ha
  rw [hF]
  rw [fin2_sum]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  simp only [hs1_00, hs1_01, hs1_10, hs1_11]
  have h_eq : (0.5 : ℂ) * (
    (fderiv ℝ a (x 0) 1 * 0 * 0 + fderiv ℝ a (x 0) 1 * 1 * 1) +
    (fderiv ℝ a (x 0) 1 * 1 * 1 + fderiv ℝ a (x 0) 1 * 0 * 0)
  ) = fderiv ℝ a (x 0) 1 := by ring
  exact h_eq

/-- Extracts the a=1 adjoint projection from the F_02 curvature matrix. Evaluates to \dot{a}. -/
lemma flrw_project_1_0_2 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 1 0 2 = fderiv ℝ a (x 0) 1 := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (flrw_A a) 0 2 x).val = (fderiv ℝ a (x 0) 1) • sigma2.val := flrw_F_0_2 a x ha
  rw [hF]
  rw [fin2_sum]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  simp only [hs2_00, hs2_01, hs2_10, hs2_11]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h_eq : (0.5 : ℂ) * (
    (fderiv ℝ a (x 0) 1 * 0 * 0 + fderiv ℝ a (x 0) 1 * -Complex.I * Complex.I) +
    (fderiv ℝ a (x 0) 1 * Complex.I * -Complex.I + fderiv ℝ a (x 0) 1 * 0 * 0)
  ) = fderiv ℝ a (x 0) 1 := by
    calc (0.5 : ℂ) * ( (fderiv ℝ a (x 0) 1 * 0 * 0 + fderiv ℝ a (x 0) 1 * -Complex.I * Complex.I) + (fderiv ℝ a (x 0) 1 * Complex.I * -Complex.I + fderiv ℝ a (x 0) 1 * 0 * 0) )
      _ = (0.5 : ℂ) * ( - fderiv ℝ a (x 0) 1 * (Complex.I * Complex.I) - fderiv ℝ a (x 0) 1 * (Complex.I * Complex.I) ) := by ring
      _ = (0.5 : ℂ) * ( - fderiv ℝ a (x 0) 1 * (-1) - fderiv ℝ a (x 0) 1 * (-1) ) := by rw [hI]
      _ = fderiv ℝ a (x 0) 1 := by ring
  exact h_eq

/-- Extracts the a=2 adjoint projection from the F_03 curvature matrix. Evaluates to \dot{a}. -/
lemma flrw_project_2_0_3 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 2 0 3 = fderiv ℝ a (x 0) 1 := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (flrw_A a) 0 3 x).val = (fderiv ℝ a (x 0) 1) • sigma3.val := flrw_F_0_3 a x ha
  rw [hF]
  rw [fin2_sum]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
  simp only [hs3_00, hs3_01, hs3_10, hs3_11]
  have h_eq : (0.5 : ℂ) * (
    (fderiv ℝ a (x 0) 1 * 1 * 1 + fderiv ℝ a (x 0) 1 * 0 * 0) +
    (fderiv ℝ a (x 0) 1 * 0 * 0 + fderiv ℝ a (x 0) 1 * -1 * -1)
  ) = fderiv ℝ a (x 0) 1 := by ring
  exact h_eq

/-- Extracts the a=2 adjoint projection from the F_12 curvature matrix. Evaluates to 2i a^2. -/
lemma flrw_project_2_1_2 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 2 1 2 = 2 * Complex.I * (a (x 0) * a (x 0)) := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (flrw_A a) 1 2 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val := flrw_F_1_2 a x ha
  rw [hF]
  rw [fin2_sum]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
  simp only [hs3_00, hs3_01, hs3_10, hs3_11]
  have h_eq : (0.5 : ℂ) * (
    (2 * Complex.I * (a (x 0) * a (x 0)) * 1 * 1 + 2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0) +
    (2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0 + 2 * Complex.I * (a (x 0) * a (x 0)) * -1 * -1)
  ) = 2 * Complex.I * (a (x 0) * a (x 0)) := by ring
  exact h_eq

/-- Extracts the a=0 adjoint projection from the F_23 curvature matrix. Evaluates to 2i a^2. -/
lemma flrw_project_0_2_3 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 0 2 3 = 2 * Complex.I * (a (x 0) * a (x 0)) := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (flrw_A a) 2 3 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val := flrw_F_2_3 a x ha
  rw [hF]
  rw [fin2_sum]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  simp only [hs1_00, hs1_01, hs1_10, hs1_11]
  have h_eq : (0.5 : ℂ) * (
    (2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0 + 2 * Complex.I * (a (x 0) * a (x 0)) * 1 * 1) +
    (2 * Complex.I * (a (x 0) * a (x 0)) * 1 * 1 + 2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0)
  ) = 2 * Complex.I * (a (x 0) * a (x 0)) := by ring
  exact h_eq

/-- Extracts the a=1 adjoint projection from the F_31 curvature matrix. Evaluates to 2i a^2. -/
lemma flrw_project_1_3_1 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 1 3 1 = 2 * Complex.I * (a (x 0) * a (x 0)) := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (flrw_A a) 3 1 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val := flrw_F_3_1 a x ha
  rw [hF]
  rw [fin2_sum]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  simp only [hs2_00, hs2_01, hs2_10, hs2_11]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h_eq : (0.5 : ℂ) * (
    (2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0 + 2 * Complex.I * (a (x 0) * a (x 0)) * -Complex.I * Complex.I) +
    (2 * Complex.I * (a (x 0) * a (x 0)) * Complex.I * -Complex.I + 2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0)
  ) = 2 * Complex.I * (a (x 0) * a (x 0)) := by
    calc (0.5 : ℂ) * ( (2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0 + 2 * Complex.I * (a (x 0) * a (x 0)) * -Complex.I * Complex.I) + (2 * Complex.I * (a (x 0) * a (x 0)) * Complex.I * -Complex.I + 2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0) )
      _ = (0.5 : ℂ) * ( - (2 * Complex.I * (a (x 0) * a (x 0))) * (Complex.I * Complex.I) - (2 * Complex.I * (a (x 0) * a (x 0))) * (Complex.I * Complex.I) ) := by ring
      _ = (0.5 : ℂ) * ( - (2 * Complex.I * (a (x 0) * a (x 0))) * (-1) - (2 * Complex.I * (a (x 0) * a (x 0))) * (-1) ) := by rw [hI]
      _ = 2 * Complex.I * (a (x 0) * a (x 0)) := by ring
  exact h_eq

/-- Expands the 3-dimensional Levi-Civita summation over the internal isotopic indices. -/
lemma urbantke_sum_iso (F : Fin 3 → Fin 3 → Fin 3 → ℂ) :
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * F a b c) =
  F 0 1 2 - F 0 2 1 - F 1 0 2 + F 1 2 0 + F 2 0 1 - F 2 1 0 := by
  simp [Fin.sum_univ_three, epsilon3, epsilon3_int]
  ring

/-- Expands the 4-dimensional Levi-Civita summation over the spacetime indices. -/
lemma urbantke_sum_space (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
  (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4, epsilon4 a b c d * F a b c d) =
  F 0 1 2 3 - F 0 1 3 2 - F 0 2 1 3 + F 0 2 3 1 + F 0 3 1 2 - F 0 3 2 1
  - F 1 0 2 3 + F 1 0 3 2 + F 1 2 0 3 - F 1 2 3 0 - F 1 3 0 2 + F 1 3 2 0
  + F 2 0 1 3 - F 2 0 3 1 - F 2 1 0 3 + F 2 1 3 0 + F 2 3 0 1 - F 2 3 1 0
  - F 3 0 1 2 + F 3 0 2 1 + F 3 1 0 2 - F 3 1 2 0 - F 3 2 0 1 + F 3 2 1 0 := by
  simp [Fin.sum_univ_four, epsilon4, epsilon4_int]
  ring

/-- The exact analytically predicted values for the 48 adjoint projection traces P^a_{mu, nu}. -/
noncomputable def flrw_P_expected (adot a2 : ℂ) (c : Fin 3) (mu nu : Fin 4) : ℂ :=
  if c = 0 ∧ mu = 0 ∧ nu = 1 then adot
  else if c = 0 ∧ mu = 1 ∧ nu = 0 then -adot
  else if c = 1 ∧ mu = 0 ∧ nu = 2 then adot
  else if c = 1 ∧ mu = 2 ∧ nu = 0 then -adot
  else if c = 2 ∧ mu = 0 ∧ nu = 3 then adot
  else if c = 2 ∧ mu = 3 ∧ nu = 0 then -adot
  else if c = 2 ∧ mu = 1 ∧ nu = 2 then 2 * Complex.I * a2
  else if c = 2 ∧ mu = 2 ∧ nu = 1 then -2 * Complex.I * a2
  else if c = 0 ∧ mu = 2 ∧ nu = 3 then 2 * Complex.I * a2
  else if c = 0 ∧ mu = 3 ∧ nu = 2 then -2 * Complex.I * a2
  else if c = 1 ∧ mu = 3 ∧ nu = 1 then 2 * Complex.I * a2
  else if c = 1 ∧ mu = 1 ∧ nu = 3 then -2 * Complex.I * a2
  else 0

lemma I_cubed : Complex.I ^ 3 = -Complex.I := by
  have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
  calc Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
  _ = -1 * Complex.I := by rw [h2]
  _ = -Complex.I := by ring

lemma flrw_project_master_c0 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) (mu nu : Fin 4) :
  project (fun m n => curvatureSl2c (flrw_A a) m n x) 0 mu nu = flrw_P_expected (fderiv ℝ a (x 0) 1) (a (x 0) * a (x 0)) 0 mu nu := by

  -- Explicitly expand project to bypass `let` bindings
  have h_expand : project (fun m n => curvatureSl2c (flrw_A a) m n x) 0 mu nu = 0.5 * ((curvatureSl2c (flrw_A a) mu nu x).val * sigma1.val).trace := rfl
  rw [h_expand]

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
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I

  match mu, nu with
  | 0, 0 => rw [flrw_F_val_master a x ha 0 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 0, 1 => rw [flrw_F_val_master a x ha 0 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 0, 2 => rw [flrw_F_val_master a x ha 0 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 0, 3 => rw [flrw_F_val_master a x ha 0 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 1, 0 => rw [flrw_F_val_master a x ha 1 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 1, 1 => rw [flrw_F_val_master a x ha 1 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 1, 2 => rw [flrw_F_val_master a x ha 1 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 1, 3 => rw [flrw_F_val_master a x ha 1 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 2, 0 => rw [flrw_F_val_master a x ha 2 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 2, 1 => rw [flrw_F_val_master a x ha 2 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 2, 2 => rw [flrw_F_val_master a x ha 2 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 2, 3 => rw [flrw_F_val_master a x ha 2 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 3, 0 => rw [flrw_F_val_master a x ha 3 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 3, 1 => rw [flrw_F_val_master a x ha 3 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 3, 2 => rw [flrw_F_val_master a x ha 3 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 3, 3 => rw [flrw_F_val_master a x ha 3 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring

lemma flrw_project_master_c1 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) (mu nu : Fin 4) :
  project (fun m n => curvatureSl2c (flrw_A a) m n x) 1 mu nu = flrw_P_expected (fderiv ℝ a (x 0) 1) (a (x 0) * a (x 0)) 1 mu nu := by

  -- Explicitly expand project to bypass `let` bindings
  have h_expand : project (fun m n => curvatureSl2c (flrw_A a) m n x) 1 mu nu = 0.5 * ((curvatureSl2c (flrw_A a) mu nu x).val * sigma2.val).trace := rfl
  rw [h_expand]

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

  match mu, nu with
  | 0, 0 => rw [flrw_F_val_master a x ha 0 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 0, 1 => rw [flrw_F_val_master a x ha 0 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 0, 2 => rw [flrw_F_val_master a x ha 0 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 0, 3 => rw [flrw_F_val_master a x ha 0 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 0 => rw [flrw_F_val_master a x ha 1 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 1 => rw [flrw_F_val_master a x ha 1 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 2 => rw [flrw_F_val_master a x ha 1 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 3 => rw [flrw_F_val_master a x ha 1 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 0 => rw [flrw_F_val_master a x ha 2 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 1 => rw [flrw_F_val_master a x ha 2 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 2 => rw [flrw_F_val_master a x ha 2 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 3 => rw [flrw_F_val_master a x ha 2 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 0 => rw [flrw_F_val_master a x ha 3 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 1 => rw [flrw_F_val_master a x ha 3 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 2 => rw [flrw_F_val_master a x ha 3 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 3 => rw [flrw_F_val_master a x ha 3 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring

lemma flrw_project_master_c2 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) (mu nu : Fin 4) :
  project (fun m n => curvatureSl2c (flrw_A a) m n x) 2 mu nu = flrw_P_expected (fderiv ℝ a (x 0) 1) (a (x 0) * a (x 0)) 2 mu nu := by

  -- Explicitly expand project to bypass `let` bindings
  have h_expand : project (fun m n => curvatureSl2c (flrw_A a) m n x) 2 mu nu = 0.5 * ((curvatureSl2c (flrw_A a) mu nu x).val * sigma3.val).trace := rfl
  rw [h_expand]

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

  match mu, nu with
  | 0, 0 => rw [flrw_F_val_master a x ha 0 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 0, 1 => rw [flrw_F_val_master a x ha 0 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 0, 2 => rw [flrw_F_val_master a x ha 0 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 0, 3 => rw [flrw_F_val_master a x ha 0 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 0 => rw [flrw_F_val_master a x ha 1 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 1 => rw [flrw_F_val_master a x ha 1 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 2 => rw [flrw_F_val_master a x ha 1 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 3 => rw [flrw_F_val_master a x ha 1 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 0 => rw [flrw_F_val_master a x ha 2 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 1 => rw [flrw_F_val_master a x ha 2 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 2 => rw [flrw_F_val_master a x ha 2 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 3 => rw [flrw_F_val_master a x ha 2 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 0 => rw [flrw_F_val_master a x ha 3 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 1 => rw [flrw_F_val_master a x ha 3 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 2 => rw [flrw_F_val_master a x ha 3 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 3 => rw [flrw_F_val_master a x ha 3 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring

lemma space_term_mul_assoc (E F1 F2 F3 : ℂ) : E * F1 * F2 * F3 = E * (F1 * F2 * F3) := by ring

/--
Evaluates the time-time component of the macroscopic Urbantke metric for the FLRW cosmological vacuum.
Yields precisely 12 * adot^3, driving the temporal signature of the expanding FLRW universe.
-/
lemma flrw_metric_00 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  urbantkeMetric (fun m n => curvatureSl2c (flrw_A a) m n x) 0 0 = 12 * (fderiv ℝ a (x 0) 1) ^ 3 := by
  unfold urbantkeMetric
  dsimp only
  simp only [space_term_mul_assoc]
  rw [urbantke_sum_iso]
  simp only [urbantke_sum_space]
  simp only [flrw_project_master_c0 a x ha, flrw_project_master_c1 a x ha, flrw_project_master_c2 a x ha]
  dsimp [flrw_P_expected]
  try ring_nf
  try simp only [Complex.I_sq, I_cubed]
  try ring

/--
Evaluates the x-x spatial component of the macroscopic Urbantke metric for the FLRW cosmological vacuum.
Yields precisely -48 * adot * a^4, capturing the dynamic expansion of the spatial hypersurface.
-/
lemma flrw_metric_11 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  urbantkeMetric (fun m n => curvatureSl2c (flrw_A a) m n x) 1 1 = -48 * (fderiv ℝ a (x 0) 1) * (a (x 0) * a (x 0)) ^ 2 := by
  unfold urbantkeMetric
  dsimp only
  simp only [space_term_mul_assoc]
  rw [urbantke_sum_iso]
  simp only [urbantke_sum_space]
  simp only [flrw_project_master_c0 a x ha, flrw_project_master_c1 a x ha, flrw_project_master_c2 a x ha]
  dsimp [flrw_P_expected]
  try ring_nf
  try simp only [Complex.I_sq, I_cubed]
  try ring

/--
Evaluates the y-y spatial component of the macroscopic Urbantke metric for the FLRW cosmological vacuum.
Yields precisely -48 * adot * a^4, capturing the dynamic expansion of the spatial hypersurface.
-/
lemma flrw_metric_22 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  urbantkeMetric (fun m n => curvatureSl2c (flrw_A a) m n x) 2 2 = -48 * (fderiv ℝ a (x 0) 1) * (a (x 0) * a (x 0)) ^ 2 := by
  unfold urbantkeMetric
  dsimp only
  simp only [space_term_mul_assoc]
  rw [urbantke_sum_iso]
  simp only [urbantke_sum_space]
  simp only [flrw_project_master_c0 a x ha, flrw_project_master_c1 a x ha, flrw_project_master_c2 a x ha]
  dsimp [flrw_P_expected]
  try ring_nf
  try simp only [Complex.I_sq, I_cubed]
  try ring

/--
Evaluates the z-z spatial component of the macroscopic Urbantke metric for the FLRW cosmological vacuum.
Yields precisely -48 * adot * a^4, capturing the dynamic expansion of the spatial hypersurface.
-/
lemma flrw_metric_33 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  urbantkeMetric (fun m n => curvatureSl2c (flrw_A a) m n x) 3 3 = -48 * (fderiv ℝ a (x 0) 1) * (a (x 0) * a (x 0)) ^ 2 := by
  unfold urbantkeMetric
  dsimp only
  simp only [space_term_mul_assoc]
  rw [urbantke_sum_iso]
  simp only [urbantke_sum_space]
  simp only [flrw_project_master_c0 a x ha, flrw_project_master_c1 a x ha, flrw_project_master_c2 a x ha]
  dsimp [flrw_P_expected]
  try ring_nf
  try simp only [Complex.I_sq, I_cubed]
  try ring

/--
Evaluates the off-diagonal spatial components of the macroscopic Urbantke metric for the FLRW cosmological vacuum.
Because the FLRW spatial slices are strictly isotropic and orthogonal to the time flow, all off-diagonals evaluate to exactly 0.
-/
lemma flrw_metric_off_diagonal (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) (μ ν : Fin 4) (h_diff : μ ≠ ν) :
  urbantkeMetric (fun m n => curvatureSl2c (flrw_A a) m n x) μ ν = 0 := by
  revert h_diff
  fin_cases μ <;> fin_cases ν <;> intro h_diff <;> try { contradiction }
  all_goals {
    unfold urbantkeMetric
    dsimp only
    simp only [space_term_mul_assoc]
    rw [urbantke_sum_iso]
    simp only [urbantke_sum_space]
    simp only [flrw_project_master_c0 a x ha, flrw_project_master_c1 a x ha, flrw_project_master_c2 a x ha]
    dsimp [flrw_P_expected]
    try ring_nf
    try simp only [Complex.I_sq, I_cubed]
    try ring
  }

end CGD.Gravity.FLRW

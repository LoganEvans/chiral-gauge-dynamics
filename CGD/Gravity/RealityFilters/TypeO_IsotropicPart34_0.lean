-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart34_0.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart33
import CGD.Gravity.Geometry

open CGD.Foundations Complex Matrix CGD.Gravity

set_option linter.unusedSimpArgs false

namespace CGD.Gravity.RealityFilters

/-- The exact analytically predicted values for the 48 adjoint projection traces P^a_{mu, nu}. -/
noncomputable def typeO_P_expected (adot a2 : ℂ) (c : Fin 3) (mu nu : Fin 4) : ℂ :=
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

lemma fin2_sum_local (f : Fin 2 → ℂ) : ∑ i : Fin 2, f i = f 0 + f 1 := by
  have eq : (Finset.univ : Finset (Fin 2)) = {0, 1} := rfl
  rw [eq]; simp [Finset.sum_insert, Finset.sum_singleton]

lemma typeO_project_master_c0 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) (mu nu : Fin 4) :
  project (fun m n => curvatureSl2c (typeO_A a) m n x) 0 mu nu = typeO_P_expected (fderiv ℝ a (x 0) 1) (a (x 0) * a (x 0)) 0 mu nu := by
  
  -- Explicitly expand project to bypass `let` bindings
  have h_expand : project (fun m n => curvatureSl2c (typeO_A a) m n x) 0 mu nu = 0.5 * ((curvatureSl2c (typeO_A a) mu nu x).val * sigma1.val).trace := rfl
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
  | 0, 0 =>
    rw [typeO_F_val_master a x ha 0 0]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 0, 1 =>
    rw [typeO_F_val_master a x ha 0 1]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 0, 2 =>
    rw [typeO_F_val_master a x ha 0 2]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 0, 3 =>
    rw [typeO_F_val_master a x ha 0 3]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 1, 0 =>
    rw [typeO_F_val_master a x ha 1 0]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 1, 1 =>
    rw [typeO_F_val_master a x ha 1 1]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 1, 2 =>
    rw [typeO_F_val_master a x ha 1 2]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 1, 3 =>
    rw [typeO_F_val_master a x ha 1 3]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 2, 0 =>
    rw [typeO_F_val_master a x ha 2 0]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 2, 1 =>
    rw [typeO_F_val_master a x ha 2 1]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 2, 2 =>
    rw [typeO_F_val_master a x ha 2 2]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 2, 3 =>
    rw [typeO_F_val_master a x ha 2 3]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 3, 0 =>
    rw [typeO_F_val_master a x ha 3 0]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 3, 1 =>
    rw [typeO_F_val_master a x ha 3 1]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 3, 2 =>
    rw [typeO_F_val_master a x ha 3 2]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring
  | 3, 3 =>
    rw [typeO_F_val_master a x ha 3 3]
    dsimp [typeO_P_expected, typeO_F_expected]
    unfold Matrix.trace Matrix.diag
    rw [fin2_sum_local]
    simp only [Matrix.mul_apply, fin2_sum_local, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]
    ring

end CGD.Gravity.RealityFilters

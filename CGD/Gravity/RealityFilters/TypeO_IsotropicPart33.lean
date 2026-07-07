-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart33.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart32
import CGD.Gravity.Geometry

open CGD.Foundations Complex Matrix CGD.Gravity

namespace CGD.Gravity.RealityFilters

/-- The exact analytically predicted values for the 16 F_{mu, nu} curvature components. -/
noncomputable def typeO_F_expected (adot a2 : ℂ) (mu nu : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
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

lemma curvatureSl2c_same (A : Fin 4 → SpacetimePoint → SL2C) (m : Fin 4) (x : SpacetimePoint) :
  (curvatureSl2c A m m x).val = 0 := by
  rw [curvatureSl2c_def]
  have h_comm : ⁅A m x, A m x⁆ = 0 := lie_self (A m x)
  rw [h_comm]
  simp

/-- Consolidates all 16 F_{mu, nu} tensors into a single rapid-access evaluation theorem. -/
lemma typeO_F_val_master (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) (mu nu : Fin 4) :
  (curvatureSl2c (typeO_A a) mu nu x).val = typeO_F_expected (fderiv ℝ a (x 0) 1) (a (x 0) * a (x 0)) mu nu := by
  have h_rev : ∀ m n, (curvatureSl2c (typeO_A a) n m x).val = - (curvatureSl2c (typeO_A a) m n x).val := by
    intro m n
    have h := curvatureSl2c_antisymm (typeO_A a) n m x
    calc (curvatureSl2c (typeO_A a) n m x).val
      _ = (- curvatureSl2c (typeO_A a) m n x).val := by rw [h]
      _ = - (curvatureSl2c (typeO_A a) m n x).val := rfl
      
  fin_cases mu <;> fin_cases nu
  · change (curvatureSl2c (typeO_A a) 0 0 x).val = typeO_F_expected _ _ 0 0
    rw [curvatureSl2c_same]; rfl
  · change (curvatureSl2c (typeO_A a) 0 1 x).val = typeO_F_expected _ _ 0 1
    rw [typeO_F_0_1 a x ha]; rfl
  · change (curvatureSl2c (typeO_A a) 0 2 x).val = typeO_F_expected _ _ 0 2
    rw [typeO_F_0_2 a x ha]; rfl
  · change (curvatureSl2c (typeO_A a) 0 3 x).val = typeO_F_expected _ _ 0 3
    rw [typeO_F_0_3 a x ha]; rfl
  · change (curvatureSl2c (typeO_A a) 1 0 x).val = typeO_F_expected _ _ 1 0
    rw [h_rev 0 1, typeO_F_0_1 a x ha]; dsimp [typeO_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (typeO_A a) 1 1 x).val = typeO_F_expected _ _ 1 1
    rw [curvatureSl2c_same]; rfl
  · change (curvatureSl2c (typeO_A a) 1 2 x).val = typeO_F_expected _ _ 1 2
    rw [typeO_F_1_2 a x ha]; rfl
  · change (curvatureSl2c (typeO_A a) 1 3 x).val = typeO_F_expected _ _ 1 3
    rw [h_rev 3 1, typeO_F_3_1 a x ha]; dsimp [typeO_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (typeO_A a) 2 0 x).val = typeO_F_expected _ _ 2 0
    rw [h_rev 0 2, typeO_F_0_2 a x ha]; dsimp [typeO_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (typeO_A a) 2 1 x).val = typeO_F_expected _ _ 2 1
    rw [h_rev 1 2, typeO_F_1_2 a x ha]; dsimp [typeO_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (typeO_A a) 2 2 x).val = typeO_F_expected _ _ 2 2
    rw [curvatureSl2c_same]; rfl
  · change (curvatureSl2c (typeO_A a) 2 3 x).val = typeO_F_expected _ _ 2 3
    rw [typeO_F_2_3 a x ha]; rfl
  · change (curvatureSl2c (typeO_A a) 3 0 x).val = typeO_F_expected _ _ 3 0
    rw [h_rev 0 3, typeO_F_0_3 a x ha]; dsimp [typeO_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (typeO_A a) 3 1 x).val = typeO_F_expected _ _ 3 1
    rw [typeO_F_3_1 a x ha]; rfl
  · change (curvatureSl2c (typeO_A a) 3 2 x).val = typeO_F_expected _ _ 3 2
    rw [h_rev 2 3, typeO_F_2_3 a x ha]; dsimp [typeO_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (typeO_A a) 3 3 x).val = typeO_F_expected _ _ 3 3
    rw [curvatureSl2c_same]; rfl

end CGD.Gravity.RealityFilters

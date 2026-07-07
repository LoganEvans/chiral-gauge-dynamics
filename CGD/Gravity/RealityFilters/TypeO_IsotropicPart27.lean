-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart27.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart26
import CGD.Gravity.Geometry

open CGD.Foundations Complex Matrix CGD.Gravity

namespace CGD.Gravity.RealityFilters

/-- 
Extracts the a=2 adjoint projection from the F_03 curvature matrix.
Evaluates to \dot{a}.
-/
lemma typeO_project_2_0_3 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (typeO_A a) μ ν x) 2 0 3 = fderiv ℝ a (x 0) 1 := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (typeO_A a) 0 3 x).val = (fderiv ℝ a (x 0) 1) • sigma3.val := typeO_F_0_3 a x ha
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

end CGD.Gravity.RealityFilters

-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart25.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart24
import CGD.Gravity.Geometry

open CGD.Foundations Complex Matrix CGD.Gravity

namespace CGD.Gravity.RealityFilters

/-- 
Extracts the a=0 adjoint projection from the F_01 curvature matrix.
Evaluates to \dot{a}.
-/
lemma typeO_project_0_0_1 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (typeO_A a) μ ν x) 0 0 1 = fderiv ℝ a (x 0) 1 := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (typeO_A a) 0 1 x).val = (fderiv ℝ a (x 0) 1) • sigma1.val := typeO_F_0_1 a x ha
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

end CGD.Gravity.RealityFilters

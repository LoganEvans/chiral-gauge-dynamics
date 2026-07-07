-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart28.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart27
import CGD.Gravity.Geometry

open CGD.Foundations Complex Matrix CGD.Gravity

namespace CGD.Gravity.RealityFilters

/-- 
Extracts the a=2 adjoint projection from the F_12 curvature matrix.
Evaluates to 2i a^2.
-/
lemma typeO_project_2_1_2 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (typeO_A a) μ ν x) 2 1 2 = 2 * Complex.I * (a (x 0) * a (x 0)) := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (typeO_A a) 1 2 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val := typeO_F_1_2 a x ha
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

end CGD.Gravity.RealityFilters

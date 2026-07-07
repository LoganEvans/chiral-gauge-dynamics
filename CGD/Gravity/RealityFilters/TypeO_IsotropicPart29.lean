-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart29.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart28
import CGD.Gravity.Geometry

open CGD.Foundations Complex Matrix CGD.Gravity

namespace CGD.Gravity.RealityFilters

/-- 
Extracts the a=0 adjoint projection from the F_23 curvature matrix.
Evaluates to 2i a^2.
-/
lemma typeO_project_0_2_3 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (typeO_A a) μ ν x) 0 2 3 = 2 * Complex.I * (a (x 0) * a (x 0)) := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (typeO_A a) 2 3 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val := typeO_F_2_3 a x ha
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

end CGD.Gravity.RealityFilters

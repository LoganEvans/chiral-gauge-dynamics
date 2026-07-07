-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart26.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart25
import CGD.Gravity.Geometry

open CGD.Foundations Complex Matrix CGD.Gravity

namespace CGD.Gravity.RealityFilters

/-- 
Extracts the a=1 adjoint projection from the F_02 curvature matrix.
Evaluates to \dot{a}.
-/
lemma typeO_project_1_0_2 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (typeO_A a) μ ν x) 1 0 2 = fderiv ℝ a (x 0) 1 := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (typeO_A a) 0 2 x).val = (fderiv ℝ a (x 0) 1) • sigma2.val := typeO_F_0_2 a x ha
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

end CGD.Gravity.RealityFilters

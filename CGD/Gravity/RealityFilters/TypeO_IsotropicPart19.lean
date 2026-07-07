-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart19.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart18

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
The F_01 component of the FLRW curvature evaluates strictly to \dot{a} sigma_x.
-/
lemma typeO_F_0_1 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (typeO_A a) 0 1 x).val = (fderiv ℝ a (x 0) 1) • sigma1.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (typeO_A a) 0 1 x (typeO_A_differentiable a 0 x ha) (typeO_A_differentiable a 1 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 0 (fun p => (typeO_A a 1 p).val i j) x = (fderiv ℝ a (x 0) 1 * sigma1.val i j) := by
    have h_mat := partialDerivMat_typeO_L_0_1 a x ha
    have h_eq : (fun p => (typeO_A a 1 p).val i j) = fun p => typeO_L a 1 p i j := by ext p; rw [typeO_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 0 (fun p => typeO_L a 1 p i j) x = partialDerivMat 0 (fun p => typeO_L a 1 p) x i j := rfl
    rw [h_eval, h_mat]
    simp only [Matrix.smul_apply, smul_eq_mul]
  have hd1 : partialDeriv 1 (fun p => (typeO_A a 0 p).val i j) x = 0 := by
    have h_mat := partialDerivMat_typeO_L_k_0 a 1 x
    have h_eq : (fun p => (typeO_A a 0 p).val i j) = fun p => typeO_L a 0 p i j := by ext p; rw [typeO_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 1 (fun p => typeO_L a 0 p i j) x = partialDerivMat 1 (fun p => typeO_L a 0 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((typeO_A a 0 x).val * (typeO_A a 1 x).val - (typeO_A a 1 x).val * (typeO_A a 0 x).val) i j = 0 := by
    have h0 : (typeO_A a 0 x).val = 0 := by rw [typeO_A_val_eq, typeO_L_0_eq]
    rw [h0]
    simp
  rw [hd0, hd1, h_comm]
  simp only [Matrix.smul_apply, smul_eq_mul, add_zero, sub_zero]

end CGD.Gravity.RealityFilters

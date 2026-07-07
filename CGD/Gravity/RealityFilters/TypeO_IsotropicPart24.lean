-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart24.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart23

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
The F_31 component of the FLRW curvature evaluates strictly to the [A_3, A_1] commutator.
-/
lemma typeO_F_3_1 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (typeO_A a) 3 1 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (typeO_A a) 3 1 x (typeO_A_differentiable a 3 x ha) (typeO_A_differentiable a 1 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 3 (fun p => (typeO_A a 1 p).val i j) x = 0 := by
    have hk : (3 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_typeO_L_k_1 a 3 x hk ha
    have h_eq : (fun p => (typeO_A a 1 p).val i j) = fun p => typeO_L a 1 p i j := by ext p; rw [typeO_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 3 (fun p => typeO_L a 1 p i j) x = partialDerivMat 3 (fun p => typeO_L a 1 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have hd1 : partialDeriv 1 (fun p => (typeO_A a 3 p).val i j) x = 0 := by
    have hk : (1 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_typeO_L_k_3 a 1 x hk ha
    have h_eq : (fun p => (typeO_A a 3 p).val i j) = fun p => typeO_L a 3 p i j := by ext p; rw [typeO_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 1 (fun p => typeO_L a 3 p i j) x = partialDerivMat 1 (fun p => typeO_L a 3 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((typeO_A a 3 x).val * (typeO_A a 1 x).val - (typeO_A a 1 x).val * (typeO_A a 3 x).val) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val) i j := by
    have h3 : (typeO_A a 3 x).val = typeO_L a 3 x := typeO_A_val_eq a 3 x
    have h1 : (typeO_A a 1 x).val = typeO_L a 1 x := typeO_A_val_eq a 1 x
    rw [h3, h1]
    have h_comm_mat := typeO_L_comm_3_1 a x
    have h_eval : (typeO_L a 3 x * typeO_L a 1 x - typeO_L a 1 x * typeO_L a 3 x) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val) i j := by rw [h_comm_mat]
    exact h_eval
  rw [hd0, hd1, h_comm]
  simp only [sub_zero, zero_add]

end CGD.Gravity.RealityFilters

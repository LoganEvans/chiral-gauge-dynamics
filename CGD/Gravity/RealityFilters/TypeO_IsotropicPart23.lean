-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart23.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart22

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
The F_23 component of the FLRW curvature evaluates strictly to the [A_2, A_3] commutator.
-/
lemma typeO_F_2_3 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (typeO_A a) 2 3 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (typeO_A a) 2 3 x (typeO_A_differentiable a 2 x ha) (typeO_A_differentiable a 3 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 2 (fun p => (typeO_A a 3 p).val i j) x = 0 := by
    have hk : (2 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_typeO_L_k_3 a 2 x hk ha
    have h_eq : (fun p => (typeO_A a 3 p).val i j) = fun p => typeO_L a 3 p i j := by ext p; rw [typeO_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 2 (fun p => typeO_L a 3 p i j) x = partialDerivMat 2 (fun p => typeO_L a 3 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have hd1 : partialDeriv 3 (fun p => (typeO_A a 2 p).val i j) x = 0 := by
    have hk : (3 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_typeO_L_k_2 a 3 x hk ha
    have h_eq : (fun p => (typeO_A a 2 p).val i j) = fun p => typeO_L a 2 p i j := by ext p; rw [typeO_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 3 (fun p => typeO_L a 2 p i j) x = partialDerivMat 3 (fun p => typeO_L a 2 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((typeO_A a 2 x).val * (typeO_A a 3 x).val - (typeO_A a 3 x).val * (typeO_A a 2 x).val) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val) i j := by
    have h2 : (typeO_A a 2 x).val = typeO_L a 2 x := typeO_A_val_eq a 2 x
    have h3 : (typeO_A a 3 x).val = typeO_L a 3 x := typeO_A_val_eq a 3 x
    rw [h2, h3]
    have h_comm_mat := typeO_L_comm_2_3 a x
    have h_eval : (typeO_L a 2 x * typeO_L a 3 x - typeO_L a 3 x * typeO_L a 2 x) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val) i j := by rw [h_comm_mat]
    exact h_eval
  rw [hd0, hd1, h_comm]
  simp only [sub_zero, zero_add]

end CGD.Gravity.RealityFilters

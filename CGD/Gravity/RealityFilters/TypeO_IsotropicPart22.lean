-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart22.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart21

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
The F_12 component of the FLRW curvature evaluates strictly to the [A_1, A_2] commutator.
-/
lemma typeO_F_1_2 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (typeO_A a) 1 2 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (typeO_A a) 1 2 x (typeO_A_differentiable a 1 x ha) (typeO_A_differentiable a 2 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 1 (fun p => (typeO_A a 2 p).val i j) x = 0 := by
    have hk : (1 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_typeO_L_k_2 a 1 x hk ha
    have h_eq : (fun p => (typeO_A a 2 p).val i j) = fun p => typeO_L a 2 p i j := by ext p; rw [typeO_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 1 (fun p => typeO_L a 2 p i j) x = partialDerivMat 1 (fun p => typeO_L a 2 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have hd1 : partialDeriv 2 (fun p => (typeO_A a 1 p).val i j) x = 0 := by
    have hk : (2 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_typeO_L_k_1 a 2 x hk ha
    have h_eq : (fun p => (typeO_A a 1 p).val i j) = fun p => typeO_L a 1 p i j := by ext p; rw [typeO_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 2 (fun p => typeO_L a 1 p i j) x = partialDerivMat 2 (fun p => typeO_L a 1 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((typeO_A a 1 x).val * (typeO_A a 2 x).val - (typeO_A a 2 x).val * (typeO_A a 1 x).val) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val) i j := by
    have h1 : (typeO_A a 1 x).val = typeO_L a 1 x := typeO_A_val_eq a 1 x
    have h2 : (typeO_A a 2 x).val = typeO_L a 2 x := typeO_A_val_eq a 2 x
    rw [h1, h2]
    have h_comm_mat := typeO_L_comm_1_2 a x
    have h_eval : (typeO_L a 1 x * typeO_L a 2 x - typeO_L a 2 x * typeO_L a 1 x) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val) i j := by rw [h_comm_mat]
    exact h_eval
  rw [hd0, hd1, h_comm]
  simp only [sub_zero, zero_add]

end CGD.Gravity.RealityFilters

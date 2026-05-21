-- FILENAME: CGD/Foundations/TensorCalculus/GaugeTransform/Invariance.lean

import CGD.Foundations.TensorCalculus.GaugeTransform.Covariance

set_option linter.unusedSimpArgs false

open Matrix Complex BigOperators Litlib.Y2003.nakahara2003geometry

namespace CGD.Foundations

Litlib.theorem
  description "Gauge Invariance of the Curvature Trace"
/--
The trace of the square of the curvature tensor is invariant under gauge transformations.
-/
theorem gauge_transform_curvature_trace (A B : Fin 4 → SpacetimePoint → SL2C) :
  isGaugeTransform A B →
  ∀ x mu nu, Matrix.trace ((curvatureSl2c A mu nu x).val * (curvatureSl2c A mu nu x).val) =
             Matrix.trace ((curvatureSl2c B mu nu x).val * (curvatureSl2c B mu nu x).val) := by
  intro h x mu nu
  rcases h with ⟨hA_smooth, U, U_inv, hU_smooth, hUinv_smooth, h_inv1, h_inv2, h_B⟩
  have hcov := gauge_curvature_covariance A B hA_smooth U U_inv hU_smooth hUinv_smooth h_inv1 h_inv2 h_B x mu nu
  
  let A_x := (curvatureSl2c A mu nu x).val
  let B_x := (curvatureSl2c B mu nu x).val
  let U_x := U x
  let Uinv_x := U_inv x
  
  have h_B_eq : B_x = U_x * A_x * Uinv_x := hcov
  
  have h_B_B : B_x * B_x = U_x * (A_x * A_x) * Uinv_x := by
    calc B_x * B_x = (U_x * A_x * Uinv_x) * (U_x * A_x * Uinv_x) := by rw [h_B_eq]
      _ = U_x * A_x * (Uinv_x * U_x) * A_x * Uinv_x := by simp only [Matrix.mul_assoc]
      _ = U_x * A_x * 1 * A_x * Uinv_x := by rw [h_inv2 x]
      _ = U_x * (A_x * A_x) * Uinv_x := by simp only [Matrix.mul_one, Matrix.mul_assoc]
      
  symm
  calc Matrix.trace (B_x * B_x) = Matrix.trace (U_x * (A_x * A_x) * Uinv_x) := by rw [h_B_B]
    _ = Matrix.trace (U_x * ((A_x * A_x) * Uinv_x)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (((A_x * A_x) * Uinv_x) * U_x) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((A_x * A_x) * (Uinv_x * U_x)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace ((A_x * A_x) * 1) := by rw [h_inv2 x]
    _ = Matrix.trace (A_x * A_x) := by rw [Matrix.mul_one]

end CGD.Foundations

-- FILENAME: CGD/Foundations/TensorCalculus/GaugeTransform.lean

import CGD.Foundations.TensorCalculus.DifferentialRules
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option linter.unusedVariables false

open Matrix Complex BigOperators CGD.Axioms Litlib.Y2003.nakahara2003geometry

namespace CGD.Foundations

/-- 
Secured Gauge Transform: Mathematically prevents two critical topological trapdoors:
1. Prevents the trivial U=0 collapse by rigorously requiring det U ≠ 0.
2. Prevents discontinuous mappings by rigorously requiring `ContDiff` (smoothness)
   for all matrix components of U across the entire manifold. A discontinuous 
   gauge transformation would physically destroy the integrity of the calculus.
-/
def isGaugeTransform (A B : Fin 4 → SpacetimePoint → SL2C) : Prop :=
  ∃ U : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ, 
    (∀ i j, ContDiff ℝ ⊤ (fun x => (U x) i j)) ∧
    (∀ x, Matrix.det (U x) ≠ 0) ∧
    ∀ x mu nu, (curvatureSl2c B mu nu x).val * U x = U x * (curvatureSl2c A mu nu x).val

theorem gauge_transform_curvature_trace (A B : Fin 4 → SpacetimePoint → SL2C) :
  isGaugeTransform A B →
  ∀ x mu nu, Matrix.trace ((curvatureSl2c A mu nu x).val * (curvatureSl2c A mu nu x).val) =
             Matrix.trace ((curvatureSl2c B mu nu x).val * (curvatureSl2c B mu nu x).val) := by
  intro h x mu nu
  rcases h with ⟨U, h_smooth, hdet, hcomm⟩
  let U_x := U x
  have hdet_unit : IsUnit (Matrix.det U_x) := isUnit_iff_ne_zero.mpr (hdet x)
  have h_inv1 : U_x * U_x⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet_unit
  have h_inv2 : U_x⁻¹ * U_x = 1 := Matrix.nonsing_inv_mul _ hdet_unit
  let A_x := (curvatureSl2c A mu nu x).val
  let B_x := (curvatureSl2c B mu nu x).val
  have h_B_eq : B_x = U_x * A_x * U_x⁻¹ := by
    calc B_x = B_x * 1 := by rw [Matrix.mul_one]
      _ = B_x * (U_x * U_x⁻¹) := by rw [←h_inv1]
      _ = (B_x * U_x) * U_x⁻¹ := by rw [Matrix.mul_assoc]
      _ = (U_x * A_x) * U_x⁻¹ := by rw [hcomm x mu nu]
      _ = U_x * A_x * U_x⁻¹ := by rw [Matrix.mul_assoc]
  have h_B_B : B_x * B_x = U_x * (A_x * A_x) * U_x⁻¹ := by
    calc B_x * B_x = (U_x * A_x * U_x⁻¹) * (U_x * A_x * U_x⁻¹) := by rw [h_B_eq]
      _ = U_x * A_x * (U_x⁻¹ * U_x) * A_x * U_x⁻¹ := by simp only [Matrix.mul_assoc]
      _ = U_x * A_x * 1 * A_x * U_x⁻¹ := by rw [h_inv2]
      _ = U_x * (A_x * A_x) * U_x⁻¹ := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  symm
  calc Matrix.trace (B_x * B_x) = Matrix.trace (U_x * (A_x * A_x) * U_x⁻¹) := by rw [h_B_B]
    _ = Matrix.trace (U_x * ((A_x * A_x) * U_x⁻¹)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (((A_x * A_x) * U_x⁻¹) * U_x) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((A_x * A_x) * (U_x⁻¹ * U_x)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace ((A_x * A_x) * 1) := by rw [h_inv2]
    _ = Matrix.trace (A_x * A_x) := by rw [Matrix.mul_one]

end CGD.Foundations

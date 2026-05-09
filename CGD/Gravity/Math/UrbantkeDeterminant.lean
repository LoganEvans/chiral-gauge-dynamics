-- FILENAME: CGD/Gravity/Math/UrbantkeDeterminant.lean

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Litlib.Math.Matrix4

namespace CGD.Gravity.Math

open Matrix

/--
A flattened algebraic identity for the Laplace Expansion of a 4x4 matrix
by its top two rows. Pre-expanding this identity prevents combinatorial OOM 
explosions when substituting complex wedge product constraints into the minors.
-/
lemma laplace_expansion_4 {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
  M.det =
    (M 0 0 * M 1 1 - M 0 1 * M 1 0) * (M 2 2 * M 3 3 - M 2 3 * M 3 2)
  - (M 0 0 * M 1 2 - M 0 2 * M 1 0) * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
  + (M 0 0 * M 1 3 - M 0 3 * M 1 0) * (M 2 1 * M 3 2 - M 2 2 * M 3 1)
  + (M 0 1 * M 1 2 - M 0 2 * M 1 1) * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
  - (M 0 1 * M 1 3 - M 0 3 * M 1 1) * (M 2 0 * M 3 2 - M 2 2 * M 3 0)
  + (M 0 2 * M 1 3 - M 0 3 * M 1 2) * (M 2 0 * M 3 1 - M 2 1 * M 3 0) := by
  rw [Litlib.Math.Matrix4.expand_det_4 M]
  ring

/--
Evaluates the abstract $g_{\mu\nu}$ metric determinant constraint via Memoized Laplace Expansion.
-/
theorem urbantke_det_eq_lambda_pow_4
  {X R : Type*} [CommRing R]
  (g : X → Matrix (Fin 4) (Fin 4) R)
  (Λ : R)
  (h_constraint : ∀ x i j, g x i j = if i = j then Λ else 0) :
  ∀ x, (g x).det = Λ ^ 4 := by
  intro x

  -- 2. Compute the 16 individual components of g_μν.
  -- 3. Crucial: Apply the Λ constraints to simplify these components individually before proceeding.
  have h_g00 : g x 0 0 = Λ := by simp [h_constraint]
  have h_g01 : g x 0 1 = 0 := by simp [h_constraint]
  have h_g02 : g x 0 2 = 0 := by simp [h_constraint]
  have h_g03 : g x 0 3 = 0 := by simp [h_constraint]

  have h_g10 : g x 1 0 = 0 := by simp [h_constraint]
  have h_g11 : g x 1 1 = Λ := by simp [h_constraint]
  have h_g12 : g x 1 2 = 0 := by simp [h_constraint]
  have h_g13 : g x 1 3 = 0 := by simp [h_constraint]

  have h_g20 : g x 2 0 = 0 := by simp [h_constraint]
  have h_g21 : g x 2 1 = 0 := by simp [h_constraint]
  have h_g22 : g x 2 2 = Λ := by simp [h_constraint]
  have h_g23 : g x 2 3 = 0 := by simp [h_constraint]

  have h_g30 : g x 3 0 = 0 := by simp [h_constraint]
  have h_g31 : g x 3 1 = 0 := by simp [h_constraint]
  have h_g32 : g x 3 2 = 0 := by simp [h_constraint]
  have h_g33 : g x 3 3 = Λ := by simp [h_constraint]

  -- 4. Compute the six 2x2 minors of the top half
  have minor01_01 : g x 0 0 * g x 1 1 - g x 0 1 * g x 1 0 = Λ * Λ := by rw [h_g00, h_g11, h_g01, h_g10]; ring
  have minor01_02 : g x 0 0 * g x 1 2 - g x 0 2 * g x 1 0 = 0 := by rw [h_g00, h_g12, h_g02, h_g10]; ring
  have minor01_03 : g x 0 0 * g x 1 3 - g x 0 3 * g x 1 0 = 0 := by rw [h_g00, h_g13, h_g03, h_g10]; ring
  have minor01_12 : g x 0 1 * g x 1 2 - g x 0 2 * g x 1 1 = 0 := by rw [h_g01, h_g12, h_g02, h_g11]; ring
  have minor01_13 : g x 0 1 * g x 1 3 - g x 0 3 * g x 1 1 = 0 := by rw [h_g01, h_g13, h_g03, h_g11]; ring
  have minor01_23 : g x 0 2 * g x 1 3 - g x 0 3 * g x 1 2 = 0 := by rw [h_g02, h_g13, h_g03, h_g12]; ring

  -- 5. Compute the six 2x2 minors of the bottom half
  have minor23_01 : g x 2 0 * g x 3 1 - g x 2 1 * g x 3 0 = 0 := by rw [h_g20, h_g31, h_g21, h_g30]; ring
  have minor23_02 : g x 2 0 * g x 3 2 - g x 2 2 * g x 3 0 = 0 := by rw [h_g20, h_g32, h_g22, h_g30]; ring
  have minor23_03 : g x 2 0 * g x 3 3 - g x 2 3 * g x 3 0 = 0 := by rw [h_g20, h_g33, h_g23, h_g30]; ring
  have minor23_12 : g x 2 1 * g x 3 2 - g x 2 2 * g x 3 1 = 0 := by rw [h_g21, h_g32, h_g22, h_g31]; ring
  have minor23_13 : g x 2 1 * g x 3 3 - g x 2 3 * g x 3 1 = 0 := by rw [h_g21, h_g33, h_g23, h_g31]; ring
  have minor23_23 : g x 2 2 * g x 3 3 - g x 2 3 * g x 3 2 = Λ * Λ := by rw [h_g22, h_g33, h_g23, h_g32]; ring

  -- 6. Assemble the 4x4 determinant using the Laplace expansion of these pre-computed minors
  rw [laplace_expansion_4 (g x)]
  rw [minor01_01, minor23_23, minor01_02, minor23_13, minor01_03, minor23_12]
  rw [minor01_12, minor23_03, minor01_13, minor23_02, minor01_23, minor23_01]
  ring

/--
7. Prove that because the components are constants (proportional to Λ), 
the spatial derivative of the combined block is 0 (formalized via an invariant difference).
-/
theorem urbantke_det_derivative_zero
  {X R : Type*} [CommRing R]
  (g : X → Matrix (Fin 4) (Fin 4) R)
  (Λ : R)
  (h_constraint : ∀ x i j, g x i j = if i = j then Λ else 0) :
  ∀ x y, (g x).det - (g y).det = 0 := by
  intro x y
  rw [urbantke_det_eq_lambda_pow_4 g Λ h_constraint x]
  rw [urbantke_det_eq_lambda_pow_4 g Λ h_constraint y]
  ring

end CGD.Gravity.Math

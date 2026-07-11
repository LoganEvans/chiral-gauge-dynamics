-- FILENAME: CGD/Foundations/TensorCalculus/GaugeTransform/Core.lean

import CGD.Foundations.TensorCalculus.GaugeTransform.CalculusHelpers

open CGD.Math

set_option linter.unusedSimpArgs false

open Matrix Complex BigOperators Litlib.Y2003.nakahara2003geometry

namespace CGD.Foundations

/--
A mathematically rigorous definition of a gauge transformation, requiring invertible and globally smooth mappings to preserve the integrity of the differential calculus.
-/
def isGaugeTransform (A B : Fin 4 → SpacetimePoint → SL2C) : Prop :=
  (∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j)) ∧
  ∃ U U_inv : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ,
    (∀ i j, ContDiff ℝ ⊤ (fun x => (U x) i j)) ∧
    (∀ i j, ContDiff ℝ ⊤ (fun x => (U_inv x) i j)) ∧
    (∀ x, U x * U_inv x = 1) ∧
    (∀ x, U_inv x * U x = 1) ∧
    ∀ x mu, (B mu x).val = U x * (A mu x).val * U_inv x + U x * partialDerivMat mu U_inv x

lemma diff_UAV (U A V : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (x : SpacetimePoint)
  (hU : ∀ i j, DifferentiableAt ℝ (fun p => U p i j) x)
  (hA : ∀ i j, DifferentiableAt ℝ (fun p => A p i j) x)
  (hV : ∀ i j, DifferentiableAt ℝ (fun p => V p i j) x) :
  ∀ i j, DifferentiableAt ℝ (fun p => (U p * A p * V p) i j) x := by
  intro i j
  exact diff_matrix_mul (fun p => U p * A p) V x (diff_matrix_mul U A x hU hA) hV i j

lemma diff_UdV (U dV : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (x : SpacetimePoint)
  (hU : ∀ i j, DifferentiableAt ℝ (fun p => U p i j) x)
  (hdV : ∀ i j, DifferentiableAt ℝ (fun p => dV p i j) x) :
  ∀ i j, DifferentiableAt ℝ (fun p => (U p * dV p) i j) x := by
  intro i j
  exact diff_matrix_mul U dV x hU hdV i j

lemma d_mu_B_nu_expansion (mu nu : Fin 4) (x : SpacetimePoint)
  (A_nu : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ)
  (U U_inv : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ)
  (hdU : ∀ i j, DifferentiableAt ℝ (fun p => U p i j) x)
  (hdA_nu : ∀ i j, DifferentiableAt ℝ (fun p => A_nu p i j) x)
  (hdUinv : ∀ i j, DifferentiableAt ℝ (fun p => U_inv p i j) x)
  (hddUinv_nu : ∀ i j, DifferentiableAt ℝ (fun p => partialDerivMat nu U_inv p i j) x) :
  partialDerivMat mu (fun p => U p * A_nu p * U_inv p + U p * partialDerivMat nu U_inv p) x =
  partialDerivMat mu U x * A_nu x * U_inv x +
  U x * partialDerivMat mu A_nu x * U_inv x +
  U x * A_nu x * partialDerivMat mu U_inv x +
  (partialDerivMat mu U x * partialDerivMat nu U_inv x + U x * partialDerivMat mu (fun p => partialDerivMat nu U_inv p) x) := by
  have h_left_diff := diff_UAV U A_nu U_inv x hdU hdA_nu hdUinv
  have h_right_diff := diff_UdV U (fun p => partialDerivMat nu U_inv p) x hdU hddUinv_nu
  rw [partialDerivMat_add (fun p => U p * A_nu p * U_inv p) (fun p => U p * partialDerivMat nu U_inv p) mu x h_left_diff h_right_diff]
  rw [partialDerivMat_mul3 mu U A_nu U_inv x hdU hdA_nu hdUinv]
  rw [partialDerivMat_mul U (fun p => partialDerivMat nu U_inv p) mu x hdU hddUinv_nu]

end CGD.Foundations

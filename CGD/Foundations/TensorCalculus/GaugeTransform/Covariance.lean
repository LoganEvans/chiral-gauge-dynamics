-- FILENAME: CGD/Foundations/TensorCalculus/GaugeTransform/Covariance.lean

import CGD.Foundations.TensorCalculus.GaugeTransform.Core
import CGD.Foundations.TensorCalculus.GaugeTransform.AlgebraHelpers

set_option linter.unusedSimpArgs false

open Matrix Complex BigOperators Litlib.Y2003.nakahara2003geometry

namespace CGD.Foundations

lemma gauge_curvature_covariance (A B : Fin 4 → SpacetimePoint → SL2C)
  (hA_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (U U_inv : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ)
  (hU_smooth : ∀ i j, ContDiff ℝ ⊤ (fun x => (U x) i j))
  (hUinv_smooth : ∀ i j, ContDiff ℝ ⊤ (fun x => (U_inv x) i j))
  (h_inv1 : ∀ x, U x * U_inv x = 1)
  (h_inv2 : ∀ x, U_inv x * U x = 1)
  (h_B : ∀ x mu, (B mu x).val = U x * (A mu x).val * U_inv x + U x * partialDerivMat mu U_inv x) :
  ∀ x mu nu, (curvatureSl2c B mu nu x).val = U x * (curvatureSl2c A mu nu x).val * U_inv x := by
  intro x mu nu

  have hdU : ∀ i j, DifferentiableAt ℝ (fun p => (U p) i j) x := fun i j => (hU_smooth i j).differentiable (by decide) x
  have hdUinv : ∀ i j, DifferentiableAt ℝ (fun p => (U_inv p) i j) x := fun i j => (hUinv_smooth i j).differentiable (by decide) x
  have hdA_mu : ∀ i j, DifferentiableAt ℝ (fun p => (A mu p).val i j) x := fun i j => (hA_smooth mu i j).differentiable (by decide) x
  have hdA_nu : ∀ i j, DifferentiableAt ℝ (fun p => (A nu p).val i j) x := fun i j => (hA_smooth nu i j).differentiable (by decide) x
  have hddUinv_mu : ∀ i j, DifferentiableAt ℝ (fun p => partialDerivMat mu U_inv p i j) x := diff_partial_mat U_inv hUinv_smooth mu x
  have hddUinv_nu : ∀ i j, DifferentiableAt ℝ (fun p => partialDerivMat nu U_inv p i j) x := diff_partial_mat U_inv hUinv_smooth nu x

  let U_x := U x
  let V_x := U_inv x
  let A_mu := (A mu x).val
  let A_nu := (A nu x).val
  let d_mu_A_nu := partialDerivMat mu (fun p => (A nu p).val) x
  let d_nu_A_mu := partialDerivMat nu (fun p => (A mu p).val) x
  let d_mu_U := partialDerivMat mu U x
  let d_nu_U := partialDerivMat nu U x
  let d_mu_V := partialDerivMat mu U_inv x
  let d_nu_V := partialDerivMat nu U_inv x
  let d_mu_d_nu_V := partialDerivMat mu (fun p => partialDerivMat nu U_inv p) x
  let d_nu_d_mu_V := partialDerivMat nu (fun p => partialDerivMat mu U_inv p) x

  have hdB_nu : partialDerivMat mu (fun p => (B nu p).val) x = d_mu_U * A_nu * V_x + U_x * d_mu_A_nu * V_x + U_x * A_nu * d_mu_V + (d_mu_U * d_nu_V + U_x * d_mu_d_nu_V) := by
    have h_B_nu_eq : (fun p => (B nu p).val) = fun p => U p * (A nu p).val * U_inv p + U p * partialDerivMat nu U_inv p := funext (fun p => h_B p nu)
    rw [h_B_nu_eq]
    exact d_mu_B_nu_expansion mu nu x (fun p => (A nu p).val) U U_inv hdU hdA_nu hdUinv hddUinv_nu

  have hdB_mu : partialDerivMat nu (fun p => (B mu p).val) x = d_nu_U * A_mu * V_x + U_x * d_nu_A_mu * V_x + U_x * A_mu * d_nu_V + (d_nu_U * d_mu_V + U_x * d_nu_d_mu_V) := by
    have h_B_mu_eq : (fun p => (B mu p).val) = fun p => U p * (A mu p).val * U_inv p + U p * partialDerivMat mu U_inv p := funext (fun p => h_B p mu)
    rw [h_B_mu_eq]
    exact d_mu_B_nu_expansion nu mu x (fun p => (A mu p).val) U U_inv hdU hdA_mu hdUinv hddUinv_mu

  have h_B_mu_B_nu : (B mu x).val * (B nu x).val = U_x * (A_mu * A_nu) * V_x + U_x * A_mu * d_nu_V - d_mu_U * A_nu * V_x - d_mu_U * d_nu_V := by
    have h1 : (B mu x).val = U_x * A_mu * V_x + U_x * d_mu_V := h_B x mu
    have h2 : (B nu x).val = U_x * A_nu * V_x + U_x * d_nu_V := h_B x nu
    rw [h1, h2]
    exact matrix_gauge_mul U_x V_x A_mu A_nu d_mu_V d_nu_V d_mu_U (h_inv2 x) (diff_inv_identity mu U U_inv x hdU hdUinv h_inv1)

  have h_B_nu_B_mu : (B nu x).val * (B mu x).val = U_x * (A_nu * A_mu) * V_x + U_x * A_nu * d_mu_V - d_nu_U * A_mu * V_x - d_nu_U * d_mu_V := by
    have h1 : (B nu x).val = U_x * A_nu * V_x + U_x * d_nu_V := h_B x nu
    have h2 : (B mu x).val = U_x * A_mu * V_x + U_x * d_mu_V := h_B x mu
    rw [h1, h2]
    exact matrix_gauge_mul U_x V_x A_nu A_mu d_nu_V d_mu_V d_nu_U (h_inv2 x) (diff_inv_identity nu U U_inv x hdU hdUinv h_inv1)

  have h_sum_nu : partialDerivMat mu (fun p => (B nu p).val) x + (B mu x).val * (B nu x).val = U_x * d_mu_A_nu * V_x + U_x * A_nu * d_mu_V + U_x * d_mu_d_nu_V + U_x * (A_mu * A_nu) * V_x + U_x * A_mu * d_nu_V := by
    rw [hdB_nu, h_B_mu_B_nu]
    exact gauge_algebra_simplify U_x V_x A_mu A_nu d_mu_A_nu d_mu_U d_mu_V d_nu_V d_mu_d_nu_V

  have h_sum_mu : partialDerivMat nu (fun p => (B mu p).val) x + (B nu x).val * (B mu x).val = U_x * d_nu_A_mu * V_x + U_x * A_mu * d_nu_V + U_x * d_nu_d_mu_V + U_x * (A_nu * A_mu) * V_x + U_x * A_nu * d_mu_V := by
    rw [hdB_mu, h_B_nu_B_mu]
    exact gauge_algebra_simplify U_x V_x A_nu A_mu d_nu_A_mu d_nu_U d_nu_V d_mu_V d_nu_d_mu_V

  have h_schwarz : d_mu_d_nu_V = d_nu_d_mu_V := partialDerivMat_commutes U_inv mu nu x hUinv_smooth

  have h_eval : U_x * d_mu_A_nu * V_x + U_x * A_nu * d_mu_V + U_x * d_mu_d_nu_V + U_x * (A_mu * A_nu) * V_x + U_x * A_mu * d_nu_V - (U_x * d_nu_A_mu * V_x + U_x * A_mu * d_nu_V + U_x * d_nu_d_mu_V + U_x * (A_nu * A_mu) * V_x + U_x * A_nu * d_mu_V) = U_x * (d_mu_A_nu - d_nu_A_mu + (A_mu * A_nu - A_nu * A_mu)) * V_x := by
    rw [h_schwarz]
    exact gauge_algebra_antisymm U_x V_x d_mu_A_nu d_nu_A_mu d_mu_V d_nu_V d_nu_d_mu_V A_mu A_nu

  have hdB_mu_smooth : ∀ i j, DifferentiableAt ℝ (fun p => (B mu p).val i j) x := by
    intro i j
    have h_B_mu_eq : (fun p => (B mu p).val i j) = fun p => (U p * (A mu p).val * U_inv p + U p * partialDerivMat mu U_inv p) i j := by funext p; rw [h_B p mu]
    rw [h_B_mu_eq]
    have hleft := diff_UAV U (fun p => (A mu p).val) U_inv x hdU hdA_mu hdUinv
    have hright := diff_UdV U (fun p => partialDerivMat mu U_inv p) x hdU hddUinv_mu
    exact DifferentiableAt.add (hleft i j) (hright i j)

  have hdB_nu_smooth : ∀ i j, DifferentiableAt ℝ (fun p => (B nu p).val i j) x := by
    intro i j
    have h_B_nu_eq : (fun p => (B nu p).val i j) = fun p => (U p * (A nu p).val * U_inv p + U p * partialDerivMat nu U_inv p) i j := by funext p; rw [h_B p nu]
    rw [h_B_nu_eq]
    have hleft := diff_UAV U (fun p => (A nu p).val) U_inv x hdU hdA_nu hdUinv
    have hright := diff_UdV U (fun p => partialDerivMat nu U_inv p) x hdU hddUinv_nu
    exact DifferentiableAt.add (hleft i j) (hright i j)

  calc (curvatureSl2c B mu nu x).val
    _ = partialDerivMat mu (fun p => (B nu p).val) x - partialDerivMat nu (fun p => (B mu p).val) x + ((B mu x).val * (B nu x).val - (B nu x).val * (B mu x).val) := curvature_val_expansion B mu nu x hdB_mu_smooth hdB_nu_smooth
    _ = (partialDerivMat mu (fun p => (B nu p).val) x + (B mu x).val * (B nu x).val) - (partialDerivMat nu (fun p => (B mu p).val) x + (B nu x).val * (B mu x).val) := by abel
    _ = U_x * d_mu_A_nu * V_x + U_x * A_nu * d_mu_V + U_x * d_mu_d_nu_V + U_x * (A_mu * A_nu) * V_x + U_x * A_mu * d_nu_V - (U_x * d_nu_A_mu * V_x + U_x * A_mu * d_nu_V + U_x * d_nu_d_mu_V + U_x * (A_nu * A_mu) * V_x + U_x * A_nu * d_mu_V) := by rw [h_sum_nu, h_sum_mu]
    _ = U_x * (d_mu_A_nu - d_nu_A_mu + (A_mu * A_nu - A_nu * A_mu)) * V_x := h_eval
    _ = U_x * (partialDerivMat mu (fun p => (A nu p).val) x - partialDerivMat nu (fun p => (A mu p).val) x + ((A mu x).val * (A nu x).val - (A nu x).val * (A mu x).val)) * V_x := by rfl
    _ = U_x * (curvatureSl2c A mu nu x).val * V_x := by rw [← curvature_val_expansion A mu nu x hdA_mu hdA_nu]

end CGD.Foundations

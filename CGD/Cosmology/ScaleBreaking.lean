-- FILENAME: CGD/Cosmology/ScaleBreaking.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Foundations.GaugeGroup
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

open Complex Matrix CGD.Gravity CGD.Foundations

namespace CGD.Cosmology

lemma val_to_sl2c_smul (c : ℂ) (M : SL2C) :
  (toSl2c (c • M.val)).val = c • M.val := by
  unfold toSl2c
  have tr_zero : Matrix.trace (c • M.val) = 0 := by
    rw [Matrix.trace_smul]
    have h_trace : Matrix.trace M.val = 0 := (mem_sl_iff M.val).mp M.property
    rw [h_trace, smul_zero]
  simp [tr_zero]

lemma project_scaled (F : Fin 4 → Fin 4 → SL2C) (lambda_sq : ℂ) (a : Fin 3) (μ α : Fin 4) :
  project (fun m n => toSl2c (lambda_sq • (F m n).val)) a μ α = lambda_sq * project F a μ α := by
  unfold project
  dsimp
  rw[val_to_sl2c_smul]
  have h_mul : (lambda_sq • (F μ α).val) * (getPauli a).val = lambda_sq • ((F μ α).val * (getPauli a).val) := by
    ext i j
    simp[Matrix.mul_apply]
    ring
  rw [h_mul]
  rw[Matrix.trace_smul]
  rw [smul_eq_mul]
  ring

/--
The Urbantke metric natively breaks conformal symmetry at the classical level. A scale transformation of the field strength tensor results in a non-trivial scaling of the emergent metric.
-/
theorem kinematicClassicalScaleBreaking (F : Fin 4 → Fin 4 → SL2C) (lambda_scale : ℂ) :
  let F_scaled := fun μ ν => toSl2c (lambda_scale^2 • (F μ ν).val);
  (∀ μ ν, urbantkeMetric F_scaled μ ν = lambda_scale^6 * urbantkeMetric F μ ν) ∧
  (urbantkeMetric F_scaled).det = lambda_scale^24 * (urbantkeMetric F).det := by
  intro F_scaled
  have h_metric : ∀ μ ν, urbantkeMetric F_scaled μ ν = lambda_scale^6 * urbantkeMetric F μ ν := by
    intros μ ν
    unfold urbantkeMetric
    dsimp only[F_scaled]
    simp_rw [project_scaled]
    have h_ring : ∀ α β γ δ a b c,
      epsilon4 α β γ δ * (lambda_scale^2 * project F a μ α) * (lambda_scale^2 * project F b ν β) * (lambda_scale^2 * project F c γ δ) =
      lambda_scale^6 * (epsilon4 α β γ δ * project F a μ α * project F b ν β * project F c γ δ) := by intros; ring
    simp_rw [h_ring]
    simp_rw [← Finset.mul_sum]
    have h_ring2 : ∀ a b c X, epsilon3 a b c * (lambda_scale^6 * X) = lambda_scale^6 * (epsilon3 a b c * X) := by intros; ring
    simp_rw [h_ring2]
    simp_rw [← Finset.mul_sum]

  constructor
  · exact h_metric
  · have h_matrix_eq : urbantkeMetric F_scaled = lambda_scale^6 • urbantkeMetric F := by
      ext μ ν
      rw [h_metric μ ν]
      rfl
    rw[h_matrix_eq]
    have h_det := Matrix.det_smul (urbantkeMetric F) (lambda_scale^6)
    have h_card : Fintype.card (Fin 4) = 4 := rfl
    rw [h_card] at h_det
    rw[h_det]
    have h_pow : (lambda_scale^6)^4 = lambda_scale^24 := by ring
    rw [h_pow]

end CGD.Cosmology

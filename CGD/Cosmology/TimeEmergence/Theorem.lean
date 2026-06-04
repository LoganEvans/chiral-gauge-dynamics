-- FILENAME: CGD/Cosmology/TimeEmergence/Theorem.lean

import CGD.Cosmology.TimeEmergence.UrbantkeAlgebra
import CGD.Axioms.PhysicalUniverse

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Cosmology

noncomputable def pPoly (F : Fin 4 → Fin 4 → SL2C) : Matrix (Fin 4) (Fin 4) ℂ :=
  let P0 := pMat (bField F 0 0) (bField F 0 1) (bField F 0 2)
  let P1 := pMat (bField F 1 0) (bField F 1 1) (bField F 1 2)
  let P2 := pMat (bField F 2 0) (bField F 2 1) (bField F 2 2)
  (2 : ℂ) • (P0 * P1 * P2 - P0 * P2 * P1 - P1 * P0 * P2 + P1 * P2 * P0 + P2 * P0 * P1 - P2 * P1 * P0)

lemma P_poly_prop_id (F : Fin 4 → Fin 4 → SL2C) :
  ∃ (c : Complex), pPoly F = c • (1 : Matrix (Fin 4) (Fin 4) Complex) := by
  unfold pPoly
  apply P_poly_is_id

lemma urbantke_eq_P_poly (F : Fin 4 → Fin 4 → SL2C) (h_symm : isFully4DSymmetric F) :
  urbantkeMetric F = pPoly F := by
  ext μ ν
  rw [urbantke_metric_collapsed F h_symm]

  have h_sum_rearrange :
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ α : Fin 4, ∑ β : Fin 4,
      epsilon3 a b c * (2 * project F a μ α * project F b ν β * project F c α β)) =
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (∑ α : Fin 4, ∑ β : Fin 4, 2 * project F a μ α * project F b ν β * project F c α β)) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro α _
    rw [Finset.mul_sum]

  rw[h_sum_rearrange]

  have h_eps := eval_eps3_sum (fun a b c => ∑ α : Fin 4, ∑ β : Fin 4, 2 * project F a μ α * project F b ν β * project F c α β)
  rw [h_eps]

  have h_anti0 : ∀ i j, project F 0 i j = - project F 0 j i := project_anti F h_symm 0
  have h_anti1 : ∀ i j, project F 1 i j = - project F 1 j i := project_anti F h_symm 1
  have h_anti2 : ∀ i j, project F 2 i j = - project F 2 j i := project_anti F h_symm 2

  rw[urbantke_symbolic_collapse (project F 0) (project F 1) (project F 2) h_anti1 μ ν]
  rw[urbantke_symbolic_collapse (project F 0) (project F 2) (project F 1) h_anti2 μ ν]
  rw[urbantke_symbolic_collapse (project F 1) (project F 0) (project F 2) h_anti0 μ ν]
  rw[urbantke_symbolic_collapse (project F 1) (project F 2) (project F 0) h_anti2 μ ν]
  rw[urbantke_symbolic_collapse (project F 2) (project F 0) (project F 1) h_anti0 μ ν]
  rw[urbantke_symbolic_collapse (project F 2) (project F 1) (project F 0) h_anti1 μ ν]

  have eq0 : project F 0 = pMat (bField F 0 0) (bField F 0 1) (bField F 0 2) := by ext i j; exact project_eq_P_mat F h_symm 0 i j
  have eq1 : project F 1 = pMat (bField F 1 0) (bField F 1 1) (bField F 1 2) := by ext i j; exact project_eq_P_mat F h_symm 1 i j
  have eq2 : project F 2 = pMat (bField F 2 0) (bField F 2 1) (bField F 2 2) := by ext i j; exact project_eq_P_mat F h_symm 2 i j

  rw [eq0, eq1, eq2]
  unfold pPoly
  simp only[Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Matrix.neg_apply]
  ring

lemma urbantke_eq_smul_id_of_self_dual (F : Fin 4 → Fin 4 → SL2C)
  (h_symm : isFully4DSymmetric F) :
  ∃ (c : Complex), urbantkeMetric F = c • (1 : Matrix (Fin 4) (Fin 4) Complex) := by
  rcases P_poly_prop_id F with ⟨c, hc⟩
  use c
  rw[urbantke_eq_P_poly F h_symm]
  exact hc

lemma math_TimeIsChiralPhase_det (F : Fin 4 → Fin 4 → SL2C)
  (h_symm : isFully4DSymmetric F) :
  ¬ isLorentzian (urbantkeMetric F) := by
  have ⟨c, hc⟩ := urbantke_eq_smul_id_of_self_dual F h_symm
  rw [hc]
  unfold isLorentzian

  intro h_lor
  rcases h_lor with ⟨h_im, h_det_re, h_det_im⟩

  have h_det : (c • (1 : Matrix (Fin 4) (Fin 4) Complex)).det = c^4 := by simp
  rw [h_det] at h_det_re
  rw[h_det] at h_det_im

  have hc_re : c.im = 0 := by
    have h_c_val := h_im 0 0
    simp only[Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h_c_val
    exact h_c_val

  have hc_complex : c = (c.re : ℂ) := Complex.ext rfl hc_re
  rw[hc_complex] at h_det_re

  have h_pow_re : (((c.re : ℂ)^4).re) = c.re^4 := by
    have h_sq : (c.re : ℂ)^4 = ((c.re^4 : ℝ) : ℂ) := by push_cast; ring
    rw [h_sq]
    rfl

  rw [h_pow_re] at h_det_re
  have h_even : Even 4 := by decide
  have h_pos : 0 ≤ c.re^4 := Even.pow_nonneg h_even c.re
  linarith

Litlib.theorem
  description "Time Emergence via Symmetry Breaking"
/--
A fully 4D symmetric field tensor naturally yields a metric with a Euclidean or degenerate signature, forbidding the unique odd-sign axis required for a Lorentzian signature. Therefore, the Lorentzian time dimension emerges geometrically only when the gauge field spontaneously breaks 4D Euclidean (SO(4)) symmetry.
-/
theorem kinematicTimeEmergence (pu : PhysicalUniverse) (phaseRegion : Set SpacetimePoint)
  (h_symm : ∀ x ∈ phaseRegion, isFully4DSymmetric (fun mu nu => curvatureSl2c pu.toUniverse.sd_sector mu nu x)) :
  ∀ x ∈ phaseRegion,
    ¬ isLorentzian (urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.sd_sector m n x)) := by
  intro x hx
  have h_tic := h_symm x hx
  exact math_TimeIsChiralPhase_det (fun mu nu => curvatureSl2c pu.toUniverse.sd_sector mu nu x) h_tic

end CGD.Cosmology

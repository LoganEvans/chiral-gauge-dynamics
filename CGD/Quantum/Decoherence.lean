-- FILENAME: CGD/Quantum/Decoherence.lean

import Litlib.Core
import CGD.Foundations.GaugeGroup
import CGD.Quantum.Definitions
import CGD.Axioms.Ontology
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Quantum

private lemma trace_2x2 (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace A = A 0 0 + A 1 1 := by
  dsimp[Matrix.trace, Matrix.diag]; rw[Fin.sum_univ_two]

private lemma mul_2x2 (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw[Matrix.mul_apply, Fin.sum_univ_two]

@[simp] private lemma sigma_x_0_0 : sigmaX 0 0 = 0 := rfl
@[simp] private lemma sigma_x_0_1 : sigmaX 0 1 = 1 := rfl
@[simp] private lemma sigma_x_1_0 : sigmaX 1 0 = 1 := rfl
@[simp] private lemma sigma_x_1_1 : sigmaX 1 1 = 0 := rfl

@[simp] private lemma sigma_z_0_0 : sigmaZ 0 0 = 1 := rfl
@[simp] private lemma sigma_z_0_1 : sigmaZ 0 1 = 0 := rfl
@[simp] private lemma sigma_z_1_0 : sigmaZ 1 0 = 0 := rfl
@[simp] private lemma sigma_z_1_1 : sigmaZ 1 1 = -1 := rfl

/-- 🟡 PHENOMENOLOGICAL: Measurement Decoherence -/
theorem phenomenologicalMeasurementDecoherence (u : Universe) :
  ∀ (x : SpacetimePoint) (theta M : ℂ),
    isOrthogonalDecoherenceLimit u x theta M sigmaX sigmaZ →
    Matrix.trace ((curvatureSl2c u.light 1 2 x).val * (curvatureSl2c u.dark 1 2 x).val) = 0 →
    Complex.sin theta = 0 := by
  intros x theta M hLimit hTrace
  unfold isOrthogonalDecoherenceLimit at hLimit
  have hM := hLimit.1
  have hL := hLimit.2.1
  have hD := hLimit.2.2
  rw[hL, hD] at hTrace
  have h_tr : Matrix.trace ((Complex.cos theta • sigmaZ + Complex.sin theta • sigmaX) * (M • sigmaX)) = 2 * M * Complex.sin theta := by
    rw[trace_2x2]
    simp only[mul_2x2, Matrix.add_apply, Matrix.smul_apply, sigma_x_0_0, sigma_x_0_1, sigma_x_1_0, sigma_x_1_1, sigma_z_0_0, sigma_z_0_1, sigma_z_1_0, sigma_z_1_1, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    ring_nf
  rw[h_tr] at hTrace
  cases mul_eq_zero.mp hTrace with
  | inl h_2M =>
    cases mul_eq_zero.mp h_2M with
    | inl h2 =>
      have h_two : (2 : ℂ) ≠ 0 := by norm_num
      exact False.elim (h_two h2)
    | inr hM_eq => exact False.elim (hM hM_eq)
  | inr hSin =>
    exact hSin

lemma trace_wave (c1 c2 : ℂ) : (1/2 : ℂ) * Matrix.trace ((c1 • sigmaX + c2 • sigmaX) * (c1 • sigmaX + c2 • sigmaX)) = (c1 + c2)^2 := by
  rw[trace_2x2, mul_2x2, mul_2x2]
  change (1/2 : ℂ) * (
    ((c1 * sigmaX 0 0 + c2 * sigmaX 0 0) * (c1 * sigmaX 0 0 + c2 * sigmaX 0 0) +
     (c1 * sigmaX 0 1 + c2 * sigmaX 0 1) * (c1 * sigmaX 1 0 + c2 * sigmaX 1 0)) +
    ((c1 * sigmaX 1 0 + c2 * sigmaX 1 0) * (c1 * sigmaX 0 1 + c2 * sigmaX 0 1) +
     (c1 * sigmaX 1 1 + c2 * sigmaX 1 1) * (c1 * sigmaX 1 1 + c2 * sigmaX 1 1))
  ) = (c1 + c2)^2
  rw[sigma_x_0_0, sigma_x_0_1, sigma_x_1_0, sigma_x_1_1]
  ring

/-- 🟡 PHENOMENOLOGICAL: Double Slit Interference -/
theorem phenomenologicalWaveInterference (u : Universe) :
  ∀ (x : SpacetimePoint) (E0 phi_avg delta_phi : ℂ),
    isCoherentSuperpositionState u x E0 phi_avg delta_phi sigmaX →
    (1 / 2 : ℂ) * Matrix.trace ((curvatureSl2c u.light 1 2 x).val * (curvatureSl2c u.light 1 2 x).val) =
    4 * (E0 * E0) * (Complex.cos phi_avg * Complex.cos phi_avg) * (Complex.cos (delta_phi / 2) * Complex.cos (delta_phi / 2)) := by
  intros x E0 phi_avg delta_phi h
  unfold isCoherentSuperpositionState at h
  rw [h, trace_wave]
  have h_add : Complex.cos (phi_avg + delta_phi / 2) = Complex.cos phi_avg * Complex.cos (delta_phi / 2) - Complex.sin phi_avg * Complex.sin (delta_phi / 2) := Complex.cos_add _ _
  have h_sub : Complex.cos (phi_avg - delta_phi / 2) = Complex.cos phi_avg * Complex.cos (delta_phi / 2) + Complex.sin phi_avg * Complex.sin (delta_phi / 2) := Complex.cos_sub _ _
  rw[h_add, h_sub]
  ring

end CGD.Quantum

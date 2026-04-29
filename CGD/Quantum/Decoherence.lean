-- FILENAME: CGD/Quantum/Decoherence.lean

import Litlib.Core
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Lagrangian
import CGD.Foundations.TensorCalculus.DifferentialRules
import CGD.Quantum.Definitions
import CGD.Axioms.Ontology
import CGD.Gravity.Geometry
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

set_option linter.unusedSimpArgs false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Quantum

Litlib.theorem
  description "Measurement Decoherence Limit"
/-- 
In the orthogonal limit where the anti-self-dual measurement frame completely decouples from the self-dual observable (zero cross-trace), the continuous gauge parameter collapses precisely to the discrete eigenstates (sin(theta) = 0 -> theta = 0, pi).
-/
theorem phenomenologicalMeasurementDecoherence (u : Universe) :
  ∀ (x : SpacetimePoint) (theta M : ℂ),
    isOrthogonalDecoherenceLimit u x theta M sigmaX sigmaZ →
    Matrix.trace ((curvatureSl2c u.sd_sector 1 2 x).val * (curvatureSl2c u.asd_sector 1 2 x).val) = 0 →
    Complex.sin theta = 0 := by
  intro x theta M hLimit hTrace
  unfold isOrthogonalDecoherenceLimit at hLimit
  rcases hLimit with ⟨hM, hSD, hASD⟩
  rw [hSD, hASD] at hTrace
  
  have hXX : Matrix.trace (sigmaX * sigmaX) = 2 := by
    unfold Matrix.trace Matrix.diag
    simp [sigmaX, mkMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_succ, Fin.sum_univ_zero]
    ring

  have hZX : Matrix.trace (sigmaZ * sigmaX) = 0 := by
    unfold Matrix.trace Matrix.diag
    simp [sigmaZ, sigmaX, mkMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_succ, Fin.sum_univ_zero]

  have h_expand : Matrix.trace (((Complex.cos theta) • sigmaZ + (Complex.sin theta) • sigmaX) * (M • sigmaX)) = 
                  Complex.cos theta * M * Matrix.trace (sigmaZ * sigmaX) + Complex.sin theta * M * Matrix.trace (sigmaX * sigmaX) := by
    simp [Matrix.add_mul, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.trace_add, Matrix.trace_smul]
    ring

  rw [h_expand, hXX, hZX] at hTrace
  
  have h_eq : 2 * M * Complex.sin theta = 0 := by
    calc 2 * M * Complex.sin theta
      _ = Complex.cos theta * M * 0 + Complex.sin theta * M * 2 := by ring
      _ = 0 := hTrace
      
  cases mul_eq_zero.mp h_eq with
  | inl h2M =>
    cases mul_eq_zero.mp h2M with
    | inl h2 => 
      revert h2
      norm_num
    | inr hM_zero => 
      contradiction
  | inr hSin => exact hSin

end CGD.Quantum

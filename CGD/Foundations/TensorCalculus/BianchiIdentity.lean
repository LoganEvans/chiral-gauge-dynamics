-- FILENAME: CGD/Foundations/TensorCalculus/BianchiIdentity.lean

import CGD.Foundations.TensorCalculus.DifferentialRules
import CGD.Foundations.TensorCalculus.LieAlgebra

set_option linter.unusedVariables false

open Matrix Complex BigOperators CGD.Axioms Litlib.Y2003.nakahara2003geometry

namespace CGD.Foundations

theorem bianchiIdentity (A : Fin 4 → SpacetimePoint → SL2C)
  (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j))
  (ρ σ ν : Fin 4) (x : SpacetimePoint) :
  covariantDeriv A ρ σ ν x + covariantDeriv A σ ν ρ x + covariantDeriv A ν ρ σ x = 0 := by
  
  have h_diff_all : ∀ α i j y, DifferentiableAt ℝ (fun p => (A α p).val i j) y :=
    fun α i j y => ((h_smooth α i j).differentiable (by decide)) y
    
  have hdA : ∀ α i j, DifferentiableAt ℝ (fun p => (A α p).val i j) x :=
    fun α i j => h_diff_all α i j x
    
  have hd_dA : ∀ α β i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c α (A β) p).val i j) x := by
    intro α β i j
    have h_eq : (fun p => (partialDerivSl2c α (A β) p).val i j) = fun p => partialDeriv α (fun p2 => (A β p2).val i j) p := by
      ext p
      have h1 := partialDerivSl2c_eq_mat (A β) α p (fun i j => h_diff_all β i j p)
      exact congr_fun (congr_fun h1 i) j
    rw [h_eq]
    have h_deriv_smooth : ContDiff ℝ 1 (fderiv ℝ (fun p => (A β p).val i j)) := (h_smooth β i j).fderiv_right (by decide)
    have hd_deriv : DifferentiableAt ℝ (fderiv ℝ (fun p => (A β p).val i j)) x := (h_deriv_smooth.differentiable (by decide)) x
    have h_apply : (fun p => partialDeriv α (fun p2 => (A β p2).val i j) p) = (ContinuousLinearMap.apply ℝ ℂ ((Pi.single α (1 : ℝ)) : Fin 4 → ℝ)) ∘ (fderiv ℝ (fun p => (A β p).val i j)) := rfl
    rw [h_apply]
    exact DifferentiableAt.comp x (ContinuousLinearMap.apply ℝ ℂ ((Pi.single α (1 : ℝ)) : Fin 4 → ℝ)).differentiableAt hd_deriv

  have hdComm : ∀ α β i j, DifferentiableAt ℝ (fun p => (⁅A α p, A β p⁆).val i j) x := by
    intro α β i j
    have h_eq : (fun p => (⁅A α p, A β p⁆).val i j) = fun p => ((A α p).val * (A β p).val - (A β p).val * (A α p).val) i j := rfl
    rw [h_eq]
    have h_mul1 := diff_matrix_mul (fun p => (A α p).val) (fun p => (A β p).val) x (hdA α) (hdA β)
    have h_mul2 := diff_matrix_mul (fun p => (A β p).val) (fun p => (A α p).val) x (hdA β) (hdA α)
    exact diff_matrix_sub (fun p => (A α p).val * (A β p).val) (fun p => (A β p).val * (A α p).val) x h_mul1 h_mul2 i j

  have hdSub : ∀ α β i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c α (A β) p - partialDerivSl2c β (A α) p).val i j) x := by
    intro α β i j
    have h_eq : (fun p => (partialDerivSl2c α (A β) p - partialDerivSl2c β (A α) p).val i j) = fun p => (partialDerivSl2c α (A β) p).val i j - (partialDerivSl2c β (A α) p).val i j := rfl
    rw [h_eq]
    exact DifferentiableAt.sub (hd_dA α β i j) (hd_dA β α i j)

  unfold covariantDeriv curvatureSl2c
  
  rw [partialDerivSl2c_add (fun p => partialDerivSl2c σ (A ν) p - partialDerivSl2c ν (A σ) p) (fun p => ⁅A σ p, A ν p⁆) ρ x (hdSub σ ν) (hdComm σ ν)]
  rw [partialDerivSl2c_add (fun p => partialDerivSl2c ν (A ρ) p - partialDerivSl2c ρ (A ν) p) (fun p => ⁅A ν p, A ρ p⁆) σ x (hdSub ν ρ) (hdComm ν ρ)]
  rw [partialDerivSl2c_add (fun p => partialDerivSl2c ρ (A σ) p - partialDerivSl2c σ (A ρ) p) (fun p => ⁅A ρ p, A σ p⁆) ν x (hdSub ρ σ) (hdComm ρ σ)]

  rw [partialDerivSl2c_sub (fun p => partialDerivSl2c σ (A ν) p) (fun p => partialDerivSl2c ν (A σ) p) ρ x (hd_dA σ ν) (hd_dA ν σ)]
  rw [partialDerivSl2c_sub (fun p => partialDerivSl2c ν (A ρ) p) (fun p => partialDerivSl2c ρ (A ν) p) σ x (hd_dA ν ρ) (hd_dA ρ ν)]
  rw [partialDerivSl2c_sub (fun p => partialDerivSl2c ρ (A σ) p) (fun p => partialDerivSl2c σ (A ρ) p) ν x (hd_dA ρ σ) (hd_dA σ ρ)]

  rw [partialDerivSl2c_bracket (A σ) (A ν) ρ x (hdA σ) (hdA ν)]
  rw [partialDerivSl2c_bracket (A ν) (A ρ) σ x (hdA ν) (hdA ρ)]
  rw [partialDerivSl2c_bracket (A ρ) (A σ) ν x (hdA ρ) (hdA σ)]
  
  have h_comm1 : partialDerivSl2c ρ (fun p => partialDerivSl2c σ (A ν) p) x = partialDerivSl2c σ (fun p => partialDerivSl2c ρ (A ν) p) x := partialDerivSl2c_commutes A ν ρ σ x (h_smooth ν)
  have h_comm2 : partialDerivSl2c ρ (fun p => partialDerivSl2c ν (A σ) p) x = partialDerivSl2c ν (fun p => partialDerivSl2c ρ (A σ) p) x := partialDerivSl2c_commutes A σ ρ ν x (h_smooth σ)
  have h_comm3 : partialDerivSl2c σ (fun p => partialDerivSl2c ν (A ρ) p) x = partialDerivSl2c ν (fun p => partialDerivSl2c σ (A ρ) p) x := partialDerivSl2c_commutes A ρ σ ν x (h_smooth ρ)
  
  have h_anti1 : ⁅partialDerivSl2c ρ (A σ) x, A ν x⁆ = - ⁅A ν x, partialDerivSl2c ρ (A σ) x⁆ := bracket_anti _ _
  have h_anti2 : ⁅partialDerivSl2c σ (A ν) x, A ρ x⁆ = - ⁅A ρ x, partialDerivSl2c σ (A ν) x⁆ := bracket_anti _ _
  have h_anti3 : ⁅partialDerivSl2c ν (A ρ) x, A σ x⁆ = - ⁅A σ x, partialDerivSl2c ν (A ρ) x⁆ := bracket_anti _ _
  
  rw [h_comm1, h_comm2, h_comm3, h_anti1, h_anti2, h_anti3]
  
  simp only [bracket_add, bracket_sub]

  have jacobi : ⁅A ρ x, ⁅A σ x, A ν x⁆⁆ + ⁅A σ x, ⁅A ν x, A ρ x⁆⁆ + ⁅A ν x, ⁅A ρ x, A σ x⁆⁆ = 0 := bracket_jacobi (A ρ x) (A σ x) (A ν x)
  rw [← jacobi]
  abel

end CGD.Foundations

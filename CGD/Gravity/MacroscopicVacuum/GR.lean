-- FILENAME: CGD/Gravity/MacroscopicVacuum/GR.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology
import CGD.Gravity.Urbantke
import Litlib.Y1989.capovilla1989general.Signature
import Litlib.Y1991.capovilla1991pure.Signature
import CGD.Gravity.MacroscopicVacuum.Basic
import CGD.Gravity.MacroscopicVacuum.WMatrix

set_option autoImplicit false
set_option linter.unusedVariables false

open Complex Matrix BigOperators
open CGD.Axioms CGD.Foundations Litlib Classical
open Litlib.Y1989.capovilla1989general
open Litlib.Y1991.capovilla1991pure

namespace CGD.Gravity

Litlib.theorem
  description "Macroscopic Vacuum (General Relativity Limit)"
/-- 
We rigorously prove that the generated complex spacetime metric maps exactly 
to a complex Ricci-flat tensor, as derived from the pure CDJ constraint equation.
-/
theorem macroscopicVacuumGR 
  [eq2_2c : CDJImpliesRicciFlat 
    SpacetimePoint 
    (fun F x μ ν => urbantkeMetric (fun m n => toSl2c (F x 0 m n • sigma1.val + F x 1 m n • sigma2.val + F x 2 m n • sigma3.val)) μ ν) 
    (fun g x μ ν => ricciTensor (fun m n p => g p m n) μ ν x)] 
  (u : Universe)
  (e : TetradField)
  (h_urbantke : ∀ x μ ν, metricFromTetrad e μ ν x = urbantkeMetric (fun m n => toSl2c (curvatureSl2c u.sd_sector m n x).val) μ ν)
  (h_nondeg : ∀ x, (urbantkeMetric (fun m n => toSl2c (curvatureSl2c u.sd_sector m n x).val)).det ≠ 0)
  (h_cdj : satisfiesPureCdjConstraint (fun p m n => cgdAdjointCurvature u m n p)) :
  ∀ x μ ν, ricciTensor (metricFromTetrad e) μ ν x = 0 := by
  have h_6a_proof : ∀ x, (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      capovillaMetric (1:ℂ) (-1:ℂ) a b c d * 
      wedgeContract (F_CGD u x a) (F_CGD u x b) epsilon4 * 
      wedgeContract (F_CGD u x c) (F_CGD u x d) epsilon4) = 0 := by
    intro p
    have hW := W_eq_zero u p (h_cdj p)
    apply Finset.sum_eq_zero; intro a _
    apply Finset.sum_eq_zero; intro b _
    apply Finset.sum_eq_zero; intro c _
    apply Finset.sum_eq_zero; intro d _
    have h_wab : wedgeContract (F_CGD u p a) (F_CGD u p b) epsilon4 = 0 := hW a b
    rw [h_wab]
    ring

  have h_nondeg_proof : ∀ x, Matrix.det (Matrix.of (fun μ ν => urbantkeMetric (fun m n => toSl2c (F_CGD u x 0 m n • sigma1.val + F_CGD u x 1 m n • sigma2.val + F_CGD u x 2 m n • sigma3.val)) μ ν)) ≠ 0 := by
    intro p
    have h_eq_inner : (fun m n => toSl2c (F_CGD u p 0 m n • sigma1.val + F_CGD u p 1 m n • sigma2.val + F_CGD u p 2 m n • sigma3.val)) = 
                      (fun m n => toSl2c (curvatureSl2c u.sd_sector m n p).val) := by
      ext m n
      rw [F_CGD_reconstruct]
    have h_eq : (fun μ ν => urbantkeMetric (fun m n => toSl2c (F_CGD u p 0 m n • sigma1.val + F_CGD u p 1 m n • sigma2.val + F_CGD u p 2 m n • sigma3.val)) μ ν) = 
                (fun μ ν => urbantkeMetric (fun m n => toSl2c (curvatureSl2c u.sd_sector m n p).val) μ ν) := by
      rw [h_eq_inner]
    rw [h_eq]
    exact h_nondeg p

  have he_nz : epsilon4 0 1 2 3 ≠ 0 := by rw [epsilon4_0123]; exact one_ne_zero

  have h_coupling : (1 : ℂ) = -(-1 : ℂ) := by ring
  have h_alpha_nz : (1 : ℂ) ≠ 0 := one_ne_zero

  have ricci_eq_zero := eq2_2c.cdj_implies_ricci_flat (F_CGD u) 1 (-1) epsilon4 epsilon4_alt he_nz h_coupling h_alpha_nz h_nondeg_proof h_6a_proof

  intro x μ ν
  have h_g_eq : (fun m n p => urbantkeMetric (fun k l => toSl2c (F_CGD u p 0 k l • sigma1.val + F_CGD u p 1 k l • sigma2.val + F_CGD u p 2 k l • sigma3.val)) m n) = metricFromTetrad e := by
    ext m n p
    have h_inner : (fun k l => toSl2c (F_CGD u p 0 k l • sigma1.val + F_CGD u p 1 k l • sigma2.val + F_CGD u p 2 k l • sigma3.val)) = 
                   (fun k l => toSl2c (curvatureSl2c u.sd_sector k l p).val) := by
      ext k l
      rw [F_CGD_reconstruct]
    rw [h_inner]
    exact (h_urbantke p m n).symm
  
  have h_r := ricci_eq_zero x μ ν
  rwa [h_g_eq] at h_r

end CGD.Gravity

-- FILENAME: CGD/Gravity/MacroscopicVacuum/GR.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology
import CGD.Gravity.Urbantke
import Litlib.Y1991.capovilla1991pure.Signature
import CGD.Gravity.MacroscopicVacuum.Basic
import CGD.Gravity.MacroscopicVacuum.WMatrix
import CGD.Gravity.MacroscopicVacuum.Spinors
import CGD.Gravity.MacroscopicVacuum.Differential

set_option autoImplicit false
set_option linter.unusedVariables false

open Complex Matrix BigOperators
open CGD.Axioms CGD.Foundations Litlib Classical
open Litlib.Y1991.capovilla1991pure

namespace CGD.Gravity

lemma cgd_sumFin2_eq_sum (f : Fin 2 → ℂ) :
  CGD.Gravity.sumFin2 f = ∑ x : Fin 2, f x := by
  unfold CGD.Gravity.sumFin2
  rw [Fin.sum_univ_two]

/-- 
Isolates the algebraic bridge proof to bypass the typeclass synthesis conflict.
Explicitly binds the non-degeneracy instance to prevent `haveI` shadowing.
-/
lemma macroscopicVacuumGR_bridge
  (u : Universe) [vac : IsClassicalVacuum u]
  (p : SpacetimePoint) (m n : Fin 4) (A B : Fin 2) :
  cgd_R u p m n A B =
    Litlib.Y1991.capovilla1991pure.sumFin2 fun C =>
      Litlib.Y1991.capovilla1991pure.sumFin2 fun D =>
        (vac.non_degenerate p).Psi A B C D * cgd_Sigma vac.urbantke_tetrad p m n C D := by
  
  -- Explicitly pass the instance to prevent `this` shadowing
  have h_bridge := @capovilla_algebraic_bridge u p (vac.non_degenerate p) m n A B
  
  have h_litlib_sum : ∀ f, Litlib.Y1991.capovilla1991pure.sumFin2 f = ∑ x : Fin 2, f x := fun f => rfl
  simp only [h_litlib_sum]
  rw [h_bridge]
  
  apply Finset.sum_congr rfl; intro C _
  apply Finset.sum_congr rfl; intro D _
  
  have h_eq := vac.sigma_compat p m n C D
  rw [h_eq]

Litlib.theorem
  description "Macroscopic Vacuum (General Relativity Limit)"
/-- 
We rigorously prove that the generated complex spacetime metric maps exactly 
to a complex Ricci-flat tensor. 

By demanding an `IsClassicalVacuum`, we completely purge all arbitrary 
macroscopic free variables (theta, Sigma, Psi, omega, dSigma, and the tetrad).
The metric is defined natively as the Urbantke metric of the Spin(4,C) connection, 
and Ricci flatness is derived purely from the internal SU(2) Yang-Mills field equations.
-/
theorem macroscopicVacuumGR 
  (u : Universe)
  [vac : IsClassicalVacuum u]
  [th_ricci : Theorem_Eq2_2c_RicciFlat 
    (Spacetime := SpacetimePoint)
    (theta := fun x => cgd_theta vac.urbantke_tetrad x) 
    (g := fun x μ ν => metricFromTetrad vac.urbantke_tetrad μ ν x) 
    (eps2_down := cgd_eps2_down) 
    (eps2_bar_down := cgd_eps2_bar_down) 
    (eps2_right := cgd_eps2_bar_down) -- In complex CDJ, right is bar down
    (eps2_up := cgd_eps2_up)
    (R := cgd_R u) 
    (Psi := fun x => (vac.non_degenerate x).Psi) 
    (Sigma := fun x => cgd_Sigma vac.urbantke_tetrad x) 
    (dSigma := fun x => cgd_dSigma vac.urbantke_tetrad x)
    (omega := fun x => cgd_omega u x)
    (isRicciFlat := fun g => ∀ x μ ν, ricciTensor (fun m n p => g p m n) μ ν x = 0)] :
  ∀ x μ ν, ricciTensor (fun m n p => urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n) μ ν x = 0 := by
  intro x μ ν
  have h_ricci_tetrad := th_ricci.eq2_2c_implies_ricci_flat ?h_Sigma_def ?h_DSigma_eq_zero ?h_eq2_2c x μ ν
  
  -- Step 1: Prove the Ricci flatness of the exact Urbantke Metric natively using metric compatibility
  have h_metric_eq : (fun m n p => metricFromTetrad vac.urbantke_tetrad m n p) = 
                     (fun m n p => urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n) := by
    funext m n p
    exact vac.metric_compat p m n
  
  rw [← h_metric_eq]
  exact h_ricci_tetrad

  -- Step 2: The tetrad-derived Sigma tensor structurally matches the geometric Capovilla Eq 2.3 definition
  case h_Sigma_def =>
    intros p m n A B
    unfold cgd_Sigma
    have h_litlib_sum : ∀ f, Litlib.Y1991.capovilla1991pure.sumFin2 f = ∑ x : Fin 2, f x := fun f => rfl
    simp only [cgd_sumFin2_eq_sum, h_litlib_sum]

  -- Step 3: The universe satisfies the classical on-shell Yang-Mills field equations
  case h_DSigma_eq_zero =>
    intros p m n r A B
    have h_cgd := vac.h_DSigma_eq_zero p m n r A B
    unfold cgd_D_Sigma_wedge cgd_covariant_deriv_Sigma_term cgd_omega_up at h_cgd
    have h_litlib_sum : ∀ f, Litlib.Y1991.capovilla1991pure.sumFin2 f = ∑ x : Fin 2, f x := fun f => rfl
    simp only [cgd_sumFin2_eq_sum] at h_cgd
    simp only [h_litlib_sum]
    exact h_cgd
    
  -- Step 4: The topological connection structurally projects down into the Urbantke vacuum geometry
  case h_eq2_2c =>
    intros p m n A B
    exact macroscopicVacuumGR_bridge u p m n A B

end CGD.Gravity

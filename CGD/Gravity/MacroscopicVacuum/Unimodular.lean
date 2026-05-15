-- FILENAME: CGD/Gravity/MacroscopicVacuum/Unimodular.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology
import CGD.Gravity.Urbantke
import Litlib.Y1991.capovilla1991pure.Signature
import Litlib.Y2024.gielen2024unimodular.Signature
import CGD.Gravity.MacroscopicVacuum.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

open Complex Matrix BigOperators
open CGD.Axioms CGD.Foundations Litlib Classical
open Litlib.Y1991.capovilla1991pure
open Litlib.Y2024.gielen2024unimodular

namespace CGD.Gravity

Litlib.theorem
  description "Unimodular Macroscopic Spacetime Volume Emergence"
/-- 
By mapping the continuous Spin(4,C) connections into the 3x3 Adjoint su(2) representation, 
we show that the Unimodular CDJ theorem extracts a strict global volume invariant `c` from the topological CDJ condition.
-/
theorem kinematicUnimodularVacuum 
  [udi : Litlib.Y1991.capovilla1991pure.UrbantkeDeterminantIdentity Unit CGD.Gravity.epsilon4 CGD.Gravity.eps2 CGD.Gravity.eps2_up]
  (bulkVacuum : Set SpacetimePoint)
  (u : Universe)
  (Λ : ℂ)
  (hLambdaNz : Λ ≠ 0)
  (h_cdj : ∀ x ∈ bulkVacuum, (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = Λ • 1) :
  ∀ x y : bulkVacuum, (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det = (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n y.val)).det ∧ 
         (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det ≠ 0 := by
  intro x y
  obtain ⟨det_val, h_det⟩ := urbantke_det_uniqueness Λ
  have hx : (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det = det_val :=
    h_det (fun m n => cgdAdjointCurvature u m n x.val) 
      (adjoint_curvature_antisymm u x.val)
      (adjoint_curvature_su2 u x.val)
      (h_cdj x.val x.property)
  have hy : (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n y.val)).det = det_val :=
    h_det (fun m n => cgdAdjointCurvature u m n y.val) 
      (adjoint_curvature_antisymm u y.val)
      (adjoint_curvature_su2 u y.val)
      (h_cdj y.val y.property)
  have hnz : (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det ≠ 0 :=
    urbantke_nondeg_of_plebanski Λ (fun m n => cgdAdjointCurvature u m n x.val) hLambdaNz 
      (adjoint_curvature_antisymm u x.val)
      (adjoint_curvature_su2 u x.val)
      (h_cdj x.val x.property)
  exact ⟨hx.trans hy.symm, hnz⟩

end CGD.Gravity

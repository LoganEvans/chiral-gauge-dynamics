-- FILENAME: CGD/Gravity/MacroscopicVacuum.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology
import Litlib.Y1991.capovilla1991pure.Signature
import Litlib.Y2024.gielen2024unimodular.Signature

set_option autoImplicit false
set_option linter.unusedVariables false

open Complex Matrix BigOperators
open CGD.Axioms CGD.Foundations Litlib
open Litlib.Y1991.capovilla1991pure
open Litlib.Y2024.gielen2024unimodular

namespace CGD.Gravity

noncomputable def metricFromTetrad (e : TetradField) : SpacetimeIndex → SpacetimeIndex → SpacetimePoint → ℂ :=
  fun μ ν x => ∑ I : InternalIndex, e I μ x * e I ν x

noncomputable def cgdUnimodularMetricAdapter (F_adj : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  urbantkeMetric (fun μ ν => 
    toSl2c (F_adj μ ν 1 2 • sigma1.val + F_adj μ ν 2 0 • sigma2.val + F_adj μ ν 0 1 • sigma3.val))

def satisfiesPureCdjConstraint (F : SpacetimePoint → Fin 4 → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ x : SpacetimePoint,
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      epsilon4 μ ν ρ σ * Matrix.trace (F x μ ν * F x ρ σ)) = 0

-- ==========================================
-- THEOREMS
-- ==========================================

Litlib.theorem
  description "Macroscopic Complex Ricci-Flat GR Vacuum"
/-- 
We rigorously prove that the generated complex spacetime metric maps exactly 
to a complex Ricci-flat tensor, as derived from the pure CDJ constraint equation.
-/
theorem macroscopicVacuumGR 
  [eq2_2c : Eq2_2c 
    SpacetimePoint 
    (fun μ f x => partialDeriv μ f x)
    (fun F μ ν x => urbantkeMetric (fun m n => toSl2c (F x m n)) μ ν) 
    (fun g μ ν x => matrixInv4x4 (fun m n => g m n x) μ ν)
    christoffel
    ricciTensor] 
  (u : Universe)
  (e : TetradField)
  (h_urbantke : ∀ x μ ν, metricFromTetrad e μ ν x = urbantkeMetric (fun m n => toSl2c (curvatureSl2c u.sd_sector m n x).val) μ ν)
  (h_nondeg : ∀ x, (urbantkeMetric (fun m n => toSl2c (curvatureSl2c u.sd_sector m n x).val)).det ≠ 0)
  (h_cdj : satisfiesPureCdjConstraint (fun p m n => (curvatureSl2c u.sd_sector m n p).val)) :
  ∀ x μ ν, ricciTensor (metricFromTetrad e) μ ν x = 0 := by
  intro x μ ν
  have h_eq : metricFromTetrad e = fun a b p => urbantkeMetric (fun m n => toSl2c (curvatureSl2c u.sd_sector m n p).val) a b := by
    funext a b p
    exact h_urbantke p a b
  rw [h_eq]
  have hEpsilonAlt : ∀ α β γ δ, epsilon4 α β γ δ = -epsilon4 β α γ δ ∧ epsilon4 α β γ δ = -epsilon4 α γ β δ ∧ epsilon4 α β γ δ = -epsilon4 α β δ γ := CGD.Gravity.epsilon4_alt
  have hEpsilonNondeg : epsilon4 0 1 2 3 ≠ 0 := by
    rw [CGD.Gravity.epsilon4_0123]
    exact one_ne_zero
  exact eq2_2c.urbantkeIsRicciFlat (fun p m n => (curvatureSl2c u.sd_sector m n p).val) epsilon4 hEpsilonAlt hEpsilonNondeg h_nondeg h_cdj x μ ν

Litlib.theorem
  description "Unimodular Vacuum Form"
/-- 
By mapping the continuous Spin(4,C) connections into the 3x3 Adjoint su(2) representation, 
we show that the Unimodular CDJ theorem extracts a strict global volume invariant `c` from the topological CDJ condition.
-/
theorem kinematicUnimodularVacuum 
  [ucdj_vol : Eq12 SpacetimePoint cgdUnimodularMetricAdapter] 
  (F_adj : Fin 4 → Fin 4 → SpacetimePoint → Matrix (Fin 3) (Fin 3) ℂ)
  (Λ : ℂ)
  (h_anti : ∀ μ ν x, F_adj μ ν x = - F_adj ν μ x)
  (hLambdaNz : Λ ≠ 0)
  (h_cdj : ∀ x, (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * Matrix.trace (F_adj μ ν x * F_adj ρ σ x)) = Λ) :
  ∀ x y, (cgdUnimodularMetricAdapter (fun m n => F_adj m n x)).det = (cgdUnimodularMetricAdapter (fun m n => F_adj m n y)).det ∧ 
         (cgdUnimodularMetricAdapter (fun m n => F_adj m n x)).det ≠ 0 := by
  intro x y
  have hEpsilonAlt : ∀ α β γ δ, epsilon4 α β γ δ = -epsilon4 β α γ δ ∧ epsilon4 α β γ δ = -epsilon4 α γ β δ ∧ epsilon4 α β γ δ = -epsilon4 α β δ γ := CGD.Gravity.epsilon4_alt
  have hEpsilonNondeg : epsilon4 0 1 2 3 ≠ 0 := by
    rw [CGD.Gravity.epsilon4_0123]
    exact one_ne_zero
  have h_vol := ucdj_vol.cdjImpliesConstantVolume F_adj epsilon4 Λ hEpsilonAlt hEpsilonNondeg hLambdaNz h_cdj
  rcases h_vol with ⟨c, hc_neq, hc_eq⟩
  constructor
  · rw [hc_eq x, hc_eq y]
  · rw [hc_eq x]
    exact hc_neq

end CGD.Gravity

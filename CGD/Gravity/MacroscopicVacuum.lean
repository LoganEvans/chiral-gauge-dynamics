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

noncomputable def cgdAdjointConnection (u : Universe) (μ : Fin 4) (x : SpacetimePoint) : Matrix (Fin 3) (Fin 3) ℂ :=
  extractAdjoint (u.sd_sector μ x).val

noncomputable def cgdAdjointCurvature (u : Universe) (μ ν : Fin 4) (x : SpacetimePoint) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => 
    partialDeriv μ (fun p => cgdAdjointConnection u ν p i j) x -
    partialDeriv ν (fun p => cgdAdjointConnection u μ p i j) x +
    (cgdAdjointConnection u μ x * cgdAdjointConnection u ν x - cgdAdjointConnection u ν x * cgdAdjointConnection u μ x) i j

def satisfiesPureCdjConstraint (F_adj : SpacetimePoint → Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  ∀ x : SpacetimePoint,
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      epsilon4 μ ν ρ σ • (F_adj x μ ν * F_adj x ρ σ)) = 0

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
  (h_cdj : satisfiesPureCdjConstraint (fun p m n => cgdAdjointCurvature u m n p)) :
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
    
  have hd_A : ∀ α (p : SpacetimePoint) i j, DifferentiableAt ℝ (fun p' => (u.sd_sector α p').val i j) p := by
    intro α p i j
    exact ((u.sd_sector.is_smooth α i j).differentiable (by decide)) p
    
  have h_F_def : ∀ p μ ν i j, (curvatureSl2c u.sd_sector μ ν p).val i j = 
    partialDeriv μ (fun p' => (u.sd_sector ν p').val i j) p - 
    partialDeriv ν (fun p' => (u.sd_sector μ p').val i j) p + 
    ((u.sd_sector μ p).val * (u.sd_sector ν p).val - (u.sd_sector ν p).val * (u.sd_sector μ p).val) i j := by
    intro p μ ν i j
    exact curvatureSl2c_val_eq u.sd_sector μ ν p (hd_A μ p) (hd_A ν p) i j
    
  exact eq2_2c.urbantkeIsRicciFlat (fun p μ => (u.sd_sector μ p).val) (fun p m n => (curvatureSl2c u.sd_sector m n p).val) (fun p m n => cgdAdjointCurvature u m n p) epsilon4 hEpsilonAlt hEpsilonNondeg h_F_def h_nondeg h_cdj x μ ν

Litlib.theorem
  description "Unimodular Vacuum Form"
/-- 
By mapping the continuous Spin(4,C) connections into the 3x3 Adjoint su(2) representation, 
we show that the Unimodular CDJ theorem extracts a strict global volume invariant `c` from the topological CDJ condition.
-/
theorem kinematicUnimodularVacuum 
  [ucdj_vol : Eq12 SpacetimePoint (fun μ f x => partialDeriv μ f x) cgdUnimodularMetricAdapter] 
  (u : Universe)
  (Λ : ℂ)
  (hLambdaNz : Λ ≠ 0)
  (h_cdj : ∀ x, (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * Matrix.trace (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = Λ) :
  ∀ x y, (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x)).det = (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n y)).det ∧ 
         (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x)).det ≠ 0 := by
  intro x y
  have hEpsilonAlt : ∀ α β γ δ, epsilon4 α β γ δ = -epsilon4 β α γ δ ∧ epsilon4 α β γ δ = -epsilon4 α γ β δ ∧ epsilon4 α β γ δ = -epsilon4 α β δ γ := CGD.Gravity.epsilon4_alt
  have hEpsilonNondeg : epsilon4 0 1 2 3 ≠ 0 := by
    rw [CGD.Gravity.epsilon4_0123]
    exact one_ne_zero

  let A_adj := fun μ p => cgdAdjointConnection u μ p
  let F_adj := fun μ ν p => cgdAdjointCurvature u μ ν p

  have h_anti : ∀ μ ν p, F_adj μ ν p = - F_adj ν μ p := by
    intro μ ν p
    ext i j
    unfold F_adj cgdAdjointCurvature
    simp only [Matrix.neg_apply, Matrix.sub_apply]
    ring

  have h_F_def : ∀ μ ν p i j, F_adj μ ν p i j = 
    partialDeriv μ (fun p' => A_adj ν p' i j) p - 
    partialDeriv ν (fun p' => A_adj μ p' i j) p + 
    (A_adj μ p * A_adj ν p - A_adj ν p * A_adj μ p) i j := by
    intro μ ν p i j
    rfl

  have h_vol := ucdj_vol.cdjImpliesConstantVolume A_adj F_adj epsilon4 Λ hEpsilonAlt hEpsilonNondeg h_F_def hLambdaNz h_cdj
  rcases h_vol with ⟨c, hc_neq, hc_eq⟩
  constructor
  · rw [hc_eq x, hc_eq y]
  · rw [hc_eq x]
    exact hc_neq

end CGD.Gravity

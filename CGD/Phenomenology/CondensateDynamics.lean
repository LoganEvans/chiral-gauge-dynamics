-- FILENAME: CGD/Phenomenology/CondensateDynamics.lean

import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse
import CGD.Gravity.Geometry
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Litlib.Core

open CGD.Foundations CGD.Math CGD.Gravity CGD.Axioms Matrix Complex

namespace CGD.Phenomenology

/--
Identifies a "Uniform Crosswind" - a gauge field that is polarized into a constant, 
single-color background state. It has no dynamic fluctuations (zero derivatives) 
and no non-Abelian internal structure (all components commute).
-/
def isUniformCrosswind (A : Fin 4 → SpacetimePoint → SL2C) : Prop :=
  (∀ mu nu x, partialDerivSl2c nu (A mu) x = 0) ∧
  (∀ mu nu x, ⁅A mu x, A nu x⁆ = 0)

lemma crosswind_curvature_zero (A : Fin 4 → SpacetimePoint → SL2C) (h_wind : isUniformCrosswind A) :
  ∀ mu nu x, curvatureSl2c A mu nu x = 0 := by
  intros mu nu x
  unfold curvatureSl2c
  rcases h_wind with ⟨h_deriv, h_comm⟩
  have h1 : partialDerivSl2c mu (A nu) x = 0 := h_deriv nu mu x
  have h2 : partialDerivSl2c nu (A mu) x = 0 := h_deriv mu nu x
  have h3 : ⁅A mu x, A nu x⁆ = 0 := h_comm mu nu x
  rw [h1, h2, h3]
  change (0 : SL2C) - 0 + 0 = 0
  simp

lemma zero_curvature_metric_zero :
  urbantkeMetric (fun _ _ => (0 : SL2C)) = 0 := by
  ext mu nu
  unfold urbantkeMetric project
  simp only [Matrix.zero_apply]
  
  apply Finset.sum_eq_zero; intro a _
  apply Finset.sum_eq_zero; intro b _
  apply Finset.sum_eq_zero; intro c _
  
  -- Evaluate the inner space_term to exactly zero
  have h_inner_zero : (∑ alpha : Fin 4, ∑ beta : Fin 4, ∑ gamma : Fin 4, ∑ delta : Fin 4,
    epsilon4 alpha beta gamma delta * 
    (0.5 * Matrix.trace ((0 : SL2C).val * (getPauli a).val)) * 
    (0.5 * Matrix.trace ((0 : SL2C).val * (getPauli b).val)) * 
    (0.5 * Matrix.trace ((0 : SL2C).val * (getPauli c).val))) = 0 := by
    
    apply Finset.sum_eq_zero; intro alpha _
    apply Finset.sum_eq_zero; intro beta _
    apply Finset.sum_eq_zero; intro gamma _
    apply Finset.sum_eq_zero; intro delta _
    
    have h_proj : 0.5 * Matrix.trace ((0 : SL2C).val * (getPauli a).val) = 0 := by
      have h_zero : (0 : SL2C).val = 0 := rfl
      rw [h_zero, Matrix.zero_mul]
      have h_tr : Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by simp [Matrix.trace]
      rw [h_tr, mul_zero]
      
    rw [h_proj]
    ring
    
  rw [h_inner_zero]
  ring

/--
To preserve macroscopic Lorentz invariance, the spacetime vacuum condensate must not exist 
as a polarized, static vector field (a 'crosswind'), which would establish a preferred frame. 

This formally proves that if the condensate loses its dynamic gradients and its non-Abelian 
color intersections, the curvature evaluates to zero, which algebraically forces the macroscopic 
metric determinant to zero. 

Because Axiom II (Macroscopic Volume) strictly forbids det(g) = 0 in the bulk, the geometry natively 
forbids Lorentz-violating crosswinds. The vacuum condensate is topologically constrained to exist strictly 
as an Isotropic Stochastic Condensate—a violent, unpolarized, non-Abelian topological fluctuation whose 
macroscopic expectation value preserves Lorentz symmetry while maintaining a non-zero spacetime volume.
-/
@[litlib_track "Kinematic Crosswind Degeneracy"]
theorem kinematicCrosswindDegeneracy (pu : PhysicalUniverse)
  (h_wind : isUniformCrosswind pu.toUniverse.sd_sector) :
  ∀ x, (urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.sd_sector m n x)).det = 0 := by
  intro x
  have h_curv : ∀ mu nu, curvatureSl2c pu.toUniverse.sd_sector mu nu x = 0 := by
    intros mu nu
    exact crosswind_curvature_zero pu.toUniverse.sd_sector h_wind mu nu x
  
  have h_F_eq : (fun m n => curvatureSl2c pu.toUniverse.sd_sector m n x) = (fun _ _ => (0 : SL2C)) := by
    funext m n; exact h_curv m n
    
  rw [h_F_eq]
  have h_metric := zero_curvature_metric_zero
  rw [h_metric]
  
  -- A zero matrix has a zero determinant if it has at least one row
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  rfl

end CGD.Phenomenology

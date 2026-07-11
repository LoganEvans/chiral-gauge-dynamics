-- FILENAME: CGD/Cosmology/BigBang.lean

import Litlib.Core
import CGD.Cosmology.Definitions
import CGD.Cosmology.TimeEmergence
import CGD.Gravity.Geometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse

set_option linter.unusedSimpArgs false

open CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms CGD.Foundations CGD.Math

namespace CGD.Cosmology

/--
A kinematic boundary evaluation. This demonstrates that if a phase region is 
artificially constrained to a fully 4D symmetric SO(4) state, the resulting 
Urbantke metric takes a purely Euclidean form (c • 1).

Rather than representing a dynamic cosmological evolution, this acts as a 
mathematical sanity check: it shows that highly symmetric ground-state toy models 
evaluate to non-singular Euclidean spaces rather than generating mathematical 
singularities in the metric.
-/
@[litlib_track "Big Bang Singularity Resolution (Euclidean Bounce)"]
theorem kinematicBigBang (pu : PhysicalUniverse) (phaseRegion : Set SpacetimePoint)
  (h_subset : phaseRegion ⊆ pu.bulk)
  (h_symm : ∀ x ∈ phaseRegion, isFully4DSymmetric (fun mu nu => curvatureSl2c pu.toUniverse.sd_sector mu nu x)) :
  ∀ x ∈ phaseRegion, ∃ c : Complex, c ≠ 0 ∧ urbantkeMetric (fun mu nu => curvatureSl2c pu.toUniverse.sd_sector mu nu x) = c • 1 := by
  intro x hx
  have h_tic := h_symm x hx
  have h_g := urbantke_eq_smul_id_of_self_dual (fun mu nu => curvatureSl2c pu.toUniverse.sd_sector mu nu x) h_tic
  rcases h_g with ⟨c, hc⟩
  use c
  constructor
  · intro hc_zero
    rw [hc_zero, zero_smul] at hc
    have h_nd := pu.has_volume.volume_exists x (h_subset hx)
    rw [hc] at h_nd
    have h_det_zero : (0 : Matrix (Fin 4) (Fin 4) Complex).det = 0 := by
      rw [Matrix.det_apply]
      apply Finset.sum_eq_zero
      intro σ _
      have h_prod : (∏ i : Fin 4, (0 : Matrix (Fin 4) (Fin 4) Complex) (σ i) i) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4))
        rfl
      rw [h_prod, smul_zero]
    exact h_nd h_det_zero
  · exact hc

lemma math_Static_Electric_Zero_term (F : Fin 4 → Fin 4 → SL2C)
  (h_static : ∀ j : Fin 4, F 0 j = 0)
  (a b c : Fin 3) (j α β γ δ : Fin 4) :
  epsilon4 α β γ δ * project F a 0 α * project F b j β * project F c γ δ = 0 := by
  have hF : F 0 α = 0 := h_static α
  have hProj : project F a 0 α = 0 := by
    unfold project
    rw[hF]
    change 0.5 * Matrix.trace ((0 : Matrix (Fin 2) (Fin 2) Complex) * (getPauli a).val) = 0
    rw[Matrix.zero_mul, Matrix.trace_zero, mul_zero]
  rw [hProj]
  ring

lemma math_Static_Electric_inner_sum_zero (F : Fin 4 → Fin 4 → SL2C)
  (h_static : ∀ j : Fin 4, F 0 j = 0)
  (a b c : Fin 3) (j : Fin 4) :
  (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
    epsilon4 α β γ δ * project F a 0 α * project F b j β * project F c γ δ) = 0 := by
  apply Finset.sum_eq_zero; intro α _
  apply Finset.sum_eq_zero; intro β _
  apply Finset.sum_eq_zero; intro γ _
  apply Finset.sum_eq_zero; intro δ _
  exact math_Static_Electric_Zero_term F h_static a b c j α β γ δ

lemma math_Static_Electric_Zero (F : Fin 4 → Fin 4 → SL2C)
  (h_static : ∀ j : Fin 4, F 0 j = 0) :
  ∀ j : Fin 4, (urbantkeMetric F) 0 j = 0 := by
  intro j
  unfold urbantkeMetric
  apply Finset.sum_eq_zero; intro a _
  apply Finset.sum_eq_zero; intro b _
  apply Finset.sum_eq_zero; intro c _
  have h_inner := math_Static_Electric_inner_sum_zero F h_static a b c j
  rw [h_inner]
  ring

lemma det_zero_of_row_zero (M : Matrix (Fin 4) (Fin 4) Complex)
  (h_row : ∀ j : Fin 4, M 0 j = 0) : M.det = 0 := by
  rw[Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have hk : σ (σ.symm 0) = 0 := Equiv.apply_symm_apply σ 0
  have hMk : M (σ (σ.symm 0)) (σ.symm 0) = 0 := by
    rw [hk]
    exact h_row (σ.symm 0)
  have h_prod : (∏ i : Fin 4, M (σ i) i) = 0 := Finset.prod_eq_zero (Finset.mem_univ (σ.symm 0)) hMk
  rw [h_prod]
  exact smul_zero _

/--
In pure connection gravity, 4D spacetime volume geometrically requires time-evolution. A completely static universe (where electric/temporal components of the field strength are zero) cannot sustain a macroscopic 4D metric and topologically collapses, forcing the metric determinant to zero.
-/
@[litlib_track "Static Universe Degeneracy"]
theorem kinematicStaticUniverseDegeneracy (pu : PhysicalUniverse) :
  isStaticUniverse pu.toUniverse →
  ∀ x, (urbantkeMetric (fun mu nu => curvatureSl2c pu.toUniverse.sd_sector mu nu x)).det = 0 := by
  intro h x
  have h_static : ∀ j : Fin 4, curvatureSl2c pu.toUniverse.sd_sector 0 j x = 0 := h x
  have h_metric_zero_row := math_Static_Electric_Zero (fun mu nu => curvatureSl2c pu.toUniverse.sd_sector mu nu x) h_static
  exact det_zero_of_row_zero _ h_metric_zero_row

end CGD.Cosmology

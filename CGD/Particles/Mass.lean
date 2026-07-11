-- FILENAME: CGD/Particles/Mass.lean

import CGD.Math.SU2
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Axioms.PhysicalUniverse

open CGD.Math CGD.Foundations CGD.Axioms Complex Matrix

namespace CGD.Particles

noncomputable def inertialMass (pu : PhysicalUniverse) (x : SpacetimePoint) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, - (Matrix.trace ((curvatureSl2c pu.toUniverse.asd_sector.val μ ν x).val *
                                             (curvatureSl2c pu.toUniverse.asd_sector.val μ ν x).val)).re

/-- Phase 3: Prove that because partial derivatives commute and the Lie bracket of SU(2) remains in SU(2), the curvature tensor natively belongs to the SU(2) Lie algebra. -/
lemma curvature_is_su2 (pu : PhysicalUniverse) (x : SpacetimePoint) (μ ν : Fin 4)
  (h_su2 : ∀ μ p, isSu2 (pu.toUniverse.asd_sector.val μ p).val) :
  isSu2 (curvatureSl2c pu.toUniverse.asd_sector.val μ ν x).val := by
  let A := pu.toUniverse.asd_sector.val

  have hAμ : ∀ i j, DifferentiableAt ℝ (fun p => (A μ p).val i j) x := by
    intro i j
    exact (pu.toUniverse.asd_sector.is_smooth μ i j).differentiable (by decide) x

  have hAν : ∀ i j, DifferentiableAt ℝ (fun p => (A ν p).val i j) x := by
    intro i j
    exact (pu.toUniverse.asd_sector.is_smooth ν i j).differentiable (by decide) x

  unfold isSu2
  constructor
  · -- Trace is 0
    exact (curvatureSl2c A μ ν x).property
  · -- Adjoint is -F
    ext i j
    let F := (curvatureSl2c A μ ν x).val
    have h_lhs : F.conjTranspose i j = star (F j i) := rfl
    have h_rhs : (- F) i j = - F i j := rfl
    rw [h_lhs, h_rhs]

    have h_F_ji : F j i = partialDeriv μ (fun p => (A ν p).val j i) x - partialDeriv ν (fun p => (A μ p).val j i) x + ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) j i := by
      exact curvatureSl2c_val_eq A μ ν x hAμ hAν j i

    have h_F_ij : F i j = partialDeriv μ (fun p => (A ν p).val i j) x - partialDeriv ν (fun p => (A μ p).val i j) x + ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) i j := by
      exact curvatureSl2c_val_eq A μ ν x hAμ hAν i j

    rw [h_F_ji, h_F_ij]

    have h_star_add : ∀ a b : ℂ, star (a + b) = star a + star b := star_add
    have h_star_sub : ∀ a b : ℂ, star (a - b) = star a - star b := star_sub
    rw [h_star_add, h_star_sub]

    have h_star_A_nu : (fun p => star ((A ν p).val j i)) = fun p => - (A ν p).val i j := by
      ext p
      have h_eq : (A ν p).val.conjTranspose i j = (- (A ν p).val) i j := by rw [(h_su2 ν p).2]
      exact h_eq

    have h_star_A_mu : (fun p => star ((A μ p).val j i)) = fun p => - (A μ p).val i j := by
      ext p
      have h_eq : (A μ p).val.conjTranspose i j = (- (A μ p).val) i j := by rw [(h_su2 μ p).2]
      exact h_eq

    have hd_nu : star (partialDeriv μ (fun p => (A ν p).val j i) x) = - partialDeriv μ (fun p => (A ν p).val i j) x := by
      rw [← partialDeriv_star _ _ _ (hAν j i)]
      rw [h_star_A_nu]
      have h_neg : (fun p => - (A ν p).val i j) = fun p => (-1 : ℂ) * (A ν p).val i j := by ext p; ring
      rw [h_neg]
      rw [partialDeriv_const_smul (-1) _ μ x (hAν i j)]
      ring

    have hd_mu : star (partialDeriv ν (fun p => (A μ p).val j i) x) = - partialDeriv ν (fun p => (A μ p).val i j) x := by
      rw [← partialDeriv_star _ _ _ (hAμ j i)]
      rw [h_star_A_mu]
      have h_neg : (fun p => - (A μ p).val i j) = fun p => (-1 : ℂ) * (A μ p).val i j := by ext p; ring
      rw [h_neg]
      rw [partialDeriv_const_smul (-1) _ ν x (hAμ i j)]
      ring

    have h_comm_su2 : ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val).conjTranspose = - ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) := by
      have h1 : ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val).conjTranspose = ((A μ x).val * (A ν x).val).conjTranspose - ((A ν x).val * (A μ x).val).conjTranspose := star_sub _ _
      have h2 : ((A μ x).val * (A ν x).val).conjTranspose = (A ν x).val.conjTranspose * (A μ x).val.conjTranspose := Matrix.star_mul ((A μ x).val) ((A ν x).val)
      have h3 : ((A ν x).val * (A μ x).val).conjTranspose = (A μ x).val.conjTranspose * (A ν x).val.conjTranspose := Matrix.star_mul ((A ν x).val) ((A μ x).val)
      rw [h1, h2, h3, (h_su2 ν x).2, (h_su2 μ x).2]
      simp only [neg_mul_neg]
      exact neg_sub _ _ |>.symm

    have h_comm : star (((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) j i) = - ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) i j := by
      have h1 : star (((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) j i) = ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val).conjTranspose i j := rfl
      rw [h1, h_comm_su2]
      rfl

    rw [hd_nu, hd_mu, h_comm]
    ring

/-- By applying the positive definite trace property to the SU(2) curvature defect, we prove the topological origin of strictly positive inertial mass. -/
@[litlib_track "Topological Mass Gap"]
theorem topologicalMassGap (pu : PhysicalUniverse) :
  ∀ (x : SpacetimePoint),
  (∀ μ p, isSu2 (pu.toUniverse.asd_sector.val μ p).val) →
  (∃ μ ν, curvatureSl2c pu.toUniverse.asd_sector.val μ ν x ≠ 0) →
  inertialMass pu x > 0 := by
  intro x h_su2 h_defect
  unfold inertialMass
  rcases h_defect with ⟨μ0, ν0, hF_neq⟩
  apply Finset.sum_pos'
  · intro μ _
    apply Finset.sum_nonneg
    intro ν _
    have hF_su2 : isSu2 (curvatureSl2c pu.toUniverse.asd_sector.val μ ν x).val := curvature_is_su2 pu x μ ν h_su2
    exact su2_trace_sq_nonneg _ hF_su2
  · use μ0
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · intro ν _
      have hF_su2 : isSu2 (curvatureSl2c pu.toUniverse.asd_sector.val μ0 ν x).val := curvature_is_su2 pu x μ0 ν h_su2
      exact su2_trace_sq_nonneg _ hF_su2
    · use ν0
      refine ⟨Finset.mem_univ _, ?_⟩
      have hF0_su2 : isSu2 (curvatureSl2c pu.toUniverse.asd_sector.val μ0 ν0 x).val := curvature_is_su2 pu x μ0 ν0 h_su2
      have hF0_neq : (curvatureSl2c pu.toUniverse.asd_sector.val μ0 ν0 x).val ≠ 0 := fun h => hF_neq (Subtype.ext h)
      exact su2_trace_sq_pos _ hF0_su2 hF0_neq

end CGD.Particles

-- FILENAME: CGD/Cosmology/DarkMatter.lean

import CGD.Axioms.PhysicalUniverse
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Spacetime
import CGD.Particles.Mass

open CGD.Axioms
open CGD.Foundations
open CGD.Particles

namespace CGD.Cosmology

def isPureNonAbelian (F : Fin 4 → Fin 4 → SL2C) : Prop :=
  ⁅F 1 2, F 2 3⁆ ≠ 0

/-- Phase 1: Prove the logical contrapositive that a non-zero commutator requires non-zero constituent matrices. -/
lemma non_abelian_implies_nonzero (M N : SL2C) (h : ⁅M, N⁆ ≠ 0) : 
  M ≠ 0 := by
  intro hM
  rw [hM] at h
  simp at h

/-- Phase 2: Prove that the physical self-interaction scattering tensor (the commutator) is itself an SU(2) matrix. -/
lemma commutator_is_su2 (M N : Matrix (Fin 2) (Fin 2) ℂ) (hM : isSu2 M) (hN : isSu2 N) : 
  isSu2 (M * N - N * M) := by
  rcases hM with ⟨hM_tr, hM_adj⟩
  rcases hN with ⟨hN_tr, hN_adj⟩
  constructor
  · -- Trace is 0
    have h1 : Matrix.trace (M * N - N * M) = Matrix.trace (M * N) - Matrix.trace (N * M) := Matrix.trace_sub _ _
    have h2 : Matrix.trace (N * M) = Matrix.trace (M * N) := Matrix.trace_mul_comm N M
    rw [h1, h2, sub_self]
  · -- Adjoint is negative self
    have h1 : (M * N - N * M).conjTranspose = (M * N).conjTranspose - (N * M).conjTranspose := star_sub _ _
    have h2 : (M * N).conjTranspose = N.conjTranspose * M.conjTranspose := star_mul _ _
    have h3 : (N * M).conjTranspose = M.conjTranspose * N.conjTranspose := star_mul _ _
    rw [h1, h2, h3, hM_adj, hN_adj]
    simp only [neg_mul_neg]
    exact neg_sub (M * N) (N * M) |>.symm

Litlib.theorem
  description "Emergent Dark Matter Profile"
/-- A pure non-Abelian defect mathematically requires inertial mass > 0, and guarantees a strictly non-zero self-interaction topological density. -/
theorem emergentDarkMatterProfile (pu : PhysicalUniverse) :
  ∀ (x : SpacetimePoint),
  (∀ μ p, isSu2 (pu.toUniverse.asd_sector.val μ p).val) →
  isPureNonAbelian (fun m n => curvatureSl2c pu.toUniverse.asd_sector.val m n x) →
  inertialMass pu x > 0 ∧
  Matrix.trace (⁅curvatureSl2c pu.toUniverse.asd_sector.val 1 2 x, curvatureSl2c pu.toUniverse.asd_sector.val 2 3 x⁆.val * 
                ⁅curvatureSl2c pu.toUniverse.asd_sector.val 1 2 x, curvatureSl2c pu.toUniverse.asd_sector.val 2 3 x⁆.val) ≠ 0 := by
  intro x h_su2 h_dark
  constructor
  · -- Mass Gap
    apply topologicalMassGap pu x h_su2
    have h_comm : ⁅curvatureSl2c pu.toUniverse.asd_sector.val 1 2 x, curvatureSl2c pu.toUniverse.asd_sector.val 2 3 x⁆ ≠ 0 := h_dark
    exact non_abelian_implies_nonzero _ _ h_comm
  · -- Self-interaction density
    let F12 := curvatureSl2c pu.toUniverse.asd_sector.val 1 2 x
    let F23 := curvatureSl2c pu.toUniverse.asd_sector.val 2 3 x
    have h_comm_neq : ⁅F12, F23⁆ ≠ 0 := h_dark
    have h_comm_val_neq : ⁅F12, F23⁆.val ≠ 0 := fun h => h_comm_neq (Subtype.ext h)
    have h_su2_F12 : isSu2 F12.val := curvature_is_su2 pu x 1 2 h_su2
    have h_su2_F23 : isSu2 F23.val := curvature_is_su2 pu x 2 3 h_su2
    have h_comm_val_eq : ⁅F12, F23⁆.val = F12.val * F23.val - F23.val * F12.val := rfl
    have h_comm_su2 : isSu2 (⁅F12, F23⁆.val) := by
      rw [h_comm_val_eq]
      exact commutator_is_su2 F12.val F23.val h_su2_F12 h_su2_F23
    have h_pos := su2_trace_sq_pos ⁅F12, F23⁆.val h_comm_su2 h_comm_val_neq
    intro h_tr_zero
    have h_re_zero : (Matrix.trace (⁅F12, F23⁆.val * ⁅F12, F23⁆.val)).re = 0 := by rw [h_tr_zero]; rfl
    linarith

end CGD.Cosmology

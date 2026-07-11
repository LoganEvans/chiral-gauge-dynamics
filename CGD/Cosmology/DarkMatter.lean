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
  ∃ μ ν ρ σ, ⁅F μ ν, F ρ σ⁆ ≠ 0

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

/--
A purely non-Abelian defect (lacking a stable U(1) Abelian projection) possesses no electric charge. However, it mathematically requires an inertial mass > 0 and guarantees a non-zero self-interaction topological density, matching the phenomenological profile of Self-Interacting Dark Matter (SIDM).
-/
@[litlib_track "Emergent Dark Matter Profile"]
theorem emergentDarkMatterProfile (pu : PhysicalUniverse) :
  ∀ (x : SpacetimePoint),
  (∀ μ p, isSu2 (pu.toUniverse.asd_sector.val μ p).val) →
  isPureNonAbelian (fun m n => curvatureSl2c pu.toUniverse.asd_sector.val m n x) →
  inertialMass pu x > 0 ∧
  ∃ α β γ δ, Matrix.trace (⁅curvatureSl2c pu.toUniverse.asd_sector.val α β x, curvatureSl2c pu.toUniverse.asd_sector.val γ δ x⁆.val *
                ⁅curvatureSl2c pu.toUniverse.asd_sector.val α β x, curvatureSl2c pu.toUniverse.asd_sector.val γ δ x⁆.val) ≠ 0 := by
  intro x h_su2 h_dark
  rcases h_dark with ⟨α, β, γ, δ, h_comm_neq⟩
  constructor
  · -- Mass Gap
    apply topologicalMassGap pu x h_su2
    use α, β
    exact non_abelian_implies_nonzero _ _ h_comm_neq
  · -- Self-interaction density
    use α, β, γ, δ
    let F_ab := curvatureSl2c pu.toUniverse.asd_sector.val α β x
    let F_gd := curvatureSl2c pu.toUniverse.asd_sector.val γ δ x
    have h_comm_val_neq : ⁅F_ab, F_gd⁆.val ≠ 0 := fun h => h_comm_neq (Subtype.ext h)
    have h_su2_F_ab : isSu2 F_ab.val := curvature_is_su2 pu x α β h_su2
    have h_su2_F_gd : isSu2 F_gd.val := curvature_is_su2 pu x γ δ h_su2
    have h_comm_val_eq : ⁅F_ab, F_gd⁆.val = F_ab.val * F_gd.val - F_gd.val * F_ab.val := rfl
    have h_comm_su2 : isSu2 (⁅F_ab, F_gd⁆.val) := by
      rw [h_comm_val_eq]
      exact commutator_is_su2 F_ab.val F_gd.val h_su2_F_ab h_su2_F_gd
    have h_pos := su2_trace_sq_pos ⁅F_ab, F_gd⁆.val h_comm_su2 h_comm_val_neq
    intro h_tr_zero
    have h_re_zero : (Matrix.trace (⁅F_ab, F_gd⁆.val * ⁅F_ab, F_gd⁆.val)).re = 0 := by rw [h_tr_zero]; rfl
    linarith

end CGD.Cosmology

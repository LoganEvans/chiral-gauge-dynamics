-- FILENAME: CGD/Foundations/ChiralDecomposition.lean

import Litlib.Core
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Spacetime
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Foundations.Action
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CGD.Axioms.PhysicalUniverse

open Complex Matrix CGD.Foundations CGD.Math BigOperators
open CGD.Axioms

namespace CGD.Foundations

-- ==============================================================================
-- ALGEBRAIC HELPERS FOR CHIRAL DECOMPOSITION
-- ==============================================================================

lemma sl2c_bracket_val (A B : SL2C) : ⁅A, B⁆.val = A.val * B.val - B.val * A.val := rfl

lemma embed_self_dual_bracket (A B : SL2C) :
  embedSelfDual ⁅A, B⁆ = embedSelfDual A * embedSelfDual B - embedSelfDual B * embedSelfDual A := by
  ext i j
  let x := chiralIso.symm i
  let y := chiralIso.symm j
  have hi : i = chiralIso x := (Equiv.apply_symm_apply chiralIso i).symm
  have hj : j = chiralIso y := (Equiv.apply_symm_apply chiralIso j).symm
  rw[hi, hj, Matrix.sub_apply, embed_self_dual_mul_apply, embed_self_dual_mul_apply]
  unfold embedSelfDual
  simp only[Matrix.of_apply, Equiv.symm_apply_apply]
  cases x <;> cases y
  · rw[sl2c_bracket_val A B]; rfl
  · change (0 : Complex) = 0 - 0; ring
  · change (0 : Complex) = 0 - 0; ring
  · change (0 : Complex) = 0 - 0; ring

lemma embed_anti_self_dual_bracket (A B : SL2C) :
  embedAntiSelfDual ⁅A, B⁆ = embedAntiSelfDual A * embedAntiSelfDual B - embedAntiSelfDual B * embedAntiSelfDual A := by
  ext i j
  let x := chiralIso.symm i
  let y := chiralIso.symm j
  have hi : i = chiralIso x := (Equiv.apply_symm_apply chiralIso i).symm
  have hj : j = chiralIso y := (Equiv.apply_symm_apply chiralIso j).symm
  rw[hi, hj, Matrix.sub_apply, embed_anti_self_dual_mul_apply, embed_anti_self_dual_mul_apply]
  unfold embedAntiSelfDual
  simp only[Matrix.of_apply, Equiv.symm_apply_apply]
  cases x <;> cases y
  · change (0 : Complex) = 0 - 0; ring
  · change (0 : Complex) = 0 - 0; ring
  · change (0 : Complex) = 0 - 0; ring
  · rw[sl2c_bracket_val A B]; rfl

lemma bracket_embed (L1 L2 R1 R2 : SL2C) :
  bracket (embedSelfDual L1 + embedAntiSelfDual R1) (embedSelfDual L2 + embedAntiSelfDual R2) =
  embedSelfDual ⁅L1, L2⁆ + embedAntiSelfDual ⁅R1, R2⁆ := by
  unfold bracket
  have h1 : (embedSelfDual L1 + embedAntiSelfDual R1) * (embedSelfDual L2 + embedAntiSelfDual R2) =
    embedSelfDual L1 * embedSelfDual L2 + embedAntiSelfDual R1 * embedAntiSelfDual R2 := by
    rw[Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    have h_ortho1 := chiralOrthogonality L1 R2
    have h_ortho2 := chiralOrthogonalityDl R1 L2
    rw[h_ortho1, h_ortho2]
    simp only[add_zero, zero_add]
  have h2 : (embedSelfDual L2 + embedAntiSelfDual R2) * (embedSelfDual L1 + embedAntiSelfDual R1) =
    embedSelfDual L2 * embedSelfDual L1 + embedAntiSelfDual R2 * embedAntiSelfDual R1 := by
    rw[Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    have h_ortho1 := chiralOrthogonality L2 R1
    have h_ortho2 := chiralOrthogonalityDl R2 L1
    rw[h_ortho1, h_ortho2]
    simp only[add_zero, zero_add]
  rw[h1, h2]
  have h3 : embedSelfDual L1 * embedSelfDual L2 + embedAntiSelfDual R1 * embedAntiSelfDual R2 -
    (embedSelfDual L2 * embedSelfDual L1 + embedAntiSelfDual R2 * embedAntiSelfDual R1) =
    (embedSelfDual L1 * embedSelfDual L2 - embedSelfDual L2 * embedSelfDual L1) +
    (embedAntiSelfDual R1 * embedAntiSelfDual R2 - embedAntiSelfDual R2 * embedAntiSelfDual R1) := by abel
  rw[h3]
  rw[← embed_self_dual_bracket L1 L2, ← embed_anti_self_dual_bracket R1 R2]

lemma embed_linear_combo (L1 L2 L3 R1 R2 R3 : SL2C) :
  (embedSelfDual L1 + embedAntiSelfDual R1) - (embedSelfDual L2 + embedAntiSelfDual R2) + (embedSelfDual L3 + embedAntiSelfDual R3) =
  embedSelfDual (L1 - L2 + L3) + embedAntiSelfDual (R1 - R2 + R3) := by
  ext i j
  simp only[Matrix.add_apply, Matrix.sub_apply]
  unfold embedSelfDual embedAntiSelfDual
  simp only[Matrix.of_apply]
  cases hi : chiralIso.symm i with
  | inl il =>
    cases hj : chiralIso.symm j with
    | inl jl => dsimp; ring
    | inr jr => dsimp; ring
  | inr ir =>
    cases hj : chiralIso.symm j with
    | inl jl => dsimp; ring
    | inr jr => dsimp; ring

lemma extract_self_dual_block (u : Universe) (ν : Fin 4) (p : SpacetimePoint) (i j : Fin 2) :
  (u.spin4c_connection ν p) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) = (u.sd_sector ν p).val i j := by
  rw [spin4c_connection_eq_embed]
  unfold embedSelfDual embedAntiSelfDual
  simp only[Matrix.add_apply, Matrix.of_apply, Equiv.symm_apply_apply]
  exact add_zero _

lemma extract_anti_self_dual_block (u : Universe) (ν : Fin 4) (p : SpacetimePoint) (i j : Fin 2) :
  (u.spin4c_connection ν p) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) = (u.asd_sector ν p).val i j := by
  rw [spin4c_connection_eq_embed]
  unfold embedSelfDual embedAntiSelfDual
  simp only[Matrix.add_apply, Matrix.of_apply, Equiv.symm_apply_apply]
  exact zero_add _

lemma to_sl2c_self (A : SL2C) : toSl2c A.val = A := by
  have h_tr : Matrix.trace A.val = 0 := by rw[← mem_sl_iff]; exact A.property
  apply Subtype.ext
  unfold toSl2c
  dsimp
  rw[h_tr]
  simp

lemma to_sl2c_self_dual_eq (u : Universe) (ν : Fin 4) :
  (fun p => toSl2c (fun i j => (u.spin4c_connection ν p) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)))) = (fun p => u.sd_sector ν p) := by
  ext p
  have h1 : (fun i j => (u.spin4c_connection ν p) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j))) = (u.sd_sector ν p).val := by
    ext i j; exact extract_self_dual_block u ν p i j
  rw[h1, to_sl2c_self]

lemma to_sl2c_anti_self_dual_eq (u : Universe) (ν : Fin 4) :
  (fun p => toSl2c (fun i j => (u.spin4c_connection ν p) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)))) = (fun p => u.asd_sector ν p) := by
  ext p
  have h1 : (fun i j => (u.spin4c_connection ν p) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j))) = (u.asd_sector ν p).val := by
    ext i j; exact extract_anti_self_dual_block u ν p i j
  rw[h1, to_sl2c_self]

theorem nativeEmbedDerivative (u : Universe) (μ ν : Fin 4) (x : SpacetimePoint) :
  partialDerivChiral μ (fun p => u.spin4c_connection ν p) x =
  embedSelfDual (partialDerivSl2c μ (u.sd_sector ν) x) + embedAntiSelfDual (partialDerivSl2c μ (u.asd_sector ν) x) := by
  unfold partialDerivChiral
  have hL : (fun p => toSl2c (fun i j => (u.spin4c_connection ν p) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)))) = u.sd_sector ν := to_sl2c_self_dual_eq u ν
  have hR : (fun p => toSl2c (fun i j => (u.spin4c_connection ν p) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)))) = u.asd_sector ν := to_sl2c_anti_self_dual_eq u ν
  rw[hL, hR]

lemma curvature_embed_eq (u : Universe) (mu nu : Fin 4) (x : SpacetimePoint) :
  curvature (fun m p => u.spin4c_connection m p) mu nu x =
  embedSelfDual (curvatureSl2c u.sd_sector mu nu x) + embedAntiSelfDual (curvatureSl2c u.asd_sector mu nu x) := by
  unfold curvature curvatureSl2c
  rw[nativeEmbedDerivative _ _ _]
  rw[nativeEmbedDerivative _ _ _]
  have h_mu : (fun m p => u.spin4c_connection m p) mu x = embedSelfDual (u.sd_sector mu x) + embedAntiSelfDual (u.asd_sector mu x) := spin4c_connection_eq_embed u mu x
  have h_nu : (fun m p => u.spin4c_connection m p) nu x = embedSelfDual (u.sd_sector nu x) + embedAntiSelfDual (u.asd_sector nu x) := spin4c_connection_eq_embed u nu x
  rw [h_mu, h_nu]
  rw [bracket_embed]
  change embedSelfDual (partialDerivSl2c mu (u.sd_sector nu) x) + embedAntiSelfDual (partialDerivSl2c mu (u.asd_sector nu) x) -
         (embedSelfDual (partialDerivSl2c nu (u.sd_sector mu) x) + embedAntiSelfDual (partialDerivSl2c nu (u.asd_sector mu) x)) +
         (embedSelfDual (chiralProject (embedSelfDual ⁅u.sd_sector mu x, u.sd_sector nu x⁆ + embedAntiSelfDual ⁅u.asd_sector mu x, u.asd_sector nu x⁆)).self_dual +
          embedAntiSelfDual (chiralProject (embedSelfDual ⁅u.sd_sector mu x, u.sd_sector nu x⁆ + embedAntiSelfDual ⁅u.asd_sector mu x, u.asd_sector nu x⁆)).anti_self_dual) =
         embedSelfDual (partialDerivSl2c mu (u.sd_sector nu) x - partialDerivSl2c nu (u.sd_sector mu) x + ⁅u.sd_sector mu x, u.sd_sector nu x⁆) +
         embedAntiSelfDual (partialDerivSl2c mu (u.asd_sector nu) x - partialDerivSl2c nu (u.asd_sector mu) x + ⁅u.asd_sector mu x, u.asd_sector nu x⁆)
  rw [chiralProject_embed_sd, chiralProject_embed_asd]
  exact embed_linear_combo _ _ _ _ _ _

-- ==============================================================================
-- THE DECOMPOSITION THEOREM
-- ==============================================================================

/--
The topological Pontryagin action strictly preserves the chiral split. Because the cross terms vanish orthogonally, the 4D spacetime topology cleanly factorizes into a self-dual topological charge and an anti-self-dual topological charge.
-/
@[litlib_track "Topological Chiral Decomposition"]
theorem algebraicChiralDecomposition (pu : PhysicalUniverse) (x : SpacetimePoint) :
  lagrangianDensity (fun mu nu => curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x) =
  actionVacuum (fun mu nu => curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x) +
  actionAntiSelfDual (fun mu nu => curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x) := by
  unfold lagrangianDensity actionVacuum actionAntiSelfDual
  have h_proj_L : ∀ mu nu,
    (chiralProject (curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x)).self_dual = curvatureSl2c pu.toUniverse.sd_sector mu nu x := by
    intro mu nu
    rw [curvature_embed_eq pu.toUniverse mu nu x]
    exact chiralProject_embed_sd _ _
  have h_proj_R : ∀ mu nu,
    (chiralProject (curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x)).anti_self_dual = curvatureSl2c pu.toUniverse.asd_sector mu nu x := by
    intro mu nu
    rw [curvature_embed_eq pu.toUniverse mu nu x]
    exact chiralProject_embed_asd _ _
  have h_trace : ∀ mu nu rho sigma,
    Matrix.trace (curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x * curvature (fun m p => pu.toUniverse.spin4c_connection m p) rho sigma x) =
    Matrix.trace ((curvatureSl2c pu.toUniverse.sd_sector mu nu x).val * (curvatureSl2c pu.toUniverse.sd_sector rho sigma x).val) +
    Matrix.trace ((curvatureSl2c pu.toUniverse.asd_sector mu nu x).val * (curvatureSl2c pu.toUniverse.asd_sector rho sigma x).val) := by
    intro mu nu rho sigma
    rw [curvature_embed_eq pu.toUniverse mu nu x, curvature_embed_eq pu.toUniverse rho sigma x]
    exact trace_embed_mul_embed _ _ _ _
  simp only [h_proj_L, h_proj_R, h_trace]
  simp only [mul_add, Finset.sum_add_distrib]

end CGD.Foundations

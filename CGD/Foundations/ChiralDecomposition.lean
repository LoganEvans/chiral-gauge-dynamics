-- FILENAME: CGD/Foundations/ChiralDecomposition.lean

import Litlib.Core
import CGD.Foundations.GaugeGroup
import CGD.Axioms.Spacetime
import CGD.Foundations.Calculus
import CGD.Foundations.Action
import CGD.Foundations.Lagrangian
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CGD.Axioms.Ontology

open Complex Matrix CGD.Foundations BigOperators
open CGD.Axioms

namespace CGD.Foundations

-- ==============================================================================
-- ALGEBRAIC HELPERS FOR CHIRAL DECOMPOSITION
-- ==============================================================================

lemma sl2c_bracket_val (A B : SL2C) : ⁅A, B⁆.val = A.val * B.val - B.val * A.val := rfl

lemma embed_self_dual_inr_left (A : SL2C) (i : Fin 2) (j : Fin 4) :
  (embedSelfDual A) (chiralIso (Sum.inr i)) j = 0 := by
  unfold embedSelfDual
  simp only[Matrix.of_apply, Equiv.symm_apply_apply]

lemma embed_self_dual_inr_right (A : SL2C) (i : Fin 4) (j : Fin 2) :
  (embedSelfDual A) i (chiralIso (Sum.inr j)) = 0 := by
  unfold embedSelfDual
  simp only [Matrix.of_apply, Equiv.symm_apply_apply]
  cases chiralIso.symm i
  · rfl
  · rfl

lemma embed_anti_self_dual_inl_left (A : SL2C) (i : Fin 2) (j : Fin 4) :
  (embedAntiSelfDual A) (chiralIso (Sum.inl i)) j = 0 := by
  unfold embedAntiSelfDual
  simp only[Matrix.of_apply, Equiv.symm_apply_apply]

lemma embed_anti_self_dual_inl_right (A : SL2C) (i : Fin 4) (j : Fin 2) :
  (embedAntiSelfDual A) i (chiralIso (Sum.inl j)) = 0 := by
  unfold embedAntiSelfDual
  simp only [Matrix.of_apply, Equiv.symm_apply_apply]
  cases chiralIso.symm i
  · rfl
  · rfl

lemma embed_self_dual_inl_inl (A : SL2C) (i j : Fin 2) :
  (embedSelfDual A) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) = A.val i j := by
  unfold embedSelfDual
  simp only[Matrix.of_apply, Equiv.symm_apply_apply]

lemma embed_anti_self_dual_inr_inr (A : SL2C) (i j : Fin 2) :
  (embedAntiSelfDual A) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) = A.val i j := by
  unfold embedAntiSelfDual
  simp only [Matrix.of_apply, Equiv.symm_apply_apply]

lemma embed_self_dual_mul_inl_inl (A B : SL2C) (i j : Fin 2) :
  (embedSelfDual A * embedSelfDual B) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) =
  (A.val * B.val) i j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw[← Equiv.sum_comp chiralIso (fun k => (embedSelfDual A) (chiralIso (Sum.inl i)) k * (embedSelfDual B) k (chiralIso (Sum.inl j)))]
  rw[Fintype.sum_sum_type]
  have h_inr : ∑ x : Fin 2, (embedSelfDual A) (chiralIso (Sum.inl i)) (chiralIso (Sum.inr x)) * (embedSelfDual B) (chiralIso (Sum.inr x)) (chiralIso (Sum.inl j)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [embed_self_dual_inr_right]
    exact zero_mul _
  rw [h_inr, add_zero]
  apply Finset.sum_congr rfl
  intro x _
  rw[embed_self_dual_inl_inl, embed_self_dual_inl_inl]

lemma embed_anti_self_dual_mul_inr_inr (A B : SL2C) (i j : Fin 2) :
  (embedAntiSelfDual A * embedAntiSelfDual B) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) =
  (A.val * B.val) i j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw[← Equiv.sum_comp chiralIso (fun k => (embedAntiSelfDual A) (chiralIso (Sum.inr i)) k * (embedAntiSelfDual B) k (chiralIso (Sum.inr j)))]
  rw [Fintype.sum_sum_type]
  have h_inl : ∑ x : Fin 2, (embedAntiSelfDual A) (chiralIso (Sum.inr i)) (chiralIso (Sum.inl x)) * (embedAntiSelfDual B) (chiralIso (Sum.inl x)) (chiralIso (Sum.inr j)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw[embed_anti_self_dual_inl_right]
    exact zero_mul _
  rw[h_inl, zero_add]
  apply Finset.sum_congr rfl
  intro x _
  rw[embed_anti_self_dual_inr_inr, embed_anti_self_dual_inr_inr]

lemma embed_self_dual_mul_apply (A B : SL2C) (x y : Fin 2 ⊕ Fin 2) :
  (embedSelfDual A * embedSelfDual B) (chiralIso x) (chiralIso y) =
  match x, y with
  | Sum.inl i, Sum.inl j => (A.val * B.val) i j
  | _, _ => 0 := by
  cases x <;> cases y
  · exact embed_self_dual_mul_inl_inl A B _ _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_self_dual_inr_right]; exact mul_zero _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_self_dual_inr_left]; exact zero_mul _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_self_dual_inr_left]; exact zero_mul _

lemma embed_anti_self_dual_mul_apply (A B : SL2C) (x y : Fin 2 ⊕ Fin 2) :
  (embedAntiSelfDual A * embedAntiSelfDual B) (chiralIso x) (chiralIso y) =
  match x, y with
  | Sum.inr i, Sum.inr j => (A.val * B.val) i j
  | _, _ => 0 := by
  cases x <;> cases y
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_anti_self_dual_inl_left]; exact zero_mul _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_anti_self_dual_inl_left]; exact zero_mul _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_anti_self_dual_inl_right]; exact mul_zero _
  · exact embed_anti_self_dual_mul_inr_inr A B _ _

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

lemma orthogonality_term (A B : SL2C) (i j k : Fin 4) :
  (embedSelfDual A) i k * (embedAntiSelfDual B) k j = 0 := by
  rw[embedSelfDual, embedAntiSelfDual]
  rw [Matrix.of_apply, Matrix.of_apply]
  cases hk : chiralIso.symm k with
  | inl kl => exact mul_zero _
  | inr kr =>
    cases hi : chiralIso.symm i with
    | inl il => exact zero_mul _
    | inr ir => exact zero_mul _

lemma chiralOrthogonality (A B : SL2C) : (embedSelfDual A) * (embedAntiSelfDual B) = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply orthogonality_term

lemma orthogonality_term_dl (A B : SL2C) (i j k : Fin 4) :
  (embedAntiSelfDual A) i k * (embedSelfDual B) k j = 0 := by
  rw[embedAntiSelfDual, embedSelfDual]
  rw [Matrix.of_apply, Matrix.of_apply]
  cases hk : chiralIso.symm k with
  | inl kl =>
    cases hi : chiralIso.symm i with
    | inl il => exact zero_mul _
    | inr ir => exact zero_mul _
  | inr kr =>
    cases hj : chiralIso.symm j with
    | inl jl => exact mul_zero _
    | inr jr => exact mul_zero _

lemma chiralOrthogonalityDl (A B : SL2C) : (embedAntiSelfDual A) * (embedSelfDual B) = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply orthogonality_term_dl

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

lemma trace_embed_self_dual_mul (A B : SL2C) :
  Matrix.trace (embedSelfDual A * embedSelfDual B) = Matrix.trace (A.val * B.val) := by
  rw [Matrix.trace, Matrix.trace]
  simp only[Matrix.diag]
  rw[← Equiv.sum_comp chiralIso (fun i => (embedSelfDual A * embedSelfDual B) i i)]
  rw [Fintype.sum_sum_type]
  have h_inr : ∑ x : Fin 2, (embedSelfDual A * embedSelfDual B) (chiralIso (Sum.inr x)) (chiralIso (Sum.inr x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    have hz : (embedSelfDual A) (chiralIso (Sum.inr x)) k = 0 := embed_self_dual_inr_left A x k
    rw[hz, zero_mul]
  rw [h_inr, add_zero]
  apply Finset.sum_congr rfl
  intro x _
  rw [embed_self_dual_mul_inl_inl]

lemma trace_embed_anti_self_dual_mul (A B : SL2C) :
  Matrix.trace (embedAntiSelfDual A * embedAntiSelfDual B) = Matrix.trace (A.val * B.val) := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag]
  rw[← Equiv.sum_comp chiralIso (fun i => (embedAntiSelfDual A * embedAntiSelfDual B) i i)]
  rw [Fintype.sum_sum_type]
  have h_inl : ∑ x : Fin 2, (embedAntiSelfDual A * embedAntiSelfDual B) (chiralIso (Sum.inl x)) (chiralIso (Sum.inl x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    have hz : (embedAntiSelfDual A) (chiralIso (Sum.inl x)) k = 0 := embed_anti_self_dual_inl_left A x k
    rw [hz, zero_mul]
  rw[h_inl, zero_add]
  apply Finset.sum_congr rfl
  intro x _
  rw[embed_anti_self_dual_mul_inr_inr]

lemma trace_embed_mul_embed (L1 R1 L2 R2 : SL2C) :
  Matrix.trace ((embedSelfDual L1 + embedAntiSelfDual R1) * (embedSelfDual L2 + embedAntiSelfDual R2)) =
  Matrix.trace (L1.val * L2.val) + Matrix.trace (R1.val * R2.val) := by
  have h1 : (embedSelfDual L1 + embedAntiSelfDual R1) * (embedSelfDual L2 + embedAntiSelfDual R2) =
    embedSelfDual L1 * embedSelfDual L2 + embedAntiSelfDual R1 * embedAntiSelfDual R2 := by
    rw[Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    rw[chiralOrthogonality, chiralOrthogonalityDl]
    simp
  rw[h1, Matrix.trace_add]
  rw[trace_embed_self_dual_mul, trace_embed_anti_self_dual_mul]

lemma to_sl2c_of_trace_zero (M : Matrix (Fin 2) (Fin 2) Complex) (h : Matrix.trace M = 0) :
  (toSl2c M).val = M := by
  unfold toSl2c
  dsimp
  rw [h]
  have h0 : (0 : Complex) / 2 = 0 := zero_div 2
  rw[h0, zero_smul, sub_zero]

lemma chiral_project_self_dual_embed (L R : SL2C) :
  (chiralProject (embedSelfDual L + embedAntiSelfDual R)).self_dual = L := by
  apply Subtype.ext
  change (toSl2c (fun (i j : Fin 2) =>
    (embedSelfDual L) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) +
    (embedAntiSelfDual R) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)))).val = L.val

  have heq : (fun (i j : Fin 2) =>
    (embedSelfDual L) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) +
    (embedAntiSelfDual R) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j))) = L.val := by
    ext i j
    rw[embed_self_dual_inl_inl]
    have hz : (embedAntiSelfDual R) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) = 0 := by
      exact embed_anti_self_dual_inl_left R i (chiralIso (Sum.inl j))
    rw[hz, add_zero]

  have ht : Matrix.trace (fun (i j : Fin 2) =>
    (embedSelfDual L) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) +
    (embedAntiSelfDual R) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j))) = 0 := by
    rw[heq]
    exact L.property

  rw[to_sl2c_of_trace_zero _ ht]
  exact heq

lemma chiral_project_anti_self_dual_embed (L R : SL2C) :
  (chiralProject (embedSelfDual L + embedAntiSelfDual R)).anti_self_dual = R := by
  apply Subtype.ext
  change (toSl2c (fun (i j : Fin 2) =>
    (embedSelfDual L) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) +
    (embedAntiSelfDual R) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)))).val = R.val

  have heq : (fun (i j : Fin 2) =>
    (embedSelfDual L) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) +
    (embedAntiSelfDual R) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j))) = R.val := by
    ext i j
    rw [embed_anti_self_dual_inr_inr]
    have hz : (embedSelfDual L) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) = 0 := by
      exact embed_self_dual_inr_left L i (chiralIso (Sum.inr j))
    rw [hz, zero_add]

  have ht : Matrix.trace (fun (i j : Fin 2) =>
    (embedSelfDual L) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) +
    (embedAntiSelfDual R) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j))) = 0 := by
    rw[heq]
    exact R.property

  rw[to_sl2c_of_trace_zero _ ht]
  exact heq

lemma extract_self_dual_block (u : Universe) (ν : Fin 4) (p : SpacetimePoint) (i j : Fin 2) :
  (u.spin4c_connection ν p) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) = (u.sd_sector ν p).val i j := by
  unfold Universe.spin4c_connection embedSelfDual embedAntiSelfDual
  simp only[Matrix.add_apply, Matrix.of_apply, Equiv.symm_apply_apply]
  exact add_zero _

lemma extract_anti_self_dual_block (u : Universe) (ν : Fin 4) (p : SpacetimePoint) (i j : Fin 2) :
  (u.spin4c_connection ν p) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) = (u.asd_sector ν p).val i j := by
  unfold Universe.spin4c_connection embedSelfDual embedAntiSelfDual
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
  have h_mu : (fun m p => u.spin4c_connection m p) mu x = embedSelfDual (u.sd_sector mu x) + embedAntiSelfDual (u.asd_sector mu x) := rfl
  have h_nu : (fun m p => u.spin4c_connection m p) nu x = embedSelfDual (u.sd_sector nu x) + embedAntiSelfDual (u.asd_sector nu x) := rfl
  rw [h_mu, h_nu]
  rw [bracket_embed]
  have h_proj_L : (chiralProject (embedSelfDual ⁅u.sd_sector mu x, u.sd_sector nu x⁆ + embedAntiSelfDual ⁅u.asd_sector mu x, u.asd_sector nu x⁆)).self_dual = ⁅u.sd_sector mu x, u.sd_sector nu x⁆ := chiral_project_self_dual_embed _ _
  have h_proj_R : (chiralProject (embedSelfDual ⁅u.sd_sector mu x, u.sd_sector nu x⁆ + embedAntiSelfDual ⁅u.asd_sector mu x, u.asd_sector nu x⁆)).anti_self_dual = ⁅u.asd_sector mu x, u.asd_sector nu x⁆ := chiral_project_anti_self_dual_embed _ _

  change embedSelfDual (partialDerivSl2c mu (u.sd_sector nu) x) + embedAntiSelfDual (partialDerivSl2c mu (u.asd_sector nu) x) -
         (embedSelfDual (partialDerivSl2c nu (u.sd_sector mu) x) + embedAntiSelfDual (partialDerivSl2c nu (u.asd_sector mu) x)) +
         (embedSelfDual (chiralProject (embedSelfDual ⁅u.sd_sector mu x, u.sd_sector nu x⁆ + embedAntiSelfDual ⁅u.asd_sector mu x, u.asd_sector nu x⁆)).self_dual +
          embedAntiSelfDual (chiralProject (embedSelfDual ⁅u.sd_sector mu x, u.sd_sector nu x⁆ + embedAntiSelfDual ⁅u.asd_sector mu x, u.asd_sector nu x⁆)).anti_self_dual) =
         embedSelfDual (partialDerivSl2c mu (u.sd_sector nu) x - partialDerivSl2c nu (u.sd_sector mu) x + ⁅u.sd_sector mu x, u.sd_sector nu x⁆) +
         embedAntiSelfDual (partialDerivSl2c mu (u.asd_sector nu) x - partialDerivSl2c nu (u.asd_sector mu) x + ⁅u.asd_sector mu x, u.asd_sector nu x⁆)

  rw[h_proj_L, h_proj_R]
  exact embed_linear_combo _ _ _ _ _ _

-- ==============================================================================
-- THE DECOMPOSITION THEOREM
-- ==============================================================================

Litlib.theorem
  description "Topological Chiral Decomposition"
/--
The topological Pontryagin action strictly preserves the chiral split. Because the cross terms vanish orthogonally, the 4D spacetime topology cleanly factorizes into a self-dual topological charge and an anti-self-dual topological charge.
-/
theorem algebraicChiralDecomposition (u : Universe) (x : SpacetimePoint) :
  lagrangianDensity (fun mu nu => curvature (fun m p => u.spin4c_connection m p) mu nu x) =
  actionVacuum (fun mu nu => curvature (fun m p => u.spin4c_connection m p) mu nu x) +
  actionAntiSelfDual (fun mu nu => curvature (fun m p => u.spin4c_connection m p) mu nu x) := by
  unfold lagrangianDensity actionVacuum actionAntiSelfDual
  have h_proj_L : ∀ mu nu,
    (chiralProject (curvature (fun m p => u.spin4c_connection m p) mu nu x)).self_dual = curvatureSl2c u.sd_sector mu nu x := by
    intro mu nu
    rw [curvature_embed_eq u mu nu x]
    exact chiral_project_self_dual_embed _ _
  have h_proj_R : ∀ mu nu,
    (chiralProject (curvature (fun m p => u.spin4c_connection m p) mu nu x)).anti_self_dual = curvatureSl2c u.asd_sector mu nu x := by
    intro mu nu
    rw [curvature_embed_eq u mu nu x]
    exact chiral_project_anti_self_dual_embed _ _
  have h_trace : ∀ mu nu rho sigma,
    Matrix.trace (curvature (fun m p => u.spin4c_connection m p) mu nu x * curvature (fun m p => u.spin4c_connection m p) rho sigma x) =
    Matrix.trace ((curvatureSl2c u.sd_sector mu nu x).val * (curvatureSl2c u.sd_sector rho sigma x).val) +
    Matrix.trace ((curvatureSl2c u.asd_sector mu nu x).val * (curvatureSl2c u.asd_sector rho sigma x).val) := by
    intro mu nu rho sigma
    rw [curvature_embed_eq u mu nu x, curvature_embed_eq u rho sigma x]
    exact trace_embed_mul_embed _ _ _ _
  simp only [h_proj_L, h_proj_R, h_trace]
  simp only [mul_add, Finset.sum_add_distrib]

end CGD.Foundations

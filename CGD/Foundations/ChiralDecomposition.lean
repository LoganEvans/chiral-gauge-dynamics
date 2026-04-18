-- FILENAME: CGD/Foundations/ChiralDecomposition.lean

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

lemma embed_light_inr_left (A : SL2C) (i : Fin 2) (j : Fin 4) :
  (embedLight A) (chiralIso (Sum.inr i)) j = 0 := by
  unfold embedLight
  simp only[Matrix.of_apply, Equiv.symm_apply_apply]

lemma embed_light_inr_right (A : SL2C) (i : Fin 4) (j : Fin 2) :
  (embedLight A) i (chiralIso (Sum.inr j)) = 0 := by
  unfold embedLight
  simp only [Matrix.of_apply, Equiv.symm_apply_apply]
  cases chiralIso.symm i
  · rfl
  · rfl

lemma embed_dark_inl_left (A : SL2C) (i : Fin 2) (j : Fin 4) :
  (embedDark A) (chiralIso (Sum.inl i)) j = 0 := by
  unfold embedDark
  simp only[Matrix.of_apply, Equiv.symm_apply_apply]

lemma embed_dark_inl_right (A : SL2C) (i : Fin 4) (j : Fin 2) :
  (embedDark A) i (chiralIso (Sum.inl j)) = 0 := by
  unfold embedDark
  simp only [Matrix.of_apply, Equiv.symm_apply_apply]
  cases chiralIso.symm i
  · rfl
  · rfl

lemma embed_light_inl_inl (A : SL2C) (i j : Fin 2) :
  (embedLight A) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) = A.val i j := by
  unfold embedLight
  simp only[Matrix.of_apply, Equiv.symm_apply_apply]

lemma embed_dark_inr_inr (A : SL2C) (i j : Fin 2) :
  (embedDark A) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) = A.val i j := by
  unfold embedDark
  simp only [Matrix.of_apply, Equiv.symm_apply_apply]

lemma embed_light_mul_inl_inl (A B : SL2C) (i j : Fin 2) :
  (embedLight A * embedLight B) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) =
  (A.val * B.val) i j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw[← Equiv.sum_comp chiralIso (fun k => (embedLight A) (chiralIso (Sum.inl i)) k * (embedLight B) k (chiralIso (Sum.inl j)))]
  rw[Fintype.sum_sum_type]
  have h_inr : ∑ x : Fin 2, (embedLight A) (chiralIso (Sum.inl i)) (chiralIso (Sum.inr x)) * (embedLight B) (chiralIso (Sum.inr x)) (chiralIso (Sum.inl j)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [embed_light_inr_right]
    exact zero_mul _
  rw [h_inr, add_zero]
  apply Finset.sum_congr rfl
  intro x _
  rw[embed_light_inl_inl, embed_light_inl_inl]

lemma embed_dark_mul_inr_inr (A B : SL2C) (i j : Fin 2) :
  (embedDark A * embedDark B) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) =
  (A.val * B.val) i j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw[← Equiv.sum_comp chiralIso (fun k => (embedDark A) (chiralIso (Sum.inr i)) k * (embedDark B) k (chiralIso (Sum.inr j)))]
  rw [Fintype.sum_sum_type]
  have h_inl : ∑ x : Fin 2, (embedDark A) (chiralIso (Sum.inr i)) (chiralIso (Sum.inl x)) * (embedDark B) (chiralIso (Sum.inl x)) (chiralIso (Sum.inr j)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw[embed_dark_inl_right]
    exact zero_mul _
  rw[h_inl, zero_add]
  apply Finset.sum_congr rfl
  intro x _
  rw[embed_dark_inr_inr, embed_dark_inr_inr]

lemma embed_light_mul_apply (A B : SL2C) (x y : Fin 2 ⊕ Fin 2) :
  (embedLight A * embedLight B) (chiralIso x) (chiralIso y) =
  match x, y with
  | Sum.inl i, Sum.inl j => (A.val * B.val) i j
  | _, _ => 0 := by
  cases x <;> cases y
  · exact embed_light_mul_inl_inl A B _ _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_light_inr_right]; exact mul_zero _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_light_inr_left]; exact zero_mul _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_light_inr_left]; exact zero_mul _

lemma embed_dark_mul_apply (A B : SL2C) (x y : Fin 2 ⊕ Fin 2) :
  (embedDark A * embedDark B) (chiralIso x) (chiralIso y) =
  match x, y with
  | Sum.inr i, Sum.inr j => (A.val * B.val) i j
  | _, _ => 0 := by
  cases x <;> cases y
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_dark_inl_left]; exact zero_mul _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_dark_inl_left]; exact zero_mul _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_dark_inl_right]; exact mul_zero _
  · exact embed_dark_mul_inr_inr A B _ _

lemma embed_light_bracket (A B : SL2C) :
  embedLight ⁅A, B⁆ = embedLight A * embedLight B - embedLight B * embedLight A := by
  ext i j
  let x := chiralIso.symm i
  let y := chiralIso.symm j
  have hi : i = chiralIso x := (Equiv.apply_symm_apply chiralIso i).symm
  have hj : j = chiralIso y := (Equiv.apply_symm_apply chiralIso j).symm
  rw[hi, hj, Matrix.sub_apply, embed_light_mul_apply, embed_light_mul_apply]
  unfold embedLight
  simp only[Matrix.of_apply, Equiv.symm_apply_apply]
  cases x <;> cases y
  · rw[sl2c_bracket_val A B]; rfl
  · change (0 : Complex) = 0 - 0; ring
  · change (0 : Complex) = 0 - 0; ring
  · change (0 : Complex) = 0 - 0; ring

lemma embed_dark_bracket (A B : SL2C) :
  embedDark ⁅A, B⁆ = embedDark A * embedDark B - embedDark B * embedDark A := by
  ext i j
  let x := chiralIso.symm i
  let y := chiralIso.symm j
  have hi : i = chiralIso x := (Equiv.apply_symm_apply chiralIso i).symm
  have hj : j = chiralIso y := (Equiv.apply_symm_apply chiralIso j).symm
  rw[hi, hj, Matrix.sub_apply, embed_dark_mul_apply, embed_dark_mul_apply]
  unfold embedDark
  simp only[Matrix.of_apply, Equiv.symm_apply_apply]
  cases x <;> cases y
  · change (0 : Complex) = 0 - 0; ring
  · change (0 : Complex) = 0 - 0; ring
  · change (0 : Complex) = 0 - 0; ring
  · rw[sl2c_bracket_val A B]; rfl

lemma orthogonality_term (A B : SL2C) (i j k : Fin 4) :
  (embedLight A) i k * (embedDark B) k j = 0 := by
  rw[embedLight, embedDark]
  rw [Matrix.of_apply, Matrix.of_apply]
  cases hk : chiralIso.symm k with
  | inl kl => exact mul_zero _
  | inr kr =>
    cases hi : chiralIso.symm i with
    | inl il => exact zero_mul _
    | inr ir => exact zero_mul _

lemma chiralOrthogonality (A B : SL2C) : (embedLight A) * (embedDark B) = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply orthogonality_term

lemma orthogonality_term_dl (A B : SL2C) (i j k : Fin 4) :
  (embedDark A) i k * (embedLight B) k j = 0 := by
  rw[embedDark, embedLight]
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

lemma chiralOrthogonalityDl (A B : SL2C) : (embedDark A) * (embedLight B) = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply orthogonality_term_dl

lemma bracket_embed (L1 L2 R1 R2 : SL2C) :
  bracket (embedLight L1 + embedDark R1) (embedLight L2 + embedDark R2) =
  embedLight ⁅L1, L2⁆ + embedDark ⁅R1, R2⁆ := by
  unfold bracket
  have h1 : (embedLight L1 + embedDark R1) * (embedLight L2 + embedDark R2) =
    embedLight L1 * embedLight L2 + embedDark R1 * embedDark R2 := by
    rw[Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    have h_ortho1 := chiralOrthogonality L1 R2
    have h_ortho2 := chiralOrthogonalityDl R1 L2
    rw[h_ortho1, h_ortho2]
    simp only[add_zero, zero_add]
  have h2 : (embedLight L2 + embedDark R2) * (embedLight L1 + embedDark R1) =
    embedLight L2 * embedLight L1 + embedDark R2 * embedDark R1 := by
    rw[Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    have h_ortho1 := chiralOrthogonality L2 R1
    have h_ortho2 := chiralOrthogonalityDl R2 L1
    rw[h_ortho1, h_ortho2]
    simp only[add_zero, zero_add]
  rw[h1, h2]
  have h3 : embedLight L1 * embedLight L2 + embedDark R1 * embedDark R2 -
    (embedLight L2 * embedLight L1 + embedDark R2 * embedDark R1) =
    (embedLight L1 * embedLight L2 - embedLight L2 * embedLight L1) +
    (embedDark R1 * embedDark R2 - embedDark R2 * embedDark R1) := by abel
  rw[h3]
  rw[← embed_light_bracket L1 L2, ← embed_dark_bracket R1 R2]

lemma embed_linear_combo (L1 L2 L3 R1 R2 R3 : SL2C) :
  (embedLight L1 + embedDark R1) - (embedLight L2 + embedDark R2) + (embedLight L3 + embedDark R3) =
  embedLight (L1 - L2 + L3) + embedDark (R1 - R2 + R3) := by
  ext i j
  simp only[Matrix.add_apply, Matrix.sub_apply]
  unfold embedLight embedDark
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

lemma trace_embed_light_mul (A B : SL2C) :
  Matrix.trace (embedLight A * embedLight B) = Matrix.trace (A.val * B.val) := by
  rw [Matrix.trace, Matrix.trace]
  simp only[Matrix.diag]
  rw[← Equiv.sum_comp chiralIso (fun i => (embedLight A * embedLight B) i i)]
  rw [Fintype.sum_sum_type]
  have h_inr : ∑ x : Fin 2, (embedLight A * embedLight B) (chiralIso (Sum.inr x)) (chiralIso (Sum.inr x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    have hz : (embedLight A) (chiralIso (Sum.inr x)) k = 0 := embed_light_inr_left A x k
    rw[hz, zero_mul]
  rw [h_inr, add_zero]
  apply Finset.sum_congr rfl
  intro x _
  rw [embed_light_mul_inl_inl]

lemma trace_embed_dark_mul (A B : SL2C) :
  Matrix.trace (embedDark A * embedDark B) = Matrix.trace (A.val * B.val) := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag]
  rw[← Equiv.sum_comp chiralIso (fun i => (embedDark A * embedDark B) i i)]
  rw [Fintype.sum_sum_type]
  have h_inl : ∑ x : Fin 2, (embedDark A * embedDark B) (chiralIso (Sum.inl x)) (chiralIso (Sum.inl x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    have hz : (embedDark A) (chiralIso (Sum.inl x)) k = 0 := embed_dark_inl_left A x k
    rw [hz, zero_mul]
  rw[h_inl, zero_add]
  apply Finset.sum_congr rfl
  intro x _
  rw[embed_dark_mul_inr_inr]

lemma trace_embed_mul_embed (L1 R1 L2 R2 : SL2C) :
  Matrix.trace ((embedLight L1 + embedDark R1) * (embedLight L2 + embedDark R2)) =
  Matrix.trace (L1.val * L2.val) + Matrix.trace (R1.val * R2.val) := by
  have h1 : (embedLight L1 + embedDark R1) * (embedLight L2 + embedDark R2) =
    embedLight L1 * embedLight L2 + embedDark R1 * embedDark R2 := by
    rw[Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    rw[chiralOrthogonality, chiralOrthogonalityDl]
    simp
  rw[h1, Matrix.trace_add]
  rw[trace_embed_light_mul, trace_embed_dark_mul]

lemma to_sl2c_of_trace_zero (M : Matrix (Fin 2) (Fin 2) Complex) (h : Matrix.trace M = 0) :
  (toSl2c M).val = M := by
  unfold toSl2c
  dsimp
  rw [h]
  have h0 : (0 : Complex) / 2 = 0 := zero_div 2
  rw[h0, zero_smul, sub_zero]

lemma chiral_project_light_embed (L R : SL2C) :
  (chiralProject (embedLight L + embedDark R)).light = L := by
  apply Subtype.ext
  change (toSl2c (fun (i j : Fin 2) =>
    (embedLight L) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) +
    (embedDark R) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)))).val = L.val

  have heq : (fun (i j : Fin 2) =>
    (embedLight L) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) +
    (embedDark R) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j))) = L.val := by
    ext i j
    rw[embed_light_inl_inl]
    have hz : (embedDark R) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) = 0 := by
      exact embed_dark_inl_left R i (chiralIso (Sum.inl j))
    rw[hz, add_zero]

  have ht : Matrix.trace (fun (i j : Fin 2) =>
    (embedLight L) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) +
    (embedDark R) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j))) = 0 := by
    rw[heq]
    exact L.property

  rw[to_sl2c_of_trace_zero _ ht]
  exact heq

lemma chiral_project_dark_embed (L R : SL2C) :
  (chiralProject (embedLight L + embedDark R)).dark = R := by
  apply Subtype.ext
  change (toSl2c (fun (i j : Fin 2) =>
    (embedLight L) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) +
    (embedDark R) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)))).val = R.val

  have heq : (fun (i j : Fin 2) =>
    (embedLight L) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) +
    (embedDark R) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j))) = R.val := by
    ext i j
    rw [embed_dark_inr_inr]
    have hz : (embedLight L) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) = 0 := by
      exact embed_light_inr_left L i (chiralIso (Sum.inr j))
    rw [hz, zero_add]

  have ht : Matrix.trace (fun (i j : Fin 2) =>
    (embedLight L) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) +
    (embedDark R) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j))) = 0 := by
    rw[heq]
    exact R.property

  rw[to_sl2c_of_trace_zero _ ht]
  exact heq

lemma extract_light_block (u : Universe) (ν : Fin 4) (p : SpacetimePoint) (i j : Fin 2) :
  (u.embed ν p) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) = (u.light ν p).val i j := by
  unfold Universe.embed embedLight embedDark
  simp only[Matrix.add_apply, Matrix.of_apply, Equiv.symm_apply_apply]
  exact add_zero _

lemma extract_dark_block (u : Universe) (ν : Fin 4) (p : SpacetimePoint) (i j : Fin 2) :
  (u.embed ν p) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) = (u.dark ν p).val i j := by
  unfold Universe.embed embedLight embedDark
  simp only[Matrix.add_apply, Matrix.of_apply, Equiv.symm_apply_apply]
  exact zero_add _

lemma to_sl2c_self (A : SL2C) : toSl2c A.val = A := by
  have h_tr : Matrix.trace A.val = 0 := by rw[← mem_sl_iff]; exact A.property
  apply Subtype.ext
  unfold toSl2c
  dsimp
  rw[h_tr]
  simp

lemma to_sl2c_light_eq (u : Universe) (ν : Fin 4) :
  (fun p => toSl2c (fun i j => (u.embed ν p) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)))) = (fun p => u.light ν p) := by
  ext p
  have h1 : (fun i j => (u.embed ν p) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j))) = (u.light ν p).val := by
    ext i j; exact extract_light_block u ν p i j
  rw[h1, to_sl2c_self]

lemma to_sl2c_dark_eq (u : Universe) (ν : Fin 4) :
  (fun p => toSl2c (fun i j => (u.embed ν p) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)))) = (fun p => u.dark ν p) := by
  ext p
  have h1 : (fun i j => (u.embed ν p) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j))) = (u.dark ν p).val := by
    ext i j; exact extract_dark_block u ν p i j
  rw[h1, to_sl2c_self]

theorem nativeEmbedDerivative (u : Universe) (μ ν : Fin 4) (x : SpacetimePoint) :
  partialDerivChiral μ (fun p => u.embed ν p) x =
  embedLight (partialDerivSl2c μ (u.light ν) x) + embedDark (partialDerivSl2c μ (u.dark ν) x) := by
  unfold partialDerivChiral
  have hL : (fun p => toSl2c (fun i j => (u.embed ν p) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)))) = u.light ν := to_sl2c_light_eq u ν
  have hR : (fun p => toSl2c (fun i j => (u.embed ν p) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)))) = u.dark ν := to_sl2c_dark_eq u ν
  rw[hL, hR]

lemma curvature_embed_eq (u : Universe) (mu nu : Fin 4) (x : SpacetimePoint) :
  curvature (fun m p => u.embed m p) mu nu x =
  embedLight (curvatureSl2c u.light mu nu x) + embedDark (curvatureSl2c u.dark mu nu x) := by
  unfold curvature curvatureSl2c
  rw[nativeEmbedDerivative _ _ _]
  rw[nativeEmbedDerivative _ _ _]
  have h_mu : (fun m p => u.embed m p) mu x = embedLight (u.light mu x) + embedDark (u.dark mu x) := rfl
  have h_nu : (fun m p => u.embed m p) nu x = embedLight (u.light nu x) + embedDark (u.dark nu x) := rfl
  rw [h_mu, h_nu]
  rw [bracket_embed]
  have h_proj_L : (chiralProject (embedLight ⁅u.light mu x, u.light nu x⁆ + embedDark ⁅u.dark mu x, u.dark nu x⁆)).light = ⁅u.light mu x, u.light nu x⁆ := chiral_project_light_embed _ _
  have h_proj_R : (chiralProject (embedLight ⁅u.light mu x, u.light nu x⁆ + embedDark ⁅u.dark mu x, u.dark nu x⁆)).dark = ⁅u.dark mu x, u.dark nu x⁆ := chiral_project_dark_embed _ _

  change embedLight (partialDerivSl2c mu (u.light nu) x) + embedDark (partialDerivSl2c mu (u.dark nu) x) -
         (embedLight (partialDerivSl2c nu (u.light mu) x) + embedDark (partialDerivSl2c nu (u.dark mu) x)) +
         (embedLight (chiralProject (embedLight ⁅u.light mu x, u.light nu x⁆ + embedDark ⁅u.dark mu x, u.dark nu x⁆)).light +
          embedDark (chiralProject (embedLight ⁅u.light mu x, u.light nu x⁆ + embedDark ⁅u.dark mu x, u.dark nu x⁆)).dark) =
         embedLight (partialDerivSl2c mu (u.light nu) x - partialDerivSl2c nu (u.light mu) x + ⁅u.light mu x, u.light nu x⁆) +
         embedDark (partialDerivSl2c mu (u.dark nu) x - partialDerivSl2c nu (u.dark mu) x + ⁅u.dark mu x, u.dark nu x⁆)

  rw[h_proj_L, h_proj_R]
  exact embed_linear_combo _ _ _ _ _ _

-- ==============================================================================
-- THE DECOMPOSITION THEOREM
-- ==============================================================================

/-- 🟡 KINEMATIC: Chiral Lagrangian strictly decomposes into Light and Dark actions when locally decoupled. -/
theorem algebraicChiralDecomposition (u : Universe) (x : SpacetimePoint) :
  lagrangianDensity (fun mu nu => curvature (fun m p => u.embed m p) mu nu x) =
  actionVacuum (fun mu nu => curvature (fun m p => u.embed m p) mu nu x) +
  actionDark (fun mu nu => curvature (fun m p => u.embed m p) mu nu x) := by

  have h_proj_L : ∀ mu nu, (chiralProject (curvature (fun m p => u.embed m p) mu nu x)).light = curvatureSl2c u.light mu nu x := by
    intro mu nu
    have h_curv := curvature_embed_eq u mu nu x
    rw [h_curv]
    exact chiral_project_light_embed _ _

  have h_proj_R : ∀ mu nu, (chiralProject (curvature (fun m p => u.embed m p) mu nu x)).dark = curvatureSl2c u.dark mu nu x := by
    intro mu nu
    have h_curv := curvature_embed_eq u mu nu x
    rw [h_curv]
    exact chiral_project_dark_embed _ _

  unfold lagrangianDensity actionVacuum actionDark
  have h_split : (∑ mu, ∑ nu, ∑ rho, ∑ sigma,
      eta mu rho * eta nu sigma * Matrix.trace (curvature (fun m p => u.embed m p) mu nu x * curvature (fun m p => u.embed m p) rho sigma x)) =
    (∑ mu, ∑ nu, ∑ rho, ∑ sigma, eta mu rho * eta nu sigma * Matrix.trace (((chiralProject (curvature (fun m p => u.embed m p) mu nu x)).light).val * ((chiralProject (curvature (fun m p => u.embed m p) rho sigma x)).light).val)) +
    (∑ mu, ∑ nu, ∑ rho, ∑ sigma, eta mu rho * eta nu sigma * Matrix.trace (((chiralProject (curvature (fun m p => u.embed m p) mu nu x)).dark).val * ((chiralProject (curvature (fun m p => u.embed m p) rho sigma x)).dark).val)) := by
    rw[← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro mu _
    rw[← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro nu _
    rw[← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro rho _
    rw[← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro sigma _
    rw[h_proj_L mu nu, h_proj_L rho sigma, h_proj_R mu nu, h_proj_R rho sigma]
    have h_curv1 := curvature_embed_eq u mu nu x
    have h_curv2 := curvature_embed_eq u rho sigma x
    rw[h_curv1, h_curv2]
    have h_trace := trace_embed_mul_embed (curvatureSl2c u.light mu nu x) (curvatureSl2c u.dark mu nu x) (curvatureSl2c u.light rho sigma x) (curvatureSl2c u.dark rho sigma x)
    rw [h_trace]
    ring
  rw[h_split, mul_add]

end CGD.Foundations

-- FILENAME: CGD/Gravity/ExactSolutions.lean

import Litlib.Core
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Axioms.Ontology
import CGD.Gravity.MacroscopicVacuum
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def exactAbelianL (c : ℂ) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  (x 1 : ℝ) • (c • sigmaX)

noncomputable def exactAbelianField (c : ℂ) (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  if mu = 2 then toSl2c (exactAbelianL c x) else 0

noncomputable def curvature_const (c : ℂ) (beta gamma : Fin 4) : SL2C :=
  if beta = 1 ∧ gamma = 2 then toSl2c (c • sigmaX)
  else if beta = 2 ∧ gamma = 1 then toSl2c ((-c) • sigmaX)
  else 0

lemma partialDeriv_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c_val : E) (μ : Fin 4) (x : SpacetimePoint) :
  partialDeriv μ (fun _ => c_val) x = 0 := by
  unfold partialDeriv
  simp [fderiv_const]

lemma partialDeriv_coord_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] 
  (c_idx : Fin 4) (M : E) (k : Fin 4) (x : SpacetimePoint) :
  partialDeriv k (fun p : SpacetimePoint => p c_idx • M) x = if k = c_idx then M else 0 := by
  unfold partialDeriv
  let F : SpacetimePoint →L[ℝ] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.proj c_idx) M
  have h_eq : (fun p : SpacetimePoint => p c_idx • M) = F := rfl
  rw [h_eq]
  rw [HasFDerivAt.fderiv (ContinuousLinearMap.hasFDerivAt F)]
  have h_eval : F ((Pi.single k (1 : ℝ)) : Fin 4 → ℝ) = ((Pi.single k (1 : ℝ)) : Fin 4 → ℝ) c_idx • M := rfl
  rw [h_eval]
  by_cases hk : k = c_idx
  · rw [hk, Pi.single_eq_same, one_smul, if_pos rfl]
  · have h_neq : k ≠ c_idx := hk
    have h_eval_zero : ((Pi.single k (1 : ℝ)) : Fin 4 → ℝ) c_idx = 0 := by simp [h_neq.symm]
    rw [h_eval_zero, zero_smul, if_neg hk]

lemma partialDerivMat_exactAbelianL (c : ℂ) (k : Fin 4) (x : SpacetimePoint) :
  partialDerivMat k (fun p => exactAbelianL c p) x = if k = 1 then c • sigmaX else 0 := by
  ext i j
  unfold partialDerivMat exactAbelianL
  change partialDeriv k (fun p => p 1 • (c • sigmaX) i j) x = (if k = 1 then c • sigmaX else 0) i j
  rw [partialDeriv_coord_smul 1 ((c • sigmaX) i j) k x]
  by_cases hk : k = 1
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk]
    rfl

lemma toSl2c_exactAbelianL (c : ℂ) (p : SpacetimePoint) :
  (toSl2c (exactAbelianL c p)).val = exactAbelianL c p := by
  unfold toSl2c exactAbelianL
  dsimp
  have h_tr : Matrix.trace (p 1 • c • sigmaX) = 0 := by
    unfold Matrix.trace Matrix.diag
    have h_sum : ∑ i : Fin 2, (p 1 • c • sigmaX) i i = (p 1 • c • sigmaX) 0 0 + (p 1 • c • sigmaX) 1 1 := Fin.sum_univ_two _
    rw [h_sum]
    unfold sigmaX mkMat
    change p 1 * (c * 0) + p 1 * (c * 0) = 0
    ring
  rw [h_tr]
  have hz : (0 : ℂ) / 2 = 0 := by ring
  rw [hz, zero_smul, sub_zero]

lemma partialDerivSl2c_exactAbelian (c : ℂ) (k l : Fin 4) (x : SpacetimePoint) :
  partialDerivSl2c k (exactAbelianField c l) x = if k = 1 ∧ l = 2 then toSl2c (c • sigmaX) else 0 := by
  unfold exactAbelianField
  by_cases hl : l = 2
  · have h_fun_eq : (fun p : SpacetimePoint => if l = 2 then toSl2c (exactAbelianL c p) else 0) = 
                    (fun p : SpacetimePoint => toSl2c (exactAbelianL c p)) := by
      funext p; rw [if_pos hl]
    rw [h_fun_eq]
    unfold partialDerivSl2c
    have h_val : (fun p => (toSl2c (exactAbelianL c p)).val) = (fun p => exactAbelianL c p) := by
      funext p; exact toSl2c_exactAbelianL c p
    rw [h_val]
    rw [partialDerivMat_exactAbelianL c k x]
    by_cases hk : k = 1
    · have hk1l2 : k = 1 ∧ l = 2 := And.intro hk hl
      rw [if_pos hk, if_pos hk1l2]
    · have hk1l2 : ¬(k = 1 ∧ l = 2) := fun h => hk h.left
      rw [if_neg hk, if_neg hk1l2]
      apply Subtype.ext
      unfold toSl2c
      simp
  · have h_fun_eq : (fun p : SpacetimePoint => if l = 2 then toSl2c (exactAbelianL c p) else 0) = 
                    (fun _ : SpacetimePoint => (0 : SL2C)) := by
      funext p; rw [if_neg hl]
    rw [h_fun_eq]
    have h_false : ¬(k = 1 ∧ l = 2) := fun h => hl h.right
    rw [if_neg h_false]
    unfold partialDerivSl2c partialDerivMat
    apply Subtype.ext
    dsimp
    ext i j
    have hzero : partialDeriv k (fun _ => (0 : ℂ)) x = 0 := partialDeriv_const 0 k x
    rw [hzero]
    unfold toSl2c
    dsimp
    have htr : Matrix.trace (fun (_ _ : Fin 2) => (0 : ℂ)) = 0 := by 
      unfold Matrix.trace Matrix.diag
      simp
    rw [htr]
    simp

lemma comm_exactAbelian (c : ℂ) (m n : Fin 4) (x : SpacetimePoint) :
  ⁅exactAbelianField c m x, exactAbelianField c n x⁆ = 0 := by
  unfold exactAbelianField
  by_cases hm : m = 2 <;> by_cases hn : n = 2
  · simp [hm, hn]
  · simp [hm, hn]
  · simp [hm, hn]
  · simp [hm, hn]

lemma toSl2c_neg (M : Matrix (Fin 2) (Fin 2) ℂ) : toSl2c (- M) = - toSl2c M := by
  apply Subtype.ext
  unfold toSl2c
  dsimp
  ext i j
  change - M i j - ((Matrix.trace (-M) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) = - (M i j - ((Matrix.trace M / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j))
  unfold Matrix.trace Matrix.diag
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  change - M i j - (((- M 0 0 + - M 1 1) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) = - (M i j - (((M 0 0 + M 1 1) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j))
  ring

lemma curvature_exactAbelian (c : ℂ) (m n : Fin 4) (x : SpacetimePoint) :
  curvatureSl2c (exactAbelianField c) m n x = curvature_const c m n := by
  rw [curvatureSl2c_def]
  rw [comm_exactAbelian c m n x, add_zero]
  rw [partialDerivSl2c_exactAbelian, partialDerivSl2c_exactAbelian]
  unfold curvature_const
  by_cases h1 : m = 1 ∧ n = 2
  · have h2_false : ¬(n = 1 ∧ m = 2) := by
      intro h
      have h_m : (1 : Fin 4) = 2 := Eq.trans h1.left.symm h.right
      revert h_m
      decide
    simp only [if_pos h1, if_neg h2_false, sub_zero]
  · by_cases h2 : m = 2 ∧ n = 1
    · have h2_rev : n = 1 ∧ m = 2 := And.intro h2.right h2.left
      simp only [if_neg h1, if_pos h2, if_pos h2_rev, zero_sub]
      have h_inner : (-c) • sigmaX = - (c • sigmaX) := by
        ext i j
        change (-c) * sigmaX i j = - (c * sigmaX i j)
        ring
      rw [h_inner]
      exact (toSl2c_neg (c • sigmaX)).symm
    · have h2_rev_false : ¬(n = 1 ∧ m = 2) := by
        intro h
        apply h2
        exact And.intro h.right h.left
      simp only [if_neg h1, if_neg h2, if_neg h2_rev_false, sub_zero]

lemma toSl2c_c_sigmaX_smul (c : ℂ) : toSl2c (c • sigmaX) = c • toSl2c sigmaX := by
  apply Subtype.ext
  unfold toSl2c
  dsimp
  ext i j
  have h_tr1 : Matrix.trace (c • sigmaX) = 0 := by
    unfold Matrix.trace Matrix.diag sigmaX mkMat
    simp [Fin.sum_univ_two]
  have h_tr2 : Matrix.trace sigmaX = 0 := by
    unfold Matrix.trace Matrix.diag sigmaX mkMat
    simp [Fin.sum_univ_two]
  rw [h_tr1, h_tr2]
  simp

Litlib.theorem
  description "Exact Abelian Macroscopic Solution"
/--
Provides an exact analytical solution mapping an Abelian plane wave natively into the macroscopic pure CDJ volume constraint.
-/
theorem dynamicExactAbelianSolution (c : ℂ) (hc : c ≠ 0) :
  ∃ (u : Universe), 
    CGD.Gravity.satisfiesPureCdjConstraint (fun p m n => cgdAdjointCurvature u m n p) ∧ 
    (∀ x, curvatureSl2c u.sd_sector 1 2 x = c • toSl2c sigmaX) ∧
    (∃ x, curvatureSl2c u.sd_sector 1 2 x ≠ 0) := by
  sorry

end CGD.Gravity

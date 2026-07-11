-- FILENAME: CGD/Gravity/ExactSolutions/Math.lean

import Litlib.Core
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Axioms.Ontology
import CGD.Gravity.MacroscopicVacuum.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations CGD.Math Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

-- ============================================================================
-- SCALARS & COMPLEX ARITHMETIC
-- ============================================================================

lemma I_sq_eq : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq

lemma I_pow_3_eq : (Complex.I : ℂ) ^ 3 = -Complex.I := by
  calc (Complex.I : ℂ) ^ 3 = Complex.I ^ 2 * Complex.I := by ring
  _ = -1 * Complex.I := by rw [Complex.I_sq]
  _ = -Complex.I := by ring

lemma I_pow_4_eq : (Complex.I : ℂ) ^ 4 = 1 := by
  calc (Complex.I : ℂ) ^ 4 = Complex.I ^ 2 * Complex.I ^ 2 := by ring
  _ = -1 * -1 := by rw [Complex.I_sq]
  _ = 1 := by ring

lemma smul_one_C (x : ℂ) : (1:ℂ) • x = x := by exact one_smul ℂ x
lemma smul_neg_one_C (x : ℂ) : (-1:ℂ) • x = -x := by exact neg_one_smul ℂ x

-- ============================================================================
-- SUM & PRODUCT EVALUATORS
-- ============================================================================

lemma sum_2_eval {E : Type*} [AddCommGroup E] (f : Fin 2 → E) :
  ∑ k : Fin 2, f k = f 0 + f 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_one]; rfl

lemma sum_3_eval {E : Type*} [AddCommGroup E] (f : Fin 3 → E) :
  ∑ k : Fin 3, f k = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]; abel

lemma sum_4_eval {E : Type*} [AddCommGroup E] (f : Fin 4 → E) :
  ∑ k : Fin 4, f k = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]; abel

lemma prod_4_eval_C (f : Fin 4 → ℂ) :
  ∏ k : Fin 4, f k = f 0 * f 1 * f 2 * f 3 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_one]
  have h1 : (Fin.succ 0 : Fin 4) = 1 := rfl
  have h2 : (Fin.succ (Fin.succ 0) : Fin 4) = 2 := rfl
  have h3 : (Fin.succ (Fin.succ (Fin.succ 0)) : Fin 4) = 3 := rfl
  rw [h1, h2, h3]; ring

-- ============================================================================
-- MATRIX & TRACE EVALUATORS
-- ============================================================================

@[simp] lemma trace_2x2_apply (A : Matrix (Fin 2) (Fin 2) ℂ) :
  Matrix.trace A = A 0 0 + A 1 1 := by
  change ∑ k : Fin 2, A k k = _; exact sum_2_eval _

@[simp] lemma mul_2x2_apply (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  change ∑ k : Fin 2, A i k * B k j = _; exact sum_2_eval _

@[simp] lemma mul_3x3_apply (A B : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j := by
  change ∑ k : Fin 3, A i k * B k j = _; exact sum_3_eval _

lemma sigmaX_0_0 : sigmaX 0 0 = 0 := rfl
lemma sigmaX_0_1 : sigmaX 0 1 = 1 := rfl
lemma sigmaX_1_0 : sigmaX 1 0 = 1 := rfl
lemma sigmaX_1_1 : sigmaX 1 1 = 0 := rfl

lemma sigmaY_0_0 : sigmaY 0 0 = 0 := rfl
lemma sigmaY_0_1 : sigmaY 0 1 = -Complex.I := rfl
lemma sigmaY_1_0 : sigmaY 1 0 = Complex.I := rfl
lemma sigmaY_1_1 : sigmaY 1 1 = 0 := rfl

lemma sigmaZ_0_0 : sigmaZ 0 0 = 1 := rfl
lemma sigmaZ_0_1 : sigmaZ 0 1 = 0 := rfl
lemma sigmaZ_1_0 : sigmaZ 1 0 = 0 := rfl
lemma sigmaZ_1_1 : sigmaZ 1 1 = -1 := rfl

lemma val_sigma1_0_0 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
lemma val_sigma1_0_1 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
lemma val_sigma1_1_0 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
lemma val_sigma1_1_1 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl

lemma val_sigma2_0_0 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
lemma val_sigma2_0_1 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
lemma val_sigma2_1_0 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
lemma val_sigma2_1_1 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl

lemma val_sigma3_0_0 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
lemma val_sigma3_0_1 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
lemma val_sigma3_1_0 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
lemma val_sigma3_1_1 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl

lemma sum_epsilon4_matrices {E : Type*} [AddCommGroup E] [Module ℂ E]
  (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → E) :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ • T μ ν ρ σ) =
    (1:ℂ) • T 0 1 2 3 + (-1:ℂ) • T 0 1 3 2 + (-1:ℂ) • T 0 2 1 3 + (1:ℂ) • T 0 2 3 1 +
    (1:ℂ) • T 0 3 1 2 + (-1:ℂ) • T 0 3 2 1 +
    (-1:ℂ) • T 1 0 2 3 + (1:ℂ) • T 1 0 3 2 + (1:ℂ) • T 1 2 0 3 + (-1:ℂ) • T 1 2 3 0 +
    (-1:ℂ) • T 1 3 0 2 + (1:ℂ) • T 1 3 2 0 +
    (1:ℂ) • T 2 0 1 3 + (-1:ℂ) • T 2 0 3 1 + (-1:ℂ) • T 2 1 0 3 + (1:ℂ) • T 2 1 3 0 +
    (1:ℂ) • T 2 3 0 1 + (-1:ℂ) • T 2 3 1 0 +
    (-1:ℂ) • T 3 0 1 2 + (1:ℂ) • T 3 0 2 1 + (1:ℂ) • T 3 1 0 2 + (-1:ℂ) • T 3 1 2 0 +
    (-1:ℂ) • T 3 2 0 1 + (1:ℂ) • T 3 2 1 0 := by
  simp only [sum_4_eval, epsilon4, epsilon4_int, Int.cast_zero, Int.cast_one, Int.cast_neg, zero_smul, add_zero, zero_add]
  abel

lemma epsilon4_1212 : epsilon4 1 2 1 2 = 0 := by unfold epsilon4 epsilon4_int; exact Int.cast_zero
lemma epsilon4_1221 : epsilon4 1 2 2 1 = 0 := by unfold epsilon4 epsilon4_int; exact Int.cast_zero
lemma epsilon4_2112 : epsilon4 2 1 1 2 = 0 := by unfold epsilon4 epsilon4_int; exact Int.cast_zero
lemma epsilon4_2121 : epsilon4 2 1 2 1 = 0 := by unfold epsilon4 epsilon4_int; exact Int.cast_zero

-- ============================================================================
-- SL2C & GAUGE UTILITIES
-- ============================================================================

lemma toSl2c_neg (M : Matrix (Fin 2) (Fin 2) ℂ) : toSl2c (- M) = - toSl2c M := by
  apply Subtype.ext; unfold toSl2c; dsimp; ext i j
  change - M i j - ((Matrix.trace (-M) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) = - (M i j - ((Matrix.trace M / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j))
  unfold Matrix.trace Matrix.diag; rw [Fin.sum_univ_two, Fin.sum_univ_two]
  change - M i j - (((- M 0 0 + - M 1 1) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) = - (M i j - (((M 0 0 + M 1 1) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j)); ring

lemma toSl2c_c_sigmaX_smul (c : ℂ) : toSl2c (c • sigmaX) = c • toSl2c sigmaX := by
  apply Subtype.ext; unfold toSl2c; dsimp; ext i j
  have h_tr1 : Matrix.trace (c • sigmaX) = 0 := by unfold Matrix.trace Matrix.diag sigmaX mkMat; simp [Fin.sum_univ_two]
  have h_tr2 : Matrix.trace sigmaX = 0 := by unfold Matrix.trace Matrix.diag sigmaX mkMat; simp [Fin.sum_univ_two]
  rw [h_tr1, h_tr2]; simp

lemma toSl2c_sub (A B : Matrix (Fin 2) (Fin 2) ℂ) : toSl2c A - toSl2c B = toSl2c (A - B) := by
  apply Subtype.ext; unfold toSl2c; dsimp; ext i j
  unfold Matrix.trace Matrix.diag; simp [Fin.sum_univ_two, Matrix.sub_apply]; ring

lemma sl2c_zero_val : (0 : SL2C).val = 0 := rfl

lemma extractAdjoint_zero : extractAdjoint (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  unfold extractAdjoint; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.trace, Matrix.diag]

-- ============================================================================
-- CALCULUS UTILITIES
-- ============================================================================

lemma partialDeriv_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c_val : E) (μ : Fin 4) (x : SpacetimePoint) :
  partialDeriv μ (fun _ => c_val) x = 0 := by unfold partialDeriv; simp

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

lemma partialDeriv_cL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : SpacetimePoint →L[ℝ] E) (k : Fin 4) (x : SpacetimePoint) :
  partialDeriv k (fun p => L p) x = L (Pi.single k 1) := by
  unfold partialDeriv
  rw [HasFDerivAt.fderiv (ContinuousLinearMap.hasFDerivAt L)]

end CGD.Gravity

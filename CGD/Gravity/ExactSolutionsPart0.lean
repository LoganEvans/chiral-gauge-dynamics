-- FILENAME: CGD/Gravity/ExactSolutionsPart0.lean

import CGD.Gravity.ExactSolutionsPart24

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

-- ============================================================================
-- SHARED COMPLEX POWERS & SCALARS
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
-- PAULI TRACE EVALUATORS
-- ============================================================================

lemma sum_2_eval {E : Type*} [AddCommGroup E] (f : Fin 2 → E) :
  ∑ k : Fin 2, f k = f 0 + f 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_one]; rfl

lemma trace_2x2_apply (A : Matrix (Fin 2) (Fin 2) ℂ) :
  Matrix.trace A = A 0 0 + A 1 1 := by
  change ∑ k : Fin 2, A k k = _; rw [sum_2_eval]

lemma mul_2x2_apply (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  change ∑ k : Fin 2, A i k * B k j = _; rw [sum_2_eval]

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

-- ============================================================================
-- THE MAP BRIDGES (Isolates unifier logic)
-- ============================================================================

noncomputable def F_val_map (m n : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  match m, n with
  | 0, 1 => -sigmaX
  | 0, 2 => -sigmaY
  | 0, 3 => -sigmaZ
  | 1, 0 => sigmaX
  | 1, 2 => Complex.I • sigmaZ
  | 1, 3 => -Complex.I • sigmaY
  | 2, 0 => sigmaY
  | 2, 1 => -Complex.I • sigmaZ
  | 2, 3 => Complex.I • sigmaX
  | 3, 0 => sigmaZ
  | 3, 1 => Complex.I • sigmaY
  | 3, 2 => -Complex.I • sigmaX
  | _, _ => 0

lemma F_origin_val_eq_map (m n : Fin 4) : F_origin_val m n = F_val_map m n := by
  fin_cases m <;> fin_cases n <;> { unfold F_origin_val F_val_map; simp }

noncomputable def extAdj_map (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 3) : ℂ :=
  match i, j with
  | 0, 1 => (1 / 2 : ℂ) * Matrix.trace (M * sigma3.val)
  | 0, 2 => -((1 / 2 : ℂ) * Matrix.trace (M * sigma2.val))
  | 1, 0 => -((1 / 2 : ℂ) * Matrix.trace (M * sigma3.val))
  | 1, 2 => (1 / 2 : ℂ) * Matrix.trace (M * sigma1.val)
  | 2, 0 => (1 / 2 : ℂ) * Matrix.trace (M * sigma2.val)
  | 2, 1 => -((1 / 2 : ℂ) * Matrix.trace (M * sigma1.val))
  | _, _ => 0

lemma extractAdjoint_eq_map (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 3) : extractAdjoint M i j = extAdj_map M i j := by
  fin_cases i <;> fin_cases j <;> { unfold extractAdjoint extAdj_map; simp }

-- ============================================================================
-- CENTRAL SCALAR LOOKUP TABLE FOR TRACES
-- ============================================================================

noncomputable def adj_F_val (m n : Fin 4) (i j : Fin 3) : ℂ :=
  match m, n, i, j with
  | 0, 1, 1, 2 => -1
  | 0, 1, 2, 1 => 1
  | 0, 2, 0, 2 => 1
  | 0, 2, 2, 0 => -1
  | 0, 3, 0, 1 => -1
  | 0, 3, 1, 0 => 1
  | 1, 0, 1, 2 => 1
  | 1, 0, 2, 1 => -1
  | 2, 0, 0, 2 => -1
  | 2, 0, 2, 0 => 1
  | 3, 0, 0, 1 => 1
  | 3, 0, 1, 0 => -1
  | 1, 2, 0, 1 => Complex.I
  | 1, 2, 1, 0 => -Complex.I
  | 2, 1, 0, 1 => -Complex.I
  | 2, 1, 1, 0 => Complex.I
  | 1, 3, 0, 2 => Complex.I
  | 1, 3, 2, 0 => -Complex.I
  | 3, 1, 0, 2 => -Complex.I
  | 3, 1, 2, 0 => Complex.I
  | 2, 3, 1, 2 => Complex.I
  | 2, 3, 2, 1 => -Complex.I
  | 3, 2, 1, 2 => -Complex.I
  | 3, 2, 2, 1 => Complex.I
  | _, _, _, _ => 0

macro "prove_adj_f" : tactic =>
  `(tactic| (
    unfold adj_F
    simp only [extractAdjoint_eq_map, F_origin_val_eq_map]
    dsimp only [F_val_map, extAdj_map, adj_F_val]
    try simp only [
      trace_2x2_apply, mul_2x2_apply,
      val_sigma1_0_0, val_sigma1_0_1, val_sigma1_1_0, val_sigma1_1_1,
      val_sigma2_0_0, val_sigma2_0_1, val_sigma2_1_0, val_sigma2_1_1,
      val_sigma3_0_0, val_sigma3_0_1, val_sigma3_1_0, val_sigma3_1_1,
      sigmaX_0_0, sigmaX_0_1, sigmaX_1_0, sigmaX_1_1,
      sigmaY_0_0, sigmaY_0_1, sigmaY_1_0, sigmaY_1_1,
      sigmaZ_0_0, sigmaZ_0_1, sigmaZ_1_0, sigmaZ_1_1,
      Matrix.smul_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply,
      Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_ofNat,
      Int.cast_zero, Int.cast_one, Int.cast_neg,
      smul_eq_mul
    ]
    try ring_nf
    try simp only [Complex.I_sq, I_pow_3_eq, I_pow_4_eq]
    try ring
  ))

lemma adj_F_eq_val (m n : Fin 4) (i j : Fin 3) : adj_F m n i j = adj_F_val m n i j := by
  fin_cases m <;> fin_cases n <;> fin_cases i <;> fin_cases j <;> prove_adj_f

end CGD.Gravity

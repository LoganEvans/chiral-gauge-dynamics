-- FILENAME: CGD/Gravity/ExactSolutionsPart26_2.lean

import CGD.Gravity.ExactSolutionsPart26_1
import CGD.Gravity.ExactSolutionsPart0

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

-- ============================================================================
-- THE MATHEMATICAL MIRROR: F_PROJ == ADJ_F
-- ============================================================================

lemma urb_F_origin_val (m n : Fin 4) : (urb_F_origin m n).val = F_origin_val m n :=
  toSl2c_val_eq _ (F_origin_val_trace m n)

lemma getPauli_0 : (getPauli 0).val = sigma1.val := rfl
lemma getPauli_1 : (getPauli 1).val = sigma2.val := rfl
lemma getPauli_2 : (getPauli 2).val = sigma3.val := rfl

lemma F_proj_0_eq (m n : Fin 4) : F_proj 0 m n = adj_F m n 1 2 := by
  unfold F_proj project adj_F extractAdjoint
  dsimp only
  have h_half : (0.5 : ℂ) = 1/2 := by norm_num
  rw [h_half]
  rw [urb_F_origin_val, getPauli_0]
  rfl

lemma F_proj_1_eq (m n : Fin 4) : F_proj 1 m n = adj_F m n 2 0 := by
  unfold F_proj project adj_F extractAdjoint
  dsimp only
  have h_half : (0.5 : ℂ) = 1/2 := by norm_num
  rw [h_half]
  rw [urb_F_origin_val, getPauli_1]
  rfl

lemma F_proj_2_eq (m n : Fin 4) : F_proj 2 m n = adj_F m n 0 1 := by
  unfold F_proj project adj_F extractAdjoint
  dsimp only
  have h_half : (0.5 : ℂ) = 1/2 := by norm_num
  rw [h_half]
  rw [urb_F_origin_val, getPauli_2]
  rfl

-- ============================================================================
-- THE MAP BRIDGES (Isolates unifier logic)
-- ============================================================================

noncomputable def F_proj_map (a : Fin 3) (m n : Fin 4) : ℂ :=
  match a with
  | 0 => adj_F_val m n 1 2
  | 1 => adj_F_val m n 2 0
  | 2 => adj_F_val m n 0 1

lemma F_proj_eval (a : Fin 3) (m n : Fin 4) : F_proj a m n = F_proj_map a m n := by
  fin_cases a
  · change F_proj 0 m n = adj_F_val m n 1 2
    rw [F_proj_0_eq, adj_F_eq_val]
  · change F_proj 1 m n = adj_F_val m n 2 0
    rw [F_proj_1_eq, adj_F_eq_val]
  · change F_proj 2 m n = adj_F_val m n 0 1
    rw [F_proj_2_eq, adj_F_eq_val]

-- ============================================================================
-- FAST URBANTKE CELL EVALUATOR
-- ============================================================================

macro "eval_urb_cell" : tactic =>
  `(tactic| (
    unfold urb_cell T_Urb
    simp only [
      F_proj_eval, F_proj_map, adj_F_val,
      zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub,
      Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_ofNat,
      Int.cast_zero, Int.cast_one, Int.cast_neg,
      smul_eq_mul
    ]
    try ring_nf
    try simp only [Complex.I_sq, I_pow_3_eq, I_pow_4_eq]
    try ring
  ))

lemma urb_cell_0_0 : urb_cell 0 0 = -12 := by eval_urb_cell
lemma urb_cell_0_1 : urb_cell 0 1 = 0 := by eval_urb_cell
lemma urb_cell_0_2 : urb_cell 0 2 = 0 := by eval_urb_cell
lemma urb_cell_0_3 : urb_cell 0 3 = 0 := by eval_urb_cell
lemma urb_cell_1_0 : urb_cell 1 0 = 0 := by eval_urb_cell
lemma urb_cell_1_1 : urb_cell 1 1 = 12 := by eval_urb_cell
lemma urb_cell_1_2 : urb_cell 1 2 = 0 := by eval_urb_cell
lemma urb_cell_1_3 : urb_cell 1 3 = 0 := by eval_urb_cell

end CGD.Gravity

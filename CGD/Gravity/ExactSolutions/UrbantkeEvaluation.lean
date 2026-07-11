-- FILENAME: CGD/Gravity/ExactSolutions/UrbantkeEvaluation.lean

import CGD.Gravity.ExactSolutions.LorentzianEval

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def urb_F_origin (m n : Fin 4) : SL2C := toSl2c (F_origin_val m n)

noncomputable def F_proj (a : Fin 3) (mu alpha : Fin 4) : ℂ :=
  project urb_F_origin a mu alpha

noncomputable def T_Urb (a b c : Fin 3) (mu nu : Fin 4) : ℂ :=
  (1:ℂ) * F_proj a mu 0 * F_proj b nu 1 * F_proj c 2 3 +
  (-1:ℂ) * F_proj a mu 0 * F_proj b nu 1 * F_proj c 3 2 +
  (-1:ℂ) * F_proj a mu 0 * F_proj b nu 2 * F_proj c 1 3 +
  (1:ℂ) * F_proj a mu 0 * F_proj b nu 2 * F_proj c 3 1 +
  (1:ℂ) * F_proj a mu 0 * F_proj b nu 3 * F_proj c 1 2 +
  (-1:ℂ) * F_proj a mu 0 * F_proj b nu 3 * F_proj c 2 1 +
  (-1:ℂ) * F_proj a mu 1 * F_proj b nu 0 * F_proj c 2 3 +
  (1:ℂ) * F_proj a mu 1 * F_proj b nu 0 * F_proj c 3 2 +
  (1:ℂ) * F_proj a mu 1 * F_proj b nu 2 * F_proj c 0 3 +
  (-1:ℂ) * F_proj a mu 1 * F_proj b nu 2 * F_proj c 3 0 +
  (-1:ℂ) * F_proj a mu 1 * F_proj b nu 3 * F_proj c 0 2 +
  (1:ℂ) * F_proj a mu 1 * F_proj b nu 3 * F_proj c 2 0 +
  (1:ℂ) * F_proj a mu 2 * F_proj b nu 0 * F_proj c 1 3 +
  (-1:ℂ) * F_proj a mu 2 * F_proj b nu 0 * F_proj c 3 1 +
  (-1:ℂ) * F_proj a mu 2 * F_proj b nu 1 * F_proj c 0 3 +
  (1:ℂ) * F_proj a mu 2 * F_proj b nu 1 * F_proj c 3 0 +
  (1:ℂ) * F_proj a mu 2 * F_proj b nu 3 * F_proj c 0 1 +
  (-1:ℂ) * F_proj a mu 2 * F_proj b nu 3 * F_proj c 1 0 +
  (-1:ℂ) * F_proj a mu 3 * F_proj b nu 0 * F_proj c 1 2 +
  (1:ℂ) * F_proj a mu 3 * F_proj b nu 0 * F_proj c 2 1 +
  (1:ℂ) * F_proj a mu 3 * F_proj b nu 1 * F_proj c 0 2 +
  (-1:ℂ) * F_proj a mu 3 * F_proj b nu 1 * F_proj c 2 0 +
  (-1:ℂ) * F_proj a mu 3 * F_proj b nu 2 * F_proj c 0 1 +
  (1:ℂ) * F_proj a mu 3 * F_proj b nu 2 * F_proj c 1 0

noncomputable def urb_cell (mu nu : Fin 4) : ℂ :=
  (1:ℂ) * T_Urb 0 1 2 mu nu + (-1:ℂ) * T_Urb 0 2 1 mu nu + (-1:ℂ) * T_Urb 1 0 2 mu nu +
  (1:ℂ) * T_Urb 1 2 0 mu nu + (1:ℂ) * T_Urb 2 0 1 mu nu + (-1:ℂ) * T_Urb 2 1 0 mu nu

lemma urbantkeMetric_eq_cell (mu nu : Fin 4) :
  urbantkeMetric urb_F_origin mu nu = urb_cell mu nu := by
  unfold urbantkeMetric

  have h_inner : ∀ a b c : Fin 3, (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, (epsilon4 α β γ δ : ℂ) * project urb_F_origin a mu α * project urb_F_origin b nu β * project urb_F_origin c γ δ) = T_Urb a b c mu nu := by
    intro a b c
    unfold T_Urb F_proj
    simp only [sum_4_eval, epsilon4, epsilon4_int, Int.cast_zero, Int.cast_one, Int.cast_neg, zero_mul, one_mul, neg_mul, add_zero, zero_add]
    ring

  have h_outer : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (epsilon3 a b c : ℂ) * T_Urb a b c mu nu) = urb_cell mu nu := by
    unfold urb_cell
    simp only [sum_3_eval, epsilon3, epsilon3_int, Int.cast_zero, Int.cast_one, Int.cast_neg, zero_mul, one_mul, neg_mul, add_zero, zero_add]
    ring

  dsimp only
  change (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (epsilon3 a b c : ℂ) * (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, (epsilon4 α β γ δ : ℂ) * project urb_F_origin a mu α * project urb_F_origin b nu β * project urb_F_origin c γ δ)) = urb_cell mu nu
  simp only [h_inner]
  exact h_outer

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
lemma urb_cell_2_0 : urb_cell 2 0 = 0 := by eval_urb_cell
lemma urb_cell_2_1 : urb_cell 2 1 = 0 := by eval_urb_cell
lemma urb_cell_2_2 : urb_cell 2 2 = 12 := by eval_urb_cell
lemma urb_cell_2_3 : urb_cell 2 3 = 0 := by eval_urb_cell
lemma urb_cell_3_0 : urb_cell 3 0 = 0 := by eval_urb_cell
lemma urb_cell_3_1 : urb_cell 3 1 = 0 := by eval_urb_cell
lemma urb_cell_3_2 : urb_cell 3 2 = 0 := by eval_urb_cell
lemma urb_cell_3_3 : urb_cell 3 3 = 12 := by eval_urb_cell

lemma det_urb_g : (Matrix.diagonal ![- (12 : ℂ), 12, 12, 12]).det = -20736 := by
  rw [Matrix.det_diagonal, prod_4_eval_C]
  have h0 : ![- (12 : ℂ), 12, 12, 12] 0 = -12 := rfl
  have h1 : ![- (12 : ℂ), 12, 12, 12] 1 = 12 := rfl
  have h2 : ![- (12 : ℂ), 12, 12, 12] 2 = 12 := rfl
  have h3 : ![- (12 : ℂ), 12, 12, 12] 3 = 12 := rfl
  rw [h0, h1, h2, h3]
  ring

lemma metric_is_Lorentzian :
  isLorentzian (urbantkeMetric urb_F_origin) := by
  unfold isLorentzian
  have h_g : urbantkeMetric urb_F_origin = Matrix.diagonal ![- (12 : ℂ), 12, 12, 12] := by
    ext i j
    rw [urbantkeMetric_eq_cell i j]
    fin_cases i <;> fin_cases j
    · change urb_cell 0 0 = -12; exact urb_cell_0_0
    · change urb_cell 0 1 = 0; exact urb_cell_0_1
    · change urb_cell 0 2 = 0; exact urb_cell_0_2
    · change urb_cell 0 3 = 0; exact urb_cell_0_3
    · change urb_cell 1 0 = 0; exact urb_cell_1_0
    · change urb_cell 1 1 = 12; exact urb_cell_1_1
    · change urb_cell 1 2 = 0; exact urb_cell_1_2
    · change urb_cell 1 3 = 0; exact urb_cell_1_3
    · change urb_cell 2 0 = 0; exact urb_cell_2_0
    · change urb_cell 2 1 = 0; exact urb_cell_2_1
    · change urb_cell 2 2 = 12; exact urb_cell_2_2
    · change urb_cell 2 3 = 0; exact urb_cell_2_3
    · change urb_cell 3 0 = 0; exact urb_cell_3_0
    · change urb_cell 3 1 = 0; exact urb_cell_3_1
    · change urb_cell 3 2 = 0; exact urb_cell_3_2
    · change urb_cell 3 3 = 12; exact urb_cell_3_3
  rw [h_g]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> { simp [Matrix.diagonal]; try norm_num }
  · constructor
    · rw [det_urb_g]
      norm_num
    · rw [det_urb_g]
      norm_num

end CGD.Gravity

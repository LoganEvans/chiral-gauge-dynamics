-- FILENAME: CGD/Gravity/ExactSolutions/LorentzianEval.lean

import CGD.Gravity.ExactSolutions.LorentzianAnsatz

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def F_val_map (m n : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  match m, n with
  | 0, 1 => -sigmaX | 0, 2 => -sigmaY | 0, 3 => -sigmaZ
  | 1, 0 => sigmaX  | 1, 2 => Complex.I • sigmaZ | 1, 3 => -Complex.I • sigmaY
  | 2, 0 => sigmaY  | 2, 1 => -Complex.I • sigmaZ | 2, 3 => Complex.I • sigmaX
  | 3, 0 => sigmaZ  | 3, 1 => Complex.I • sigmaY | 3, 2 => -Complex.I • sigmaX
  | _, _ => 0

Litlib.theorem
  description "Exact Lorentzian Field Curvature At Origin"
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

noncomputable def adj_F_val (m n : Fin 4) (i j : Fin 3) : ℂ :=
  match m, n, i, j with
  | 0, 1, 1, 2 => -1 | 0, 1, 2, 1 => 1  | 0, 2, 0, 2 => 1  | 0, 2, 2, 0 => -1
  | 0, 3, 0, 1 => -1 | 0, 3, 1, 0 => 1  | 1, 0, 1, 2 => 1  | 1, 0, 2, 1 => -1
  | 2, 0, 0, 2 => -1 | 2, 0, 2, 0 => 1  | 3, 0, 0, 1 => 1  | 3, 0, 1, 0 => -1
  | 1, 2, 0, 1 => Complex.I | 1, 2, 1, 0 => -Complex.I
  | 2, 1, 0, 1 => -Complex.I | 2, 1, 1, 0 => Complex.I
  | 1, 3, 0, 2 => Complex.I | 1, 3, 2, 0 => -Complex.I
  | 3, 1, 0, 2 => -Complex.I | 3, 1, 2, 0 => Complex.I
  | 2, 3, 1, 2 => Complex.I | 2, 3, 2, 1 => -Complex.I
  | 3, 2, 1, 2 => -Complex.I | 3, 2, 2, 1 => Complex.I
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
      Int.cast_zero, Int.cast_one, Int.cast_neg, smul_eq_mul
    ]
    try ring_nf; try simp only [Complex.I_sq, I_pow_3_eq, I_pow_4_eq]; try ring
  ))

lemma adj_F_eq_val (m n : Fin 4) (i j : Fin 3) : adj_F m n i j = adj_F_val m n i j := by
  fin_cases m <;> fin_cases n <;> fin_cases i <;> fin_cases j <;> prove_adj_f

end CGD.Gravity

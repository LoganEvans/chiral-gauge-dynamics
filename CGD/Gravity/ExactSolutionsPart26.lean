-- FILENAME: CGD/Gravity/ExactSolutionsPart26.lean

import CGD.Gravity.ExactSolutionsPart26_3

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma prod_4_eval_C (f : Fin 4 → ℂ) :
  ∏ k : Fin 4, f k = f 0 * f 1 * f 2 * f 3 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_one]
  have h1 : (Fin.succ 0 : Fin 4) = 1 := rfl
  have h2 : (Fin.succ (Fin.succ 0) : Fin 4) = 2 := rfl
  have h3 : (Fin.succ (Fin.succ (Fin.succ 0)) : Fin 4) = 3 := rfl
  rw [h1, h2, h3]
  ring

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

-- FILENAME: CGD/Gravity/ExactSolutionsPart26_3.lean

import CGD.Gravity.ExactSolutionsPart26_2

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma urb_cell_2_0 : urb_cell 2 0 = 0 := by eval_urb_cell
lemma urb_cell_2_1 : urb_cell 2 1 = 0 := by eval_urb_cell
lemma urb_cell_2_2 : urb_cell 2 2 = 12 := by eval_urb_cell
lemma urb_cell_2_3 : urb_cell 2 3 = 0 := by eval_urb_cell
lemma urb_cell_3_0 : urb_cell 3 0 = 0 := by eval_urb_cell
lemma urb_cell_3_1 : urb_cell 3 1 = 0 := by eval_urb_cell
lemma urb_cell_3_2 : urb_cell 3 2 = 0 := by eval_urb_cell
lemma urb_cell_3_3 : urb_cell 3 3 = 12 := by eval_urb_cell

end CGD.Gravity

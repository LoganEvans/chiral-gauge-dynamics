-- FILENAME: CGD/Gravity/ExactSolutionsPart22.lean

import CGD.Gravity.ExactSolutionsPart21

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma exactLorentzian_comm_origin (mu nu : Fin 4) :
  ⁅exactLorentzianField mu origin, exactLorentzianField nu origin⁆ = 0 := by
  have h_mu : exactLorentzianField mu origin = 0 := exactLorentzianField_origin_zero mu
  have h_nu : exactLorentzianField nu origin = 0 := exactLorentzianField_origin_zero nu
  rw [h_mu, h_nu]
  simp

lemma toSl2c_sub (A B : Matrix (Fin 2) (Fin 2) ℂ) :
  toSl2c A - toSl2c B = toSl2c (A - B) := by
  apply Subtype.ext
  unfold toSl2c
  dsimp
  ext i j
  unfold Matrix.trace Matrix.diag
  simp [Fin.sum_univ_two, Matrix.sub_apply]
  ring

noncomputable def c_F_mat (mu nu : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  L_map nu (Pi.single mu 1) - L_map mu (Pi.single nu 1)

lemma curvature_origin_eq (mu nu : Fin 4) :
  curvatureSl2c exactLorentzianField mu nu origin = toSl2c (c_F_mat mu nu) := by
  rw [curvatureSl2c_def]
  rw [exactLorentzian_comm_origin mu nu, add_zero]
  rw [partialDerivSl2c_exactLorentzian_eval, partialDerivSl2c_exactLorentzian_eval]
  rw [toSl2c_sub]
  rfl

end CGD.Gravity

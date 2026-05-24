-- FILENAME: CGD/Gravity/ExactSolutionsPart12.lean

import CGD.Gravity.ExactSolutionsPart11

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

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

end CGD.Gravity

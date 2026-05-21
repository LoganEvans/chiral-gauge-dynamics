-- FILENAME: CGD/Quantum/SchroedingerPart6.lean

import CGD.Quantum.SchroedingerPart5

set_option linter.unusedSimpArgs false

open CGD.Foundations Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum

lemma P_minus_gamma0 : P_minus * gamma0 = - P_minus := by
  ext i j
  dsimp [P_minus]
  rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, gamma0_sq]
  simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply]
  ring

end CGD.Quantum

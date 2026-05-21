-- FILENAME: CGD/Quantum/SchroedingerPart5.lean

import CGD.Quantum.SchroedingerPart4

open CGD.Foundations Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum

lemma P_plus_gamma0 : P_plus * gamma0 = P_plus := by
  ext i j
  dsimp [P_plus]
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, gamma0_sq]
  simp [Matrix.smul_apply, Matrix.add_apply]
  ring

end CGD.Quantum

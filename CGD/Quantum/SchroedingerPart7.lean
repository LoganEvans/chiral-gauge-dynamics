-- FILENAME: CGD/Quantum/SchroedingerPart7.lean

import CGD.Quantum.SchroedingerPart6

open CGD.Foundations Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum

lemma P_plus_gammaVec (j : Fin 4) (hj : j ≠ 0) : P_plus * gammaVec j = gammaVec j * P_minus := by
  dsimp [P_plus, P_minus]
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  rw [gamma0_gammaVec_anti j hj]
  ext a b
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  try ring

end CGD.Quantum

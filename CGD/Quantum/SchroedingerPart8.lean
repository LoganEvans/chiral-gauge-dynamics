-- FILENAME: CGD/Quantum/SchroedingerPart8.lean

import CGD.Quantum.SchroedingerPart7

open CGD.Foundations Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum

lemma P_minus_gammaVec (j : Fin 4) (hj : j ≠ 0) : P_minus * gammaVec j = gammaVec j * P_plus := by
  dsimp [P_plus, P_minus]
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
  rw [gamma0_gammaVec_anti j hj]
  ext a b
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  try ring

end CGD.Quantum

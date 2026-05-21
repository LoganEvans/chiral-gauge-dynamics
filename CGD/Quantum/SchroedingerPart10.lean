-- FILENAME: CGD/Quantum/SchroedingerPart10.lean

import CGD.Quantum.SchroedingerPart9

open CGD.Foundations Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum

lemma P_plus_D_space (dPsi : Fin 4 → Matrix (Fin 4) (Fin 4) Complex) :
  P_plus * spatialDiracOp dPsi =
  gammaVec 1 * (P_minus * dPsi 1) + gammaVec 2 * (P_minus * dPsi 2) + gammaVec 3 * (P_minus * dPsi 3) := by
  dsimp [spatialDiracOp]
  rw [Matrix.mul_add, Matrix.mul_add]
  have h_assoc1 : P_plus * (gammaVec 1 * dPsi 1) = (P_plus * gammaVec 1) * dPsi 1 := (Matrix.mul_assoc _ _ _).symm
  have h_assoc2 : P_plus * (gammaVec 2 * dPsi 2) = (P_plus * gammaVec 2) * dPsi 2 := (Matrix.mul_assoc _ _ _).symm
  have h_assoc3 : P_plus * (gammaVec 3 * dPsi 3) = (P_plus * gammaVec 3) * dPsi 3 := (Matrix.mul_assoc _ _ _).symm
  rw [h_assoc1, h_assoc2, h_assoc3]
  rw [P_plus_gammaVec 1 (by decide), P_plus_gammaVec 2 (by decide), P_plus_gammaVec 3 (by decide)]
  have h_assoc4 : (gammaVec 1 * P_minus) * dPsi 1 = gammaVec 1 * (P_minus * dPsi 1) := Matrix.mul_assoc _ _ _
  have h_assoc5 : (gammaVec 2 * P_minus) * dPsi 2 = gammaVec 2 * (P_minus * dPsi 2) := Matrix.mul_assoc _ _ _
  have h_assoc6 : (gammaVec 3 * P_minus) * dPsi 3 = gammaVec 3 * (P_minus * dPsi 3) := Matrix.mul_assoc _ _ _
  rw [h_assoc4, h_assoc5, h_assoc6]

end CGD.Quantum

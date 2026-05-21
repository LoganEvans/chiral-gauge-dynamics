-- FILENAME: CGD/Quantum/SchroedingerPart9.lean

import CGD.Quantum.SchroedingerPart8

open CGD.Foundations Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum

lemma diracOperatorCore_expand (dPsi : Fin 4 → Matrix (Fin 4) (Fin 4) Complex) :
  (∑ mu, gammaVec mu * dPsi mu) = gamma0 * dPsi 0 + spatialDiracOp dPsi := by
  dsimp [spatialDiracOp]
  rw [sum_fin_4_matrix]
  have h0 : gammaVec 0 = gamma0 := rfl
  rw [h0]
  ext a b
  simp [Matrix.add_apply]
  ring

end CGD.Quantum

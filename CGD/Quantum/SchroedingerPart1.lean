-- FILENAME: CGD/Quantum/SchroedingerPart1.lean

import CGD.Quantum.Dirac
import Litlib.Core
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

open CGD.Foundations Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum

noncomputable def P_plus : Matrix (Fin 4) (Fin 4) Complex :=
  (1 / 2 : Complex) • (1 + gamma0)

noncomputable def P_minus : Matrix (Fin 4) (Fin 4) Complex :=
  (1 / 2 : Complex) • (1 - gamma0)

noncomputable def modulatedTemporalDeriv (dPsi0 Psi : Matrix (Fin 4) (Fin 4) Complex) (m : Complex) : Matrix (Fin 4) (Fin 4) Complex :=
  dPsi0 + m • Psi

noncomputable def spatialDiracOp (dPsi : Fin 4 → Matrix (Fin 4) (Fin 4) Complex) : Matrix (Fin 4) (Fin 4) Complex :=
  gammaVec 1 * dPsi 1 + gammaVec 2 * dPsi 2 + gammaVec 3 * dPsi 3

lemma sum_fin_4_matrix (f : Fin 4 → Matrix (Fin 4) (Fin 4) Complex) : ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp [add_assoc]

end CGD.Quantum

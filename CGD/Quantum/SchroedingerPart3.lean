-- FILENAME: CGD/Quantum/SchroedingerPart3.lean

import CGD.Quantum.SchroedingerPart2

open CGD.Foundations Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum

lemma gamma0_sq : gamma0 * gamma0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    rw [eval_mul_4x4_local]
    simp [gamma0, Matrix.fromBlocks, Matrix.reindex, Litlib.Math.Dirac.chiralIso, 
          Litlib.Math.Dirac.chiralIsoInv, Litlib.Math.Dirac.chiralIsoTo, 
          Matrix.submatrix, Sum.elim, Matrix.zero_apply]
  }

end CGD.Quantum

-- FILENAME: CGD/Quantum/SchroedingerPart4.lean

import CGD.Quantum.SchroedingerPart3

set_option linter.unusedSimpArgs false

open CGD.Foundations Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum

lemma gamma0_gammaVec_anti_1 : gamma0 * gammaVec 1 = - (gammaVec 1 * gamma0) := by
  ext a b
  fin_cases a <;> fin_cases b
  all_goals {
    rw [Matrix.neg_apply, eval_mul_4x4, eval_mul_4x4]
    simp [gamma0, gammaVec, gammaSpatial, 
          sigmaToMatrix, Litlib.Math.SU2.s1, Litlib.Math.SU2.s2, Litlib.Math.SU2.s3, 
          Matrix.fromBlocks, Matrix.reindex, Litlib.Math.Dirac.chiralIso, 
          Litlib.Math.Dirac.chiralIsoInv, Litlib.Math.Dirac.chiralIsoTo, 
          Matrix.submatrix, Sum.elim]
    try ring_nf
  }

lemma gamma0_gammaVec_anti_2 : gamma0 * gammaVec 2 = - (gammaVec 2 * gamma0) := by
  ext a b
  fin_cases a <;> fin_cases b
  all_goals {
    rw [Matrix.neg_apply, eval_mul_4x4, eval_mul_4x4]
    simp [gamma0, gammaVec, gammaSpatial, 
          sigmaToMatrix, Litlib.Math.SU2.s1, Litlib.Math.SU2.s2, Litlib.Math.SU2.s3, 
          Matrix.fromBlocks, Matrix.reindex, Litlib.Math.Dirac.chiralIso, 
          Litlib.Math.Dirac.chiralIsoInv, Litlib.Math.Dirac.chiralIsoTo, 
          Matrix.submatrix, Sum.elim]
    try ring_nf
  }

lemma gamma0_gammaVec_anti_3 : gamma0 * gammaVec 3 = - (gammaVec 3 * gamma0) := by
  ext a b
  fin_cases a <;> fin_cases b
  all_goals {
    rw [Matrix.neg_apply, eval_mul_4x4, eval_mul_4x4]
    simp [gamma0, gammaVec, gammaSpatial, 
          sigmaToMatrix, Litlib.Math.SU2.s1, Litlib.Math.SU2.s2, Litlib.Math.SU2.s3, 
          Matrix.fromBlocks, Matrix.reindex, Litlib.Math.Dirac.chiralIso, 
          Litlib.Math.Dirac.chiralIsoInv, Litlib.Math.Dirac.chiralIsoTo, 
          Matrix.submatrix, Sum.elim]
    try ring_nf
  }

/-- Proves the core Clifford spatial anticommutation natively via 4x4 block computation. -/
lemma gamma0_gammaVec_anti (j : Fin 4) (hj : j ≠ 0) : gamma0 * gammaVec j = - (gammaVec j * gamma0) := by
  revert hj
  fin_cases j
  · intro h; contradiction
  · intro _; exact gamma0_gammaVec_anti_1
  · intro _; exact gamma0_gammaVec_anti_2
  · intro _; exact gamma0_gammaVec_anti_3

end CGD.Quantum

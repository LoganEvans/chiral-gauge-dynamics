-- FILENAME: CGD/Gravity/ExactSolutionsPart6.lean

import CGD.Gravity.ExactSolutionsPart5

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma partialDerivMat_exactAbelianL (c : ℂ) (k : Fin 4) (x : SpacetimePoint) :
  partialDerivMat k (fun p => exactAbelianL c p) x = if k = 1 then c • sigmaX else 0 := by
  ext i j
  unfold partialDerivMat exactAbelianL
  change partialDeriv k (fun p => p 1 • (c • sigmaX) i j) x = (if k = 1 then c • sigmaX else 0) i j
  rw [partialDeriv_coord_smul 1 ((c • sigmaX) i j) k x]
  by_cases hk : k = 1
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk]
    rfl

end CGD.Gravity

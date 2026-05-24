-- FILENAME: CGD/Gravity/ExactSolutionsPart7.lean

import CGD.Gravity.ExactSolutionsPart6

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma toSl2c_exactAbelianL (c : ℂ) (p : SpacetimePoint) :
  (toSl2c (exactAbelianL c p)).val = exactAbelianL c p := by
  unfold toSl2c exactAbelianL
  dsimp
  have h_tr : Matrix.trace (p 1 • c • sigmaX) = 0 := by
    unfold Matrix.trace Matrix.diag
    have h_sum : ∑ i : Fin 2, (p 1 • c • sigmaX) i i = (p 1 • c • sigmaX) 0 0 + (p 1 • c • sigmaX) 1 1 := Fin.sum_univ_two _
    rw [h_sum]
    unfold sigmaX mkMat
    change p 1 * (c * 0) + p 1 * (c * 0) = 0
    ring
  rw [h_tr]
  have hz : (0 : ℂ) / 2 = 0 := by ring
  rw [hz, zero_smul, sub_zero]

end CGD.Gravity

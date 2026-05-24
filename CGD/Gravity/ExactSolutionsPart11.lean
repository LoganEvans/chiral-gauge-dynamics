-- FILENAME: CGD/Gravity/ExactSolutionsPart11.lean

import CGD.Gravity.ExactSolutionsPart10

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma curvature_exactAbelian (c : ℂ) (m n : Fin 4) (x : SpacetimePoint) :
  curvatureSl2c (exactAbelianField c) m n x = curvature_const c m n := by
  rw [curvatureSl2c_def]
  rw [comm_exactAbelian c m n x, add_zero]
  rw [partialDerivSl2c_exactAbelian, partialDerivSl2c_exactAbelian]
  unfold curvature_const
  by_cases h1 : m = 1 ∧ n = 2
  · have h2_false : ¬(n = 1 ∧ m = 2) := by
      intro h
      have h_m : (1 : Fin 4) = 2 := Eq.trans h1.left.symm h.right
      revert h_m
      decide
    simp only [if_pos h1, if_neg h2_false, sub_zero]
  · by_cases h2 : m = 2 ∧ n = 1
    · have h2_rev : n = 1 ∧ m = 2 := And.intro h2.right h2.left
      simp only [if_neg h1, if_pos h2, if_pos h2_rev, zero_sub]
      have h_inner : (-c) • sigmaX = - (c • sigmaX) := by
        ext i j
        change (-c) * sigmaX i j = - (c * sigmaX i j)
        ring
      rw [h_inner]
      exact (toSl2c_neg (c • sigmaX)).symm
    · have h2_rev_false : ¬(n = 1 ∧ m = 2) := by
        intro h
        apply h2
        exact And.intro h.right h.left
      simp only [if_neg h1, if_neg h2, if_neg h2_rev_false, sub_zero]

end CGD.Gravity

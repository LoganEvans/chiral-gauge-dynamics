-- FILENAME: CGD/Gravity/ExactSolutionsPart9.lean

import CGD.Gravity.ExactSolutionsPart8

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma comm_exactAbelian (c : ℂ) (m n : Fin 4) (x : SpacetimePoint) :
  ⁅exactAbelianField c m x, exactAbelianField c n x⁆ = 0 := by
  unfold exactAbelianField
  by_cases hm : m = 2 <;> by_cases hn : n = 2
  · simp [hm, hn]
  · simp [hm, hn]
  · simp [hm, hn]
  · simp [hm, hn]

end CGD.Gravity

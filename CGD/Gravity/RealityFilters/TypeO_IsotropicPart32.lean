-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart32.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart31
import CGD.Gravity.Geometry

open CGD.Foundations Complex Matrix CGD.Gravity

namespace CGD.Gravity.RealityFilters

/-- 
Expands the 4-dimensional Levi-Civita summation over the spacetime indices.
Reduces 256 terms down to the 24 strictly non-zero permutations.
-/
lemma urbantke_sum_space (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
  (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4, epsilon4 a b c d * F a b c d) =
  F 0 1 2 3 - F 0 1 3 2 - F 0 2 1 3 + F 0 2 3 1 + F 0 3 1 2 - F 0 3 2 1
  - F 1 0 2 3 + F 1 0 3 2 + F 1 2 0 3 - F 1 2 3 0 - F 1 3 0 2 + F 1 3 2 0
  + F 2 0 1 3 - F 2 0 3 1 - F 2 1 0 3 + F 2 1 3 0 + F 2 3 0 1 - F 2 3 1 0
  - F 3 0 1 2 + F 3 0 2 1 + F 3 1 0 2 - F 3 1 2 0 - F 3 2 0 1 + F 3 2 1 0 := by
  simp [Fin.sum_univ_four, epsilon4, epsilon4_int]
  ring

end CGD.Gravity.RealityFilters

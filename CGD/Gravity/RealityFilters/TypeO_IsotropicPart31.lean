-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart31.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart30
import CGD.Gravity.Geometry

open CGD.Foundations Complex Matrix CGD.Gravity

namespace CGD.Gravity.RealityFilters

/-- 
Expands the 3-dimensional Levi-Civita summation over the internal isotopic indices.
Reduces 27 terms down to the 6 strictly non-zero permutations.
-/
lemma urbantke_sum_iso (F : Fin 3 → Fin 3 → Fin 3 → ℂ) :
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * F a b c) =
  F 0 1 2 - F 0 2 1 - F 1 0 2 + F 1 2 0 + F 2 0 1 - F 2 1 0 := by
  simp [Fin.sum_univ_three, epsilon3, epsilon3_int]
  ring

end CGD.Gravity.RealityFilters

-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart1.lean

import CGD.Foundations.Calculus
import CGD.Gravity.Geometry

open CGD.Foundations Complex Matrix BigOperators

namespace CGD.Gravity.RealityFilters

/-- The exact Type O matrix evaluator. -/
noncomputable def typeO_L (a : ℝ → ℂ) (μ : Fin 4) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  if μ = 0 then 0
  else if μ = 1 then a (x 0) • sigma1.val
  else if μ = 2 then a (x 0) • sigma2.val
  else if μ = 3 then a (x 0) • sigma3.val
  else 0

/-- The exact Type O gauge field evaluator in SL2C. -/
noncomputable def typeO_A (a : ℝ → ℂ) (μ : Fin 4) (x : SpacetimePoint) : SL2C :=
  toSl2c (typeO_L a μ x)

lemma fin2_sum (f : Fin 2 → ℂ) : ∑ i : Fin 2, f i = f 0 + f 1 := by
  have eq : (Finset.univ : Finset (Fin 2)) = {0, 1} := rfl
  rw [eq]
  simp [Finset.sum_insert, Finset.sum_singleton]

end CGD.Gravity.RealityFilters

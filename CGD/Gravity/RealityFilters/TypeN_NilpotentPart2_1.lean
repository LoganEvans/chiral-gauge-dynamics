-- FILENAME: CGD/Gravity/RealityFilters/TypeN_NilpotentPart2_1.lean

import CGD.Gravity.RealityFilters.TypeN_NilpotentPart1
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- Differentiability of the retarded time coordinate u = t - z. -/
lemma diff_retarded (x : SpacetimePoint) : 
  DifferentiableAt ℝ (fun p => p 0 - p 3) x := by
  let L0 : SpacetimePoint →L[ℝ] ℝ := ContinuousLinearMap.proj (0 : Fin 4)
  let L3 : SpacetimePoint →L[ℝ] ℝ := ContinuousLinearMap.proj (3 : Fin 4)
  let L : SpacetimePoint →L[ℝ] ℝ := L0 - L3
  have h_eq : (fun p : SpacetimePoint => p 0 - p 3) = L := rfl
  rw [h_eq]
  exact L.hasFDerivAt.differentiableAt

end CGD.Gravity.RealityFilters

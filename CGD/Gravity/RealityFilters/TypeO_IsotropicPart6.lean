-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart6.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart5

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
Proves that the coordinate-projected time function remains differentiable on the 4D manifold.
-/
lemma diff_time_dep (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  DifferentiableAt ℝ (fun p => a (p 0)) x := by
  let proj0 : SpacetimePoint →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have h_comp : (fun (p : SpacetimePoint) => a (p 0)) = a ∘ proj0 := by
    ext p
    rfl
  rw [h_comp]
  have h_proj_diff : DifferentiableAt ℝ proj0 x := proj0.differentiableAt
  exact DifferentiableAt.comp x ha h_proj_diff

end CGD.Gravity.RealityFilters

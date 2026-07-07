-- FILENAME: CGD/Gravity/RealityFilters/TypeN_NilpotentPart6_3_Metric.lean

import CGD.Gravity.RealityFilters.TypeN_NilpotentPart6_2_Metric

open CGD.Foundations Complex Matrix CGD.Gravity

namespace CGD.Gravity.RealityFilters

/-- 
Evaluates the determinant of the perturbed Type N Urbantke metric. 
Because gravitational waves are strictly null and traceless, their scalar invariants 
vanish identically (F ∧ F = 0), leaving the exact background FLRW volume.
-/
lemma typeN_det_eval (a f : ℝ → ℂ) (v : Fin 4 → ℂ) (x : SpacetimePoint) 
  (ha : DifferentiableAt ℝ a (x 0)) (hf : DifferentiableAt ℝ f (x 0 - x 3)) :
  (urbantkeMetric (fun m n => curvatureSl2c (typeN_A a f v) m n x)).det = 
  -1327104 * (fderiv ℝ a (x 0) 1) ^ 6 * (a (x 0)) ^ 12 := sorry

end CGD.Gravity.RealityFilters

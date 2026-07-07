-- FILENAME: CGD/Gravity/RealityFilters/TypeN_NilpotentPart6_2_Metric.lean

import CGD.Gravity.RealityFilters.TypeN_NilpotentPart6_1_Metric

open CGD.Foundations Complex Matrix CGD.Gravity

namespace CGD.Gravity.RealityFilters

/-- Evaluates the macroscopic Urbantke metric components for the perturbed Type N universe. -/
lemma typeN_metric_components (a f : ℝ → ℂ) (v : Fin 4 → ℂ) (x : SpacetimePoint) 
  (ha : DifferentiableAt ℝ a (x 0)) (hf : DifferentiableAt ℝ f (x 0 - x 3)) (μ ν : Fin 4) :
  urbantkeMetric (fun m n => curvatureSl2c (typeN_A a f v) m n x) μ ν = expected_typeN_metric a f v x μ ν := sorry

end CGD.Gravity.RealityFilters

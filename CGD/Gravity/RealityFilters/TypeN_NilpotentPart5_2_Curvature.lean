-- FILENAME: CGD/Gravity/RealityFilters/TypeN_NilpotentPart5_2_Curvature.lean

import CGD.Gravity.RealityFilters.TypeN_NilpotentPart5_1_Curvature

open CGD.Foundations Complex Matrix CGD.Gravity

namespace CGD.Gravity.RealityFilters

/-- Evaluates the full curvature matrix F_μν for the Type N connection. -/
lemma typeN_F_val_eval (a f : ℝ → ℂ) (v : Fin 4 → ℂ) (x : SpacetimePoint) 
  (ha : DifferentiableAt ℝ a (x 0)) (hf : DifferentiableAt ℝ f (x 0 - x 3)) (μ ν : Fin 4) :
  (curvatureSl2c (typeN_A a f v) μ ν x).val = expected_typeN_F a f v x μ ν := sorry

end CGD.Gravity.RealityFilters

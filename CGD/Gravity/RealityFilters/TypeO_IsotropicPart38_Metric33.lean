-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart38_Metric33.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart37_Metric22

open CGD.Foundations Complex Matrix CGD.Gravity

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace CGD.Gravity.RealityFilters

/--
Evaluates the z-z spatial component of the macroscopic Urbantke metric for the Type O cosmological vacuum.
Yields precisely -48 * adot * a^4, capturing the dynamic expansion of the spatial hypersurface.
-/
lemma typeO_metric_33 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  urbantkeMetric (fun m n => curvatureSl2c (typeO_A a) m n x) 3 3 = -48 * (fderiv ℝ a (x 0) 1) * (a (x 0) * a (x 0)) ^ 2 := by
  
  -- Unfold the Urbantke metric definition
  unfold urbantkeMetric
  
  -- Substitute all 'let' bindings to expose the raw tensor products
  dsimp only
  
  -- Associate the products to match the `urbantke_sum_space` signature
  simp only [space_term_mul_assoc]
  
  -- Apply the 3D internal and 4D spacetime Levi-Civita exact reduction theorems
  rw [urbantke_sum_iso]
  simp only [urbantke_sum_space]

  -- Inject the 48 exact projection traces
  simp only [typeO_project_master_c0 a x ha, typeO_project_master_c1 a x ha, typeO_project_master_c2 a x ha]
  
  -- Evaluate the conditional expectation matrix directly
  dsimp [typeO_P_expected]

  -- Algebraic reduction
  try ring_nf
  try simp only [Complex.I_sq, I_cubed_local]
  try ring

end CGD.Gravity.RealityFilters

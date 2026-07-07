-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart35_Metric00.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart34_0
import CGD.Gravity.RealityFilters.TypeO_IsotropicPart34_1
import CGD.Gravity.RealityFilters.TypeO_IsotropicPart34_2
import CGD.Gravity.RealityFilters.TypeO_IsotropicPart33
import CGD.Gravity.RealityFilters.TypeO_IsotropicPart32
import CGD.Gravity.RealityFilters.TypeO_IsotropicPart31

open CGD.Foundations Complex Matrix CGD.Gravity

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace CGD.Gravity.RealityFilters

lemma I_cubed_local : Complex.I ^ 3 = -Complex.I := by
  have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
  calc Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
  _ = -1 * Complex.I := by rw [h2]
  _ = -Complex.I := by ring

lemma space_term_mul_assoc (E F1 F2 F3 : ℂ) : E * F1 * F2 * F3 = E * (F1 * F2 * F3) := by ring

/--
Evaluates the time-time component of the macroscopic Urbantke metric for the Type O cosmological vacuum.
Yields precisely 12 * adot^3, driving the temporal signature of the expanding FLRW universe.
-/
lemma typeO_metric_00 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  urbantkeMetric (fun m n => curvatureSl2c (typeO_A a) m n x) 0 0 = 12 * (fderiv ℝ a (x 0) 1) ^ 3 := by
  
  -- Unfold the Urbantke metric definition
  unfold urbantkeMetric
  
  -- Substitute all 'let' bindings to expose the raw tensor products
  dsimp only
  
  -- Associate the products to match the `urbantke_sum_space` signature: eps * F1 * F2 * F3 -> eps * (F1 * F2 * F3)
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

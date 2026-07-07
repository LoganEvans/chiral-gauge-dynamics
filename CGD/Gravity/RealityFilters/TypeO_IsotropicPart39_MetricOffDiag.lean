-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart39_MetricOffDiag.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart38_Metric33

open CGD.Foundations Complex Matrix CGD.Gravity

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace CGD.Gravity.RealityFilters

/--
Evaluates the off-diagonal spatial components of the macroscopic Urbantke metric for the Type O cosmological vacuum.
Because the FLRW spatial slices are strictly isotropic and orthogonal to the time flow, all off-diagonals evaluate to exactly 0.
-/
lemma typeO_metric_off_diagonal (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) (μ ν : Fin 4) (h_diff : μ ≠ ν) :
  urbantkeMetric (fun m n => curvatureSl2c (typeO_A a) m n x) μ ν = 0 := by
  
  -- Destruct the grid and discard the 4 diagonal cases via contradiction
  revert h_diff
  fin_cases μ <;> fin_cases ν <;> intro h_diff <;> try { contradiction }
  
  -- The remaining 12 non-diagonal cases are pumped through the reduction engine
  all_goals {
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

    -- Algebraic reduction collapses all off-diagonal cross-terms to zero
    try ring_nf
    try simp only [Complex.I_sq, I_cubed_local]
    try ring
  }

end CGD.Gravity.RealityFilters

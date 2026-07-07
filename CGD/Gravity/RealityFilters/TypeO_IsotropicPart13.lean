-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart13.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart12

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
The temporal component of the FLRW connection is identically zero in the Weyl gauge.
-/
lemma typeO_L_0_eq (a : ℝ → ℂ) (x : SpacetimePoint) :
  typeO_L a 0 x = 0 := by
  unfold typeO_L
  simp

end CGD.Gravity.RealityFilters

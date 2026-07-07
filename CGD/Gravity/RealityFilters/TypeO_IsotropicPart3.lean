-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart3.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart2

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

lemma typeO_A_val_eq (a : ℝ → ℂ) (μ : Fin 4) (x : SpacetimePoint) :
  (typeO_A a μ x).val = typeO_L a μ x := by
  unfold typeO_A
  have h_tr := typeO_L_trace_zero a μ x
  rw [toSl2c_val_eq _ h_tr]

end CGD.Gravity.RealityFilters

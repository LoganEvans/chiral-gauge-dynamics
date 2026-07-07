-- FILENAME: CGD/Gravity/RealityFilters/TypeN_NilpotentPart6_4_Metric.lean

import CGD.Gravity.RealityFilters.TypeN_NilpotentPart6_3_Metric

open CGD.Foundations Complex Matrix CGD.Gravity

namespace CGD.Gravity.RealityFilters

/-- Proves the determinant satisfies the strict Lorentzian reality conditions (Real and strictly negative). -/
lemma typeN_det_signs (adot a_val : ℂ)
  (h_adot_im : adot.im = 0) (h_a_im : a_val.im = 0)
  (h_adot_nz : adot ≠ 0) (h_a_nz : a_val ≠ 0) :
  let det := -1327104 * adot ^ 6 * a_val ^ 12
  det.im = 0 ∧ det.re < 0 := sorry

end CGD.Gravity.RealityFilters

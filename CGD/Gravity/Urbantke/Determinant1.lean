-- FILENAME: CGD/Gravity/Urbantke/Determinant1.lean

import CGD.Gravity.Urbantke.PseudoInverse
import CGD.Gravity.Urbantke.MetricTrace8
import CGD.Gravity.Urbantke.PlebanskiComponents1

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

/-- 
If the CDJ constraints hold, the resulting constructed metric is mathematically 
guaranteed to be non-degenerate.
-/
lemma urbantke_nondeg_of_cdj_eq2_21 
  (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  (sqrt_g detPsi : ℂ)
  (h_sqrt_g : sqrt_g^2 = (cgdUnimodularMetricAdapter F).det)
  (h_eq2_21 : (3 * I / 2 : ℂ) * sqrt_g * detPsi = 1) :
  (cgdUnimodularMetricAdapter F).det ≠ 0 := by
  
  -- Given the CDJ Eq 2.21 physical constraint, a degenerate metric mathematically yields a contradiction.
  intro h_cgd_det_zero
  rw [h_cgd_det_zero] at h_sqrt_g
  have h_sqrt_zero : sqrt_g = 0 := sq_eq_zero_iff.mp h_sqrt_g
  rw [h_sqrt_zero] at h_eq2_21
  have h_zero_eq_one : (0 : ℂ) = 1 := by
    calc (0 : ℂ) = (3 * I / 2 : ℂ) * 0 * detPsi := by ring
    _ = 1 := h_eq2_21
  exact zero_ne_one h_zero_eq_one

end CGD.Gravity

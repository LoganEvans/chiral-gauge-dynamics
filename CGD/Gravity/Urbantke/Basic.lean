-- FILENAME: CGD/Gravity/Urbantke/Basic.lean

import CGD.Gravity.Geometry
import CGD.Foundations.GaugeGroup
import Litlib.Y1991.capovilla1991pure.Signature
import Mathlib.Topology.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

noncomputable def eps2 : Fin 2 → Fin 2 → ℂ := !![0, 1; -1, 0]
noncomputable def eps2_up : Fin 2 → Fin 2 → ℂ := !![0, 1; -1, 0]

def clump (i j : Fin 2) : Fin 3 :=
  if i = 0 ∧ j = 0 then 0
  else if i = 1 ∧ j = 1 then 1
  else 2

/-- 
The symmetric Pauli-spinor basis matrices: tau_a = sigma_a * eps2 
This ensures the curvature tensor R_{AB} is symmetric in A, B.
-/
noncomputable def tau (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  if a = 0 then !![-1, 0; 0, 1] 
  else if a = 1 then !![Complex.I, 0; 0, Complex.I] 
  else !![0, 1; 1, 0]

def F_comp (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3) (μ ν : Fin 4) : ℂ :=
  if a = 0 then F μ ν 1 2 else if a = 1 then F μ ν 2 0 else F μ ν 0 1

noncomputable def cgdUnimodularMetricAdapter (F_adj : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  urbantkeMetric (fun μ ν => 
    toSl2c (F_adj μ ν 1 2 • sigma1.val + F_adj μ ν 2 0 • sigma2.val + F_adj μ ν 0 1 • sigma3.val))

noncomputable def capovilla_R (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (μ ν : Fin 4) (A B : Fin 2) : ℂ :=
  ∑ a : Fin 3, F_comp F a μ ν * tau a A B

end CGD.Gravity

-- FILENAME: CGD/Quantum/Dirac/Unroll.lean

import CGD.Quantum.Dirac.Definitions

open Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum.Dirac

/-- 
A custom expansion lemma to force Lean to evaluate Fin 4 sums 
explicitly into 4 terms, bypassing abstract tensor heuristics.
-/
lemma sum_fin4_unroll {α : Type*} [AddCommMonoid α] (f : Fin 4 → α) : 
  (∑ i : Fin 4, f i) = f 0 + f 1 + f 2 + f 3 := by
  exact Fin.sum_univ_four f

end CGD.Quantum.Dirac

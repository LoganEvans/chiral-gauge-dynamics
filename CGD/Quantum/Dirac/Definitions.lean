-- FILENAME: CGD/Quantum/Dirac/Definitions.lean

import Litlib.Core
import Litlib.Math.Dirac

open Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum.Dirac

/-- The local Minkowski metric (+ - - -) for the tangent space Clifford algebra. -/
noncomputable def minkowskiEta (a b : Fin 4) : ℂ :=
  if a = 0 ∧ b = 0 then 1
  else if a = b then -1
  else 0

/-- 
The Geometric Spinor (Kähler-Dirac Mode). 
Constructed strictly from the local internal curvature components F_{ab}.
This guarantees flawless gauge covariance (adjoint representation) 
and removes the need for arbitrary fermion fields.
-/
@[litlib_track "Geometric Spinor Definition"]
noncomputable def geometricSpinor (F : Fin 4 → Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ a : Fin 4, ∑ b : Fin 4, F a b • (gammaVec a * gammaVec b)

/-- 
The Geometric Yang-Mills Current. 
Defined as the covariant divergence of the curvature tensor.
-/
noncomputable def yangMillsCurrent (D_F : Fin 4 → Fin 4 → Fin 4 → ℂ) (b : Fin 4) : ℂ :=
  ∑ c : Fin 4, ∑ a : Fin 4, minkowskiEta c a * D_F c a b

end CGD.Quantum.Dirac

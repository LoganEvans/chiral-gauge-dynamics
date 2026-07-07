-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart14.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart13

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
The partial derivatives of the temporal component of the FLRW connection are identically zero.
-/
lemma partialDerivMat_typeO_L_k_0 (a : ℝ → ℂ) (k : Fin 4) (x : SpacetimePoint) :
  partialDerivMat k (fun p => typeO_L a 0 p) x = 0 := by
  have h_direct : (fun p => typeO_L a 0 p) = fun _ => 0 := funext (fun p => typeO_L_0_eq a p)
  rw [h_direct]
  exact partialDerivMat_const 0 k x

end CGD.Gravity.RealityFilters

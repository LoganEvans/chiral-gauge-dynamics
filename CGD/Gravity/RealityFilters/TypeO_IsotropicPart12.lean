-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart12.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart11

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
Evaluates the spatial partial derivative of the mu=3 Type O connection matrix.
-/
lemma partialDerivMat_typeO_L_k_3 (a : ℝ → ℂ) (k : Fin 4) (x : SpacetimePoint) 
  (hk : k ≠ 0) (ha : DifferentiableAt ℝ a (x 0)) :
  partialDerivMat k (fun p => typeO_L a 3 p) x = 0 := by
  ext i j
  unfold partialDerivMat
  have h_eq : (fun p => typeO_L a 3 p i j) = fun p => sigma3.val i j * a (p 0) := by
    ext p
    have h_eval : typeO_L a 3 p = a (p 0) • sigma3.val := by
      unfold typeO_L
      simp
    rw [h_eval]
    change a (p 0) * sigma3.val i j = sigma3.val i j * a (p 0)
    ring
  rw [h_eq]
  have hd := diff_time_dep a x ha
  rw [partialDeriv_const_smul (sigma3.val i j) (fun p => a (p 0)) k x hd]
  rw [partialDeriv_time_dep_spatial a k x hk ha]
  change sigma3.val i j * 0 = 0
  ring

end CGD.Gravity.RealityFilters

-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart9.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart8

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
Evaluates the temporal partial derivative of the mu=2 Type O connection matrix.
-/
lemma partialDerivMat_typeO_L_0_2 (a : ℝ → ℂ) (x : SpacetimePoint) 
  (ha : DifferentiableAt ℝ a (x 0)) :
  partialDerivMat 0 (fun p => typeO_L a 2 p) x = (fderiv ℝ a (x 0) 1) • sigma2.val := by
  ext i j
  unfold partialDerivMat
  have h_eq : (fun p => typeO_L a 2 p i j) = fun p => sigma2.val i j * a (p 0) := by
    ext p
    have h_eval : typeO_L a 2 p = a (p 0) • sigma2.val := by
      unfold typeO_L
      simp
    rw [h_eval]
    change a (p 0) * sigma2.val i j = sigma2.val i j * a (p 0)
    ring
  rw [h_eq]
  have hd := diff_time_dep a x ha
  rw [partialDeriv_const_smul (sigma2.val i j) (fun p => a (p 0)) 0 x hd]
  rw [partialDeriv_time_dep_time a x ha]
  change sigma2.val i j * fderiv ℝ a (x 0) 1 = fderiv ℝ a (x 0) 1 * sigma2.val i j
  ring

end CGD.Gravity.RealityFilters

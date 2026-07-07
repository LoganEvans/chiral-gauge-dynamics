-- FILENAME: CGD/Gravity/RealityFilters/TypeN_NilpotentPart3_1_Derivs.lean

import CGD.Gravity.RealityFilters.TypeN_NilpotentPart2

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

lemma partialDerivMat_typeN_L_k_0 (a f : ℝ → ℂ) (v : Fin 4 → ℂ) (k : Fin 4) (x : SpacetimePoint) 
  (hf : DifferentiableAt ℝ f (x 0 - x 3)) :
  partialDerivMat k (fun p => typeN_L a f v 0 p) x = 
    (partialDeriv k (fun p => f (p 0 - p 3)) x * v 0) • (sigma1.val + Complex.I • sigma2.val) := by
  ext i j
  have h_chain : DifferentiableAt ℝ (fun p => f (p 0 - p 3)) x := DifferentiableAt.comp x hf (diff_retarded x)
  have h_eq : (fun p => typeN_L a f v 0 p i j) = (fun p => (v 0 * (sigma1.val + Complex.I • sigma2.val) i j) * f (p 0 - p 3)) := by
    ext p
    unfold typeN_L
    have h0 : (0:Fin 4) = 0 := rfl
    simp only [h0, if_true]
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  unfold partialDerivMat
  rw [h_eq]
  rw [partialDeriv_const_smul _ _ k x h_chain]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

end CGD.Gravity.RealityFilters

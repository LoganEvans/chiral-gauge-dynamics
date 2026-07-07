-- FILENAME: CGD/Gravity/RealityFilters/TypeN_NilpotentPart3_2_Derivs.lean

import CGD.Gravity.RealityFilters.TypeN_NilpotentPart3_1_Derivs

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

lemma partialDerivMat_typeN_L_k_1 (a f : ℝ → ℂ) (v : Fin 4 → ℂ) (k : Fin 4) (x : SpacetimePoint) 
  (ha : DifferentiableAt ℝ (fun p : SpacetimePoint => a (p 0)) x)
  (hf : DifferentiableAt ℝ f (x 0 - x 3)) :
  partialDerivMat k (fun p => typeN_L a f v 1 p) x = 
    (partialDeriv k (fun p => a (p 0)) x) • sigma1.val + 
    (partialDeriv k (fun p => f (p 0 - p 3)) x * v 1) • (sigma1.val + Complex.I • sigma2.val) := by
  ext i j
  have h_chain : DifferentiableAt ℝ (fun p => f (p 0 - p 3)) x := DifferentiableAt.comp x hf (diff_retarded x)
  have h_eq : (fun p => typeN_L a f v 1 p i j) = (fun p => (sigma1.val i j) * a (p 0) + (v 1 * (sigma1.val + Complex.I • sigma2.val) i j) * f (p 0 - p 3)) := by
    ext p
    unfold typeN_L
    have hn : (1:Fin 4) ≠ 0 := by decide
    have hy : (1:Fin 4) = 1 := rfl
    simp only [hn, hy, if_false, if_true]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  unfold partialDerivMat
  rw [h_eq]
  have h_a_proj : DifferentiableAt ℝ (fun p : SpacetimePoint => a (p 0)) x := ha
  have h_left : DifferentiableAt ℝ (fun p => (sigma1.val i j) * a (p 0)) x := diff_const_mul _ _ _ h_a_proj
  have h_right : DifferentiableAt ℝ (fun p => (v 1 * (sigma1.val + Complex.I • sigma2.val) i j) * f (p 0 - p 3)) x := diff_const_mul _ _ _ h_chain
  rw [partialDeriv_add _ _ _ _ h_left h_right]
  rw [partialDeriv_const_smul _ _ _ _ h_a_proj]
  rw [partialDeriv_const_smul _ _ _ _ h_chain]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end CGD.Gravity.RealityFilters

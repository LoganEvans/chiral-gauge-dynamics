-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart18.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart17
import Mathlib.Analysis.Calculus.ContDiff.Basic

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
Proves that the internal elements of the Type O matrix field are everywhere differentiable, 
satisfying the prerequisite for invoking the rigorous curvature matrix evaluation theorem.
-/
lemma typeO_A_differentiable (a : ℝ → ℂ) (μ : Fin 4) (x : SpacetimePoint) 
  (ha : DifferentiableAt ℝ a (x 0)) :
  ∀ i j, DifferentiableAt ℝ (fun p => (typeO_A a μ p).val i j) x := by
  intros i j
  have h_eq : (fun p => (typeO_A a μ p).val i j) = fun p => typeO_L a μ p i j := by
    ext p
    rw [typeO_A_val_eq]
  rw [h_eq]
  unfold typeO_L
  split_ifs
  · exact differentiableAt_const 0
  · have h_smul : (fun (p : SpacetimePoint) => (a (p 0) • sigma1.val) i j) = fun (p : SpacetimePoint) => sigma1.val i j * a (p 0) := by
      ext p
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    rw [h_smul]
    exact DifferentiableAt.const_mul (diff_time_dep a x ha) (sigma1.val i j)
  · have h_smul : (fun (p : SpacetimePoint) => (a (p 0) • sigma2.val) i j) = fun (p : SpacetimePoint) => sigma2.val i j * a (p 0) := by
      ext p
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    rw [h_smul]
    exact DifferentiableAt.const_mul (diff_time_dep a x ha) (sigma2.val i j)
  · have h_smul : (fun (p : SpacetimePoint) => (a (p 0) • sigma3.val) i j) = fun (p : SpacetimePoint) => sigma3.val i j * a (p 0) := by
      ext p
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    rw [h_smul]
    exact DifferentiableAt.const_mul (diff_time_dep a x ha) (sigma3.val i j)
  · exact differentiableAt_const 0

end CGD.Gravity.RealityFilters

-- FILENAME: CGD/Gravity/RealityFilters/TypeN_NilpotentPart2_3.lean

import CGD.Gravity.RealityFilters.TypeN_NilpotentPart2_2
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- Longitudinal spatial derivative of a purely retarded-time dependent function f(t-z). -/
lemma partialDeriv_retarded_3
  (f : ℝ → ℂ) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f (x 0 - x 3)) :
  partialDeriv 3 (fun p => f (p 0 - p 3)) x = - fderiv ℝ f (x 0 - x 3) 1 := by
  unfold partialDeriv
  let L0 : SpacetimePoint →L[ℝ] ℝ := ContinuousLinearMap.proj (0 : Fin 4)
  let L3 : SpacetimePoint →L[ℝ] ℝ := ContinuousLinearMap.proj (3 : Fin 4)
  let L : SpacetimePoint →L[ℝ] ℝ := L0 - L3
  have h_comp : (fun p : SpacetimePoint => f (p 0 - p 3)) = f ∘ L := rfl
  rw [h_comp]
  
  have h_eval : L x = x 0 - x 3 := rfl
  
  have hf' : DifferentiableAt ℝ f (L x) := by
    rw [h_eval]
    exact hf
    
  have hdL : DifferentiableAt ℝ L x := L.hasFDerivAt.differentiableAt
  rw [fderiv_comp x hf' hdL]
  rw [ContinuousLinearMap.comp_apply]
  rw [L.hasFDerivAt.fderiv]
  
  -- The chain rule produced `L x`, so we rewrite it back to `x 0 - x 3` to match the target.
  rw [h_eval]
  
  have hL_val : L (Pi.single 3 1) = -1 := by
    -- We use `change` to definitionally evaluate the ContinuousLinearMap application
    change (Pi.single (3:Fin 4) (1:ℝ) : SpacetimePoint) 0 - (Pi.single (3:Fin 4) (1:ℝ) : SpacetimePoint) 3 = -1
    have h0 : (Pi.single (3:Fin 4) (1:ℝ) : SpacetimePoint) 0 = 0 := by simp
    have h3 : (Pi.single (3:Fin 4) (1:ℝ) : SpacetimePoint) 3 = 1 := by simp
    rw [h0, h3]
    exact zero_sub 1
    
  rw [hL_val]
  exact ContinuousLinearMap.map_neg (fderiv ℝ f (x 0 - x 3)) 1

end CGD.Gravity.RealityFilters

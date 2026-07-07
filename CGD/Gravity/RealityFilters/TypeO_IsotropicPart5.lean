-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart5.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart4
import Mathlib.Analysis.Calculus.FDeriv.Mul

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
Temporal derivatives of time-dependent isotropic functions strictly evaluate to the 1D chain rule derivative.
-/
lemma partialDeriv_time_dep_time
  (f : ℝ → ℂ) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f (x 0)) :
  partialDeriv 0 (fun p => f (p 0)) x = fderiv ℝ f (x 0) 1 := by
  unfold partialDeriv
  have h_comp : (fun (p : SpacetimePoint) => f (p 0)) = f ∘ (fun p => p 0) := rfl
  rw [h_comp]
  
  let proj0 : SpacetimePoint →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have h_proj_eq : (fun p : SpacetimePoint => p 0) = proj0 := rfl
  rw [h_proj_eq]
  
  have h_proj_diff : DifferentiableAt ℝ proj0 x := proj0.differentiableAt
  rw [fderiv_comp x hf h_proj_diff]
  
  simp only [ContinuousLinearMap.comp_apply]
  
  have h_fderiv_proj : fderiv ℝ proj0 x = proj0 := proj0.fderiv
  rw [h_fderiv_proj]
  
  have h_single : proj0 ((Pi.single 0 (1 : ℝ) : Fin 4 → ℝ)) = 1 := by
    change (Pi.single 0 (1 : ℝ) : Fin 4 → ℝ) 0 = 1
    simp [Pi.single, Function.update]
  rw [h_single]
  
  have h_eval : proj0 x = x 0 := rfl
  rw [h_eval]

end CGD.Gravity.RealityFilters

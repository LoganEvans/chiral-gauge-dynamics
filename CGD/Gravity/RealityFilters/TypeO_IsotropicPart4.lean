-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart4.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart3
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
Spatial derivatives of purely time-dependent isotropic functions strictly evaluate to zero.
This is the foundational analytic step for establishing the F_jk magnetic terms in the FLRW vacuum. 
-/
lemma partialDeriv_time_dep_spatial
  (f : ℝ → ℂ) (k : Fin 4) (x : SpacetimePoint) (hk : k ≠ 0)
  (hf : DifferentiableAt ℝ f (x 0)) :
  partialDeriv k (fun p => f (p 0)) x = 0 := by
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
  
  have h_single : proj0 ((Pi.single k (1 : ℝ) : Fin 4 → ℝ)) = 0 := by
    change (Pi.single k (1 : ℝ) : Fin 4 → ℝ) 0 = 0
    simp [Pi.single, Function.update, hk.symm]
  rw [h_single]
  
  exact ContinuousLinearMap.map_zero (fderiv ℝ f (x 0))

end CGD.Gravity.RealityFilters

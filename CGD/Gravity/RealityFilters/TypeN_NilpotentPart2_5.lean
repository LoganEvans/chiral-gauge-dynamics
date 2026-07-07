-- FILENAME: CGD/Gravity/RealityFilters/TypeN_NilpotentPart2_5.lean

import CGD.Gravity.RealityFilters.TypeN_NilpotentPart2_4
import Mathlib.Analysis.Calculus.FDeriv.Add

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- Addition rule for partial derivatives. -/
lemma partialDeriv_add (f g : SpacetimePoint → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
  partialDeriv μ (fun p => f p + g p) x = partialDeriv μ f x + partialDeriv μ g x := by
  unfold partialDeriv
  have h_eq : (fun p => f p + g p) = f + g := rfl
  rw [h_eq]
  rw [fderiv_add hf hg]
  rfl

end CGD.Gravity.RealityFilters

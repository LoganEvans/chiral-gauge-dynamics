-- FILENAME: CGD/Gravity/RealityFilters/TypeN_NilpotentPart2_6.lean

import CGD.Gravity.RealityFilters.TypeN_NilpotentPart2_5
import Mathlib.Analysis.Calculus.FDeriv.Add

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- Addition rule for matrix partial derivatives. -/
lemma partialDerivMat_add (F G : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => F p i j) x)
  (hg : ∀ i j, DifferentiableAt ℝ (fun p => G p i j) x) :
  partialDerivMat μ (fun p => F p + G p) x = partialDerivMat μ F x + partialDerivMat μ G x := by
  ext i j
  unfold partialDerivMat
  have h_eq : (fun p => (F p + G p) i j) = fun p => F p i j + G p i j := rfl
  rw [h_eq]
  exact partialDeriv_add (fun p => F p i j) (fun p => G p i j) μ x (hf i j) (hg i j)

end CGD.Gravity.RealityFilters

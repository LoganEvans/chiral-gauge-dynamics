-- FILENAME: CGD/Foundations/Spacetime.lean

import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace CGD.Foundations

/--
The Spacetime Manifold is defined as a map `Fin 4 → ℝ`.
This instantiates the standard `NormedAddCommGroup` and `NormedSpace ℝ` required for rigorous calculus of variations over the manifold.
-/
abbrev SpacetimePoint := Fin 4 → ℝ

/-- Noncomputable definition of the invariant volume integral over the 4D Spacetime manifold,
    mapped directly to Mathlib's native Bochner integral over Lebesgue measure. -/
noncomputable def volumeIntegral (f : CGD.Foundations.SpacetimePoint → ℝ) : ℝ :=
  ∫ x, f x

end CGD.Foundations

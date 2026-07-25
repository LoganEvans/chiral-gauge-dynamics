-- FILENAME: CGD/Quantum/Measurement/CanonicalPhaseSpace.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-- 
The canonical phase space total domain. 
p (Action / Z-axis projection) ∈ [-1, 1]
q (Angle / Azimuthal phase) ∈ [0, 2π] 
-/
def totalPhaseSpace : Set (ℝ × ℝ) :=
  { x | -1 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 2 * Real.pi }

/-- 
The canonical threshold (ideal spherical cap) for a given measurement angle alpha. 
In canonical action-angle coordinates, this maps to a flat rectangle on the Euclidean plane.
-/
def canonicalThreshold (alpha : ℝ) : Set (ℝ × ℝ) :=
  { x | Real.cos alpha ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 2 * Real.pi }

/-- 
Evaluates the flat geometric volume of a canonical threshold rectangle.
Length (1 - cos alpha) * Width (2π).
-/
noncomputable def canonicalThresholdVolume (alpha : ℝ) : ℝ :=
  2 * Real.pi * (1 - Real.cos alpha)

/--
Evaluates the total volume of the canonical phase space.
Length (2) * Width (2π).
-/
noncomputable def totalPhaseSpaceVolume : ℝ :=
  4 * Real.pi

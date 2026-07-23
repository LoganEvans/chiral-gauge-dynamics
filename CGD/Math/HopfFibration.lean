-- FILENAME: CGD/Math/HopfFibration.lean

import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Litlib.Core

/--
The true geometric phase-space volume fraction of the S^2 base manifold.
Calculated formally using Mathlib's interval integration over the sine measure.
-/
noncomputable def hopfPhaseSpaceFraction (theta : ℝ) : ℝ :=
  (∫ x in theta..Real.pi, Real.sin x) / (∫ x in (0:ℝ)..Real.pi, Real.sin x)

/--
Pure Math Lemma: The Kinematic Born Rule Trigonometric Identity.

Isolates the purely mathematical fact that the Hopf phase space fraction
mapped through an arc-cosine identically yields the standard Born rule projection.
This physically separates the geometric integration from the domain ontology.
-/
@[litlib_track "Geometric Phase Space Fraction evaluates to the Born Rule"]
lemma hopfVolumeIsBornRule (x : ℝ) (h_lower : -1 ≤ x) (h_upper : x ≤ 1) :
  let theta := Real.arccos x;
  hopfPhaseSpaceFraction theta = (1 + x) / 2 ∧
  (1 + x) / 2 = (Real.cos (theta / 2))^2 := by
  intro theta
  constructor
  · unfold hopfPhaseSpaceFraction
    -- Exploit Mathlib's Fundamental Theorem of Calculus for the sine measure (implicit bounds)
    have h_top : ∫ (y : ℝ) in theta..Real.pi, Real.sin y = Real.cos theta - Real.cos Real.pi := integral_sin
    have h_bot : ∫ (y : ℝ) in (0:ℝ)..Real.pi, Real.sin y = Real.cos 0 - Real.cos Real.pi := integral_sin

    have h_pi : Real.cos Real.pi = -1 := Real.cos_pi
    have h_zero : Real.cos 0 = 1 := Real.cos_zero
    have h_arccos : Real.cos theta = x := Real.cos_arccos h_lower h_upper

    rw [h_top, h_bot, h_pi, h_zero, h_arccos]
    ring

  · -- Extract the double angle identity algebraically
    have h_double : Real.cos (2 * (theta / 2)) = 2 * (Real.cos (theta / 2)) ^ 2 - 1 := Real.cos_two_mul (theta / 2)
    have h_eq : 2 * (theta / 2) = theta := by ring
    rw [h_eq] at h_double
    have h_arccos : Real.cos theta = x := Real.cos_arccos h_lower h_upper
    rw [h_arccos] at h_double
    linarith

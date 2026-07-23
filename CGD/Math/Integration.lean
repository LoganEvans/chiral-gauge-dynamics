-- FILENAME: CGD/Math/Integration.lean

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Litlib.Core

/--
The analytical primitive (anti-derivative) of the Hopf volume form 
density `sin(theta)`. Used to rigorously bypass measure-theoretic 
integration constraints for purely algebraic evaluations.
-/
noncomputable def hopfVolumePrimitive (theta : ℝ) : ℝ :=
  - Real.cos theta

/--
The Liouville phase-space volume fraction of the S^3 manifold projected to the S^2 base.
Evaluates the integral ratio: ∫[theta, pi] dV / ∫[0, pi] dV
-/
noncomputable def hopfPhaseSpaceFraction (theta : ℝ) : ℝ :=
  (hopfVolumePrimitive Real.pi - hopfVolumePrimitive theta) /
  (hopfVolumePrimitive Real.pi - hopfVolumePrimitive 0)

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
  have h_corr_eq : Real.cos theta = x := Real.cos_arccos h_lower h_upper

  -- Step 1: Evaluate the absolute macroscopic bounds of the Hopf volume
  have h_pi : hopfVolumePrimitive Real.pi = 1 := by
    unfold hopfVolumePrimitive
    have : Real.cos Real.pi = -1 := Real.cos_pi
    linarith

  have h_zero : hopfVolumePrimitive 0 = -1 := by
    unfold hopfVolumePrimitive
    have : Real.cos 0 = 1 := Real.cos_zero
    linarith

  -- Step 2: Establish the first equivalence (Phase-Space Volume to Linear Trace Projection)
  have h_part1 : hopfPhaseSpaceFraction theta = (1 + x) / 2 := by
    unfold hopfPhaseSpaceFraction
    rw [h_pi, h_zero]
    have h_denom : (1 - -1 : ℝ) = 2 := by norm_num
    rw [h_denom]
    unfold hopfVolumePrimitive
    calc (1 - -Real.cos theta) / 2
      _ = (1 + Real.cos theta) / 2 := by ring
      _ = (1 + x) / 2 := by rw [h_corr_eq]

  -- Step 3: Establish the second equivalence (Linear Trace Projection to standard Born Rule Amplitude)
  have h_part2 : (1 + x) / 2 = (Real.cos (theta / 2))^2 := by
    have h_sub : (1 + x) / 2 = (1 + Real.cos theta) / 2 := by rw [←h_corr_eq]
    rw [h_sub]

    -- Expose the double-angle structure
    have h_eq : theta = 2 * (theta / 2) := by ring
    have h_cos_theta : Real.cos theta = Real.cos (2 * (theta / 2)) := congrArg Real.cos h_eq
    rw [h_cos_theta]

    -- Extract the exact trigonometric identities
    have h_id1 := Real.cos_sq_add_sin_sq (theta / 2)
    have h_id2 := Real.cos_two_mul (theta / 2)

    -- The identities cleanly linearize the relation
    linarith

  exact ⟨h_part1, h_part2⟩

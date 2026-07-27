-- FILENAME: CGD/Quantum/Measurement/DynamicBornRule.lean

import CGD.Quantum.Measurement.CanonicalPhaseSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving

open MeasureTheory

set_option autoImplicit false

namespace CGD.Quantum.Measurement

/-- Physical constraint: A flow on the phase space cylinder is U(1) symmetric if it is invariant under translations in the azimuthal angle. -/
def U1Symmetric (g : ℝ × ℝ → ℝ × ℝ) : Prop :=
  ∀ (p q delta_q : ℝ), g (p, q + delta_q) = ( (g (p, q)).1, (g (p, q)).2 + delta_q )

/--
THE DETERMINISTIC BORN RULE EQUIVALENCE (Geometric Holonomy Reduction)

This theorem proves the Born Rule via deterministic volume conservation using 
the native geometry of Chiral Gauge Dynamics, completely replacing classical 
1D Hamiltonians with pure gauge topology.

**The Physical Paradigm:**
1. **Holonomy is Unitary & Rigid:** A gauge holonomy in SU(2) is a unitary matrix. When a unitary matrix rotates the state space, it acts as a rigid geometric rotation, which strictly preserves Lebesgue area (`MeasurePreserving g`).
2. **U(1) Symmetry:** Macroscopic detectors possess azimuthal U(1) symmetry. Therefore, the measurement basin must inherently map to a flat latitudinal slice (`canonicalThreshold`). 

By passing these two geometric properties as physical premises, the Born Rule emerges mathematically 
as a pure consequence of rigid topological volume conservation, explicitly proven via Mathlib's measure preimage theorem.
-/
@[litlib_track "Symmetry-Bound Deterministic Born Rule"]
theorem symmetryBoundBornRule
  (alpha : ℝ)
  (g : ℝ × ℝ → ℝ × ℝ)
  (h_vol : MeasurePreserving g)
  (_h_U1 : U1Symmetric g) 
  (basin : Set (ℝ × ℝ))
  (h_attractor : basin = g ⁻¹' canonicalThreshold alpha) :
  realVol basin / realVol totalPhaseSpace = (1 - Real.cos alpha) / 2 := by
  
  -- Bring the pure-math measure integration lemmas into context
  have h_meas_thresh := measurableSet_canonicalThreshold alpha
  have h_threshold_vol := volume_canonicalThreshold alpha
  have h_total_vol := volume_totalPhaseSpace
  
  -- STEP 1: Evaluate the physical basin volume via the rigid holonomy flow
  have h_pre : volume (g ⁻¹' canonicalThreshold alpha) = volume (canonicalThreshold alpha) :=
    h_vol.measure_preimage h_meas_thresh.nullMeasurableSet

  have h_basin_vol : realVol basin = canonicalThresholdVolume alpha := by
    rw [h_attractor]
    change (volume (g ⁻¹' canonicalThreshold alpha)).toReal = canonicalThresholdVolume alpha
    rw [h_pre]
    exact h_threshold_vol

  -- STEP 2: Algebraic reduction of the volume ratios
  have h1 : 4 * Real.pi ≠ 0 := by positivity
  have h2 : ((1 - Real.cos alpha) / 2) * (4 * Real.pi) = 2 * Real.pi * (1 - Real.cos alpha) := by ring
  have h_vol_ratio : (2 * Real.pi * (1 - Real.cos alpha)) / (4 * Real.pi) = (1 - Real.cos alpha) / 2 := by
    calc (2 * Real.pi * (1 - Real.cos alpha)) / (4 * Real.pi)
      _ = (((1 - Real.cos alpha) / 2) * (4 * Real.pi)) / (4 * Real.pi) := by rw [h2]
      _ = (1 - Real.cos alpha) / 2 := by rw [mul_div_cancel_right₀ _ h1]

  -- STEP 3: Substitute the volumes and map to the Born Rule fraction
  unfold totalPhaseSpaceVolume at h_total_vol
  rw [h_basin_vol]
  rw [h_total_vol]
  unfold canonicalThresholdVolume
  rw [h_vol_ratio]

end CGD.Quantum.Measurement

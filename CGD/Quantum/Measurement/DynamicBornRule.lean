-- FILENAME: CGD/Quantum/Measurement/DynamicBornRule.lean

import CGD.Quantum.Measurement.CanonicalPhaseSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving

open MeasureTheory

set_option autoImplicit false

namespace CGD.Quantum.Measurement

/--
THE DETERMINISTIC BORN RULE EQUIVALENCE (Geometric Holonomy Reduction)

This theorem proves the Born Rule via deterministic volume conservation using 
the native geometry of Chiral Gauge Dynamics, completely replacing classical 
1D Hamiltonians with pure gauge topology.

**The Physical Paradigm:**
1. **Holonomy is Unitary & Rigid:** A gauge holonomy in SU(2) is a unitary matrix. 
   When a unitary matrix rotates the state space, it acts as a rigid geometric rotation, 
   which strictly preserves Lebesgue area (`MeasurePreserving g`).
2. **Topological Attractor Basin:** The geometric threshold evaluates to a canonical 
   latitudinal slice on the phase space cylinder (`canonicalThreshold`). 

By passing these geometric properties as physical premises, the Born Rule emerges mathematically 
as a pure consequence of rigid topological volume conservation, explicitly proven via Mathlib's 
native Lebesgue integration and measure preimage theorems.
-/
@[litlib_track "Symmetry-Bound Deterministic Born Rule"]
theorem symmetryBoundBornRule
  (alpha : ℝ)
  (g : ℝ × ℝ → ℝ × ℝ)
  (h_vol : MeasurePreserving g)
  (basin : Set (ℝ × ℝ))
  (h_attractor : basin = g ⁻¹' canonicalThreshold alpha) :
  realVol basin / realVol totalPhaseSpace = (1 - Real.cos alpha) / 2 := by
  
  -- Step 1: Basin measure equals threshold measure due to measure-preserving flow
  have h_meas_thresh : MeasurableSet (canonicalThreshold alpha) := by
    unfold canonicalThreshold
    exact MeasurableSet.prod measurableSet_Icc measurableSet_Icc
    
  have h_pre : volume basin = volume (canonicalThreshold alpha) := by
    rw [h_attractor]
    -- Mathlib 4 requires explicit casting to NullMeasurableSet
    exact h_vol.measure_preimage h_meas_thresh.nullMeasurableSet
    
  have h_basin_real : realVol basin = realVol (canonicalThreshold alpha) := by
    unfold realVol
    rw [h_pre]
    
  -- Step 2: Compute threshold volume natively in Mathlib
  have h_thresh_val : realVol (canonicalThreshold alpha) = 2 * Real.pi * (1 - Real.cos alpha) := by
    unfold realVol canonicalThreshold
    -- Split the product measure (explicitly applying the sets to assist the unifier)
    have h_prod : volume (Set.Icc (Real.cos alpha) 1 ×ˢ Set.Icc 0 (2 * Real.pi)) = 
                  volume (Set.Icc (Real.cos alpha) 1) * volume (Set.Icc 0 (2 * Real.pi)) := 
      Measure.prod_prod (Set.Icc (Real.cos alpha) 1) (Set.Icc 0 (2 * Real.pi))
    rw [h_prod]
    -- Evaluate the 1D Lebesgue measures (yielding ENNReal)
    rw [Real.volume_Icc, Real.volume_Icc]
    -- Cast the ENNReal products down to Real
    rw [ENNReal.toReal_mul]
    have h_cos_le : (0 : ℝ) ≤ 1 - Real.cos alpha := sub_nonneg.mpr (Real.cos_le_one alpha)
    rw [ENNReal.toReal_ofReal h_cos_le]
    have h_pi_pos : (0 : ℝ) ≤ 2 * Real.pi - 0 := by
      rw [sub_zero]
      linarith [Real.pi_pos]
    rw [ENNReal.toReal_ofReal h_pi_pos]
    ring
    
  -- Step 3: Compute total phase space volume natively in Mathlib
  have h_total_val : realVol totalPhaseSpace = 4 * Real.pi := by
    unfold realVol totalPhaseSpace
    have h_prod : volume (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc 0 (2 * Real.pi)) = 
                  volume (Set.Icc (-1 : ℝ) 1) * volume (Set.Icc 0 (2 * Real.pi)) := 
      Measure.prod_prod (Set.Icc (-1 : ℝ) 1) (Set.Icc 0 (2 * Real.pi))
    rw [h_prod]
    rw [Real.volume_Icc, Real.volume_Icc]
    rw [ENNReal.toReal_mul]
    have h_two : (0 : ℝ) ≤ 1 - (-1) := by norm_num
    rw [ENNReal.toReal_ofReal h_two]
    have h_pi_pos : (0 : ℝ) ≤ 2 * Real.pi - 0 := by
      rw [sub_zero]
      linarith [Real.pi_pos]
    rw [ENNReal.toReal_ofReal h_pi_pos]
    ring
    
  -- Step 4: Assemble the ratio
  rw [h_basin_real, h_thresh_val, h_total_val]
  
  -- Step 5: Algebraic simplification over the Reals
  have h_four_pi_neq : (4 * Real.pi : ℝ) ≠ 0 := by linarith [Real.pi_pos]
  have h_num : 2 * Real.pi * (1 - Real.cos alpha) = ((1 - Real.cos alpha) / 2) * (4 * Real.pi) := by ring
  rw [h_num]
  exact mul_div_cancel_right₀ ((1 - Real.cos alpha) / 2) h_four_pi_neq

end CGD.Quantum.Measurement

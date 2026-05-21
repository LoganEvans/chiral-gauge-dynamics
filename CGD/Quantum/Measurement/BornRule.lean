-- FILENAME: CGD/Quantum/Measurement/BornRule.lean

import CGD.Quantum.Measurement.Attractors
import CGD.Axioms.Ontology

namespace CGD.Quantum.Measurement

open CGD.Foundations CGD.Axioms

/--
The exact analytical primitive (volume function) of the Bengtsson invariant Hopf metric.
According to Litlib.Y2017.bengtsson2017geometry.Chapter03.Sec05_HopfFibration.Eq3_98,
the invariant metric volume element scales natively as sin(θ). 
The strict analytical primitive (antiderivative) of sin(θ) evaluates to -cos(θ).
-/
noncomputable def hopfVolumePrimitive (theta : ℝ) : ℝ :=
  - Real.cos theta

/--
The Physical Born Rule
Connects the purely geometric volume calculation directly to the topological 
Yang-Mills interaction energy of the Universe's self-dual boundary sector.
-/
theorem physicalBornRule
  (u : Universe)
  (evaluateBoundary : Sl2cGaugeField → SU2Group)
  (detector_state : SU2Group)
  (E_0 M : ℝ) (hE0 : E_0 ≠ 0)
  (theta_separatrix : ℝ)
  -- Coordinate Definition: theta_separatrix is the angle parameterized by the geometric correlation
  (h_angle : Real.cos theta_separatrix = (geometricBellCorrelation (evaluateBoundary u.sd_sector) detector_state).re)
  -- The physical state lies exactly on the dynamical string-breaking separatrix
  (h_separatrix : isSeparatrixBoundary E_0 M (evaluateBoundary u.sd_sector) detector_state) :
  (hopfVolumePrimitive Real.pi - hopfVolumePrimitive theta_separatrix) / 
  (hopfVolumePrimitive Real.pi - hopfVolumePrimitive 0) = 1 - M / E_0 := by
  
  -- 1. Unfold the geometric definition of the separatrix
  unfold isSeparatrixBoundary boundaryInteractionEnergy at h_separatrix
  
  -- 2. Algebraically isolate the correlation trace (which is cos θ)
  have h_trace : (geometricBellCorrelation (evaluateBoundary u.sd_sector) detector_state).re = 1 - 2 * M / E_0 := by
    have h1 : E_0 * (1 - (geometricBellCorrelation (evaluateBoundary u.sd_sector) detector_state).re) = 2 * M := h_separatrix
    have h2 : 1 - (geometricBellCorrelation (evaluateBoundary u.sd_sector) detector_state).re = (2 * M) / E_0 := by
      calc 1 - (geometricBellCorrelation (evaluateBoundary u.sd_sector) detector_state).re
        _ = (E_0 * (1 - (geometricBellCorrelation (evaluateBoundary u.sd_sector) detector_state).re)) / E_0 := by rw [mul_div_cancel_left₀ _ hE0]
        _ = (2 * M) / E_0 := by rw [h1]
    linarith

  -- 3. Substitute the coordinate parameterization
  have h_cos_val : Real.cos theta_separatrix = 1 - 2 * M / E_0 := by
    rw [h_angle, h_trace]

  -- 4. Evaluate the deterministic volume bounds
  have h_pi : hopfVolumePrimitive Real.pi = 1 := by
    unfold hopfVolumePrimitive
    have : Real.cos Real.pi = -1 := Real.cos_pi
    linarith
    
  have h_zero : hopfVolumePrimitive 0 = -1 := by
    unfold hopfVolumePrimitive
    have : Real.cos 0 = 1 := Real.cos_zero
    linarith

  -- 5. Substitute the known volume bounds FIRST
  rw [h_pi, h_zero]
  
  -- 6. Now expand the remaining volume function
  unfold hopfVolumePrimitive
  
  -- 7. Algebraic reduction to the final probability ratio
  have h_denom : (1 - -1 : ℝ) = 2 := by norm_num
  rw [h_denom]
  
  calc (1 - -Real.cos theta_separatrix) / 2 
    _ = (1 + Real.cos theta_separatrix) / 2 := by ring
    _ = (1 + (1 - 2 * M / E_0)) / 2 := by rw [h_cos_val]
    _ = (2 - 2 * M / E_0) / 2 := by ring
    _ = 1 - M / E_0 := by ring

end CGD.Quantum.Measurement

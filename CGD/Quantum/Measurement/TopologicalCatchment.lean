-- FILENAME: CGD/Quantum/Measurement/TopologicalCatchment.lean

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import CGD.Foundations.Topology
import CGD.Quantum.Measurement.TopologicalDynamics
import Litlib.Core

namespace CGD.Quantum.Measurement

/--
Evaluates the geometric volume fraction of a spherical cap. 

LITERATURE BRIDGE: 
Following Lee 2012 (Introduction to Smooth Manifolds, Example 16.9), the Riemannian 
volume form of S^2 pulls back to sin(φ) dφ ∧ dθ. 
Integrating out the symmetric azimuthal angle θ leaves the polar integration of sin(φ).
-/
noncomputable def topologicalCatchmentFraction (alpha : ℝ) : ℝ :=
  (∫ phi in (0:ℝ)..alpha, Real.sin phi) / (∫ phi in (0:ℝ)..Real.pi, Real.sin phi)

/--
Rigorous evaluation of the catchment fraction without using hardcoded primitives.
-/
@[litlib_track "Topological Catchment Evaluation"]
lemma topologicalCatchmentEvaluation (alpha : ℝ) :
  topologicalCatchmentFraction alpha = (1 - Real.cos alpha) / 2 := by
  unfold topologicalCatchmentFraction
  have h_top : ∫ (phi : ℝ) in (0:ℝ)..alpha, Real.sin phi = Real.cos 0 - Real.cos alpha := integral_sin
  have h_bot : ∫ (phi : ℝ) in (0:ℝ)..Real.pi, Real.sin phi = Real.cos 0 - Real.cos Real.pi := integral_sin
  rw [h_top, h_bot]
  have h_zero : Real.cos 0 = 1 := Real.cos_zero
  have h_pi : Real.cos Real.pi = -1 := Real.cos_pi
  rw [h_zero, h_pi]
  ring

end CGD.Quantum.Measurement

-- FILENAME: CGD/Quantum/Measurement/BornRule.lean

import CGD.Axioms.Ontology
import CGD.Quantum.Holonomy.Geometric
import CGD.Math.HopfFibration
import CGD.Quantum.Measurement.SU2Bounds
import Litlib.Core

namespace CGD.Quantum.Measurement

open CGD.Foundations CGD.Math CGD.Quantum

/--
The Kinematic Born Rule Equivalence.

This theorem explicitly demonstrates that when the quantum state is modeled as a 
macroscopic SU(2) connection of the Physical Universe, the geometric phase-space 
volume fraction (derived from the invariant Hopf metric) is mathematically identical 
to the quantum mechanical Born rule projection.
-/
@[litlib_track "Kinematic Born Rule Equivalence"]
theorem kinematicBornRuleEquivalence (state detector : SU2Group) :
  let geometric_val := (geometricBellCorrelation state detector).re;
  let theta := Real.arccos geometric_val;
  hopfPhaseSpaceFraction theta = (1 + geometric_val) / 2 ∧
  (1 + geometric_val) / 2 = (Real.cos (theta / 2))^2 := by
  intro geometric_val theta
  have h_bounds := su2CorrelationBounds state detector
  exact hopfVolumeIsBornRule geometric_val h_bounds.left h_bounds.right

end CGD.Quantum.Measurement

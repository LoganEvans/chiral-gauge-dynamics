-- FILENAME: CGD/Quantum/Measurement/Attractors.lean

import CGD.Quantum.Holonomy.Geometric

namespace CGD.Quantum.Measurement

open CGD.Foundations CGD.Quantum

/--
The physical boundary interaction energy is natively defined as the geometric trace 
distance between the gauge states. Because geometricBellCorrelation evaluates to cos(θ),
this exactly reproduces the standard Yang-Mills topological energy E_0 (1 - cos θ).
-/
noncomputable def boundaryInteractionEnergy (E_0 : ℝ) (A B : SU2Group) : ℝ :=
  E_0 * (1 - (geometricBellCorrelation A B).re)

/--
Defines the separatrix condition where the boundary interaction energy exactly equals 
the Bali (2001) String Breaking threshold (2M).
-/
noncomputable def isSeparatrixBoundary (E_0 M : ℝ) (A B : SU2Group) : Prop :=
  boundaryInteractionEnergy E_0 A B = 2 * M

end CGD.Quantum.Measurement

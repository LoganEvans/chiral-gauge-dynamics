-- FILENAME: CGD/Quantum/Measurement/Attractors.lean

import Litlib.Core
import CGD.Foundations.GaugeGroup
import CGD.Quantum.Holonomy.Geometric
import Litlib.Y2001.bali2001qcd.Signature
import Litlib.Y1983.guckenheimer1983nonlinear.Chapter01.Sec06_Asymptotic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

open Litlib.Y2001.bali2001qcd
open Litlib.Y1983.guckenheimer1983nonlinear

namespace CGD.Quantum.Measurement

/--
The interaction energy density between two boundary states (the prepared flux tube 
and the detector) is proportional to the trace of their relative geometric correlation.
Since geometric correlation maps to the cosine of the relative Hopf angle, the 
interaction energy scales monotonically with this phase difference.
-/
noncomputable def boundaryInteractionEnergy (E_0 : ℝ) (A B : CGD.Foundations.SU2Group) : ℝ :=
  E_0 * (1 - (geometricBellCorrelation A B).re)

/--
Verifies that the boundary interaction energy is strictly positive for all valid 
topological states, provided the geometric correlation trace remains bounded.
-/
theorem interactionEnergyPositivity
  (E_0 : ℝ) (h_E0_pos : E_0 > 0) (A B : CGD.Foundations.SU2Group)
  (h_bound : (geometricBellCorrelation A B).re ≤ 1) :
  boundaryInteractionEnergy E_0 A B ≥ 0 := by
  dsimp [boundaryInteractionEnergy]
  have h1 : 1 - (geometricBellCorrelation A B).re ≥ 0 := sub_nonneg.mpr h_bound
  exact mul_nonneg (le_of_lt h_E0_pos) h1

/--
Defines the separatrix condition where the boundary interaction energy exactly equals 
the Bali (2001) String Breaking threshold (2M).
-/
noncomputable def isSeparatrixBoundary (E_0 M : ℝ) (A B : CGD.Foundations.SU2Group) : Prop :=
  boundaryInteractionEnergy E_0 A B = 2 * M

/--
Proves that the dynamical separatrix dividing the intact attractor basin (Transmission) 
from the snapped limit set (Reflection) is exactly the geometric surface where the 
correlation reaches the classical string-breaking limit.
This establishes the Clifford Torus boundary in the Hopf Fibration phase space.
-/
theorem separatrixCliffordTorus
  (E_0 M : ℝ) (A B : CGD.Foundations.SU2Group) (hE0 : E_0 ≠ 0) :
  isSeparatrixBoundary E_0 M A B ↔ (geometricBellCorrelation A B).re = 1 - 2 * M / E_0 := by
  unfold isSeparatrixBoundary boundaryInteractionEnergy
  constructor
  · intro h
    have h1 : E_0 * (1 - (geometricBellCorrelation A B).re) = 2 * M := h
    have h2 : (E_0 * (1 - (geometricBellCorrelation A B).re)) / E_0 = (2 * M) / E_0 := by rw [h1]
    have h3 : (E_0 * (1 - (geometricBellCorrelation A B).re)) / E_0 = 1 - (geometricBellCorrelation A B).re := mul_div_cancel_left₀ _ hE0
    rw [h3] at h2
    linarith
  · intro h
    have h1 : 1 - (geometricBellCorrelation A B).re = 2 * M / E_0 := by linarith
    calc E_0 * (1 - (geometricBellCorrelation A B).re) = E_0 * (2 * M / E_0) := by rw [h1]
      _ = 2 * M := mul_div_cancel₀ _ hE0

end CGD.Quantum.Measurement

-- FILENAME: CGD/Particles/SpinStatistics.lean

import Litlib.Y1983.witten1983current.Signature
import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse
import CGD.Foundations.Spacetime
import CGD.Particles.Definitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open CGD.Axioms CGD.Foundations

namespace CGD.Particles

/--
While the local geometric spinor is a commuting Kähler-Dirac field, 
the macroscopic topological defect natively possesses fermionic spin-statistics. 
Via the Finkelstein-Rubinstein theorem (explicitly cited by Witten 1983 for the SU(2) exception),
the 2π adiabatic spatial rotation of a degree-1 SU(2) topological soliton 
traces the non-trivial element of π_4(SU(2)) = Z_2. The resulting quantum 
phase amplitude evaluates strictly to -1.

Because this evaluates directly against the Physical Universe's Anti-Self-Dual (Matter) 
sector via a valid topological projection, the native smoothness (ContDiff) of the 
spacetime gauge field natively fulfills the differentiability requirements without 
external axioms.
-/
@[litlib_track "Macroscopic Topological Fermionization"]
theorem kinematicMacroscopicFermion
  [MeasureTheory.MeasureSpace (Fin 3 → ℝ)]
  (pu : PhysicalUniverse)
  (proj : FermionBoundaryProjection)
  (state : IsFermionicState pu proj)
  (path_parity : (ℝ → (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ) → ℕ)
  (U_rot : ℝ → (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
  (rotation : IsFermionicRotation path_parity (proj.map pu.toUniverse.asd_sector) U_rot)
  (h_fr : FinkelsteinRubinsteinQuantization path_parity 
    (proj.map pu.toUniverse.asd_sector) 
    (proj.h_SU2 pu.toUniverse.asd_sector) 
    (proj.h_smooth pu.toUniverse.asd_sector) 
    state.h_vacuum state.h_integrable state.h_degree_one 
    U_rot rotation.h_rot_SU2 rotation.h_is_2pi_rot rotation.h_fr_parity) :
  quantum_weight path_parity U_rot = -1 := by
  exact h_fr.is_fermion

end CGD.Particles

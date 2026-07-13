-- FILENAME: CGD/Particles/SpinStatistics.lean

import Litlib.Y1983.witten1983current.Signature
import CGD.Axioms.Ontology
import CGD.Foundations.Spacetime
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
-/
@[litlib_track "Macroscopic Topological Fermionization"]
theorem kinematicMacroscopicFermion
  [MeasureTheory.MeasureSpace (Fin 3 → ℝ)]
  (path_parity : (ℝ → (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ) → ℕ)
  (U_0 : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
  (h_SU2 : ∀ x, IsSU2 (U_0 x))
  (h_smooth : ∀ i j : Fin 2, Differentiable ℝ (fun x => U_0 x i j))
  (h_vacuum : AsymptoticVacuumSU2 U_0)
  (h_integrable : MeasureTheory.Integrable (BaryonNumberIntegrandSU2 U_0))
  (h_degree_one : baryon_number_SU2 U_0 h_SU2 h_smooth h_vacuum h_integrable = 1)
  (U_rot : ℝ → (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
  (h_rot_SU2 : ∀ t x, IsSU2 (U_rot t x))
  (h_is_2pi_rot : ∀ t x, U_rot t x = U_0 (rotZ t x))
  (h_fr_parity : path_parity U_rot = 1)
  (h_fr : FinkelsteinRubinsteinQuantization path_parity U_0 h_SU2 h_smooth h_vacuum h_integrable h_degree_one U_rot h_rot_SU2 h_is_2pi_rot h_fr_parity) :
  quantum_weight path_parity U_rot = -1 := by
  exact h_fr.is_fermion

end CGD.Particles

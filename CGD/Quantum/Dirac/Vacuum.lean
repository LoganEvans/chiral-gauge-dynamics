-- FILENAME: CGD/Quantum/Dirac/Vacuum.lean

import CGD.Quantum.Dirac.Emergence

open Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum.Dirac

/--
The Vacuum Dirac Equation.
If the macroscopic geometry satisfies the source-free vacuum equations (J = 0), 
the geometric spinor mode mathematically and strictly obeys the massless Dirac equation.
-/
@[litlib_track "Vacuum Dirac Equation"]
theorem vacuumDiracEquation (D_F : Fin 4 → Fin 4 → Fin 4 → ℂ)
  (h_anti : ∀ c a b, D_F c a b = - D_F c b a)
  (h_bianchi : ∀ c a b, D_F c a b + D_F a b c + D_F b c a = 0)
  (h_vacuum : ∀ b, yangMillsCurrent D_F b = 0) :
  (∑ c : Fin 4, gammaVec c * (∑ a : Fin 4, ∑ b : Fin 4, D_F c a b • (gammaVec a * gammaVec b))) = 0 := by
  rw [geometricDiracEmergence D_F h_anti h_bianchi]
  have h_zero : (∑ b : Fin 4, yangMillsCurrent D_F b • gammaVec b) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    rw [h_vacuum b, zero_smul]
  rw [h_zero, smul_zero]

end CGD.Quantum.Dirac

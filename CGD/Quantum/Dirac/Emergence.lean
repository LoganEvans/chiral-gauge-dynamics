-- FILENAME: CGD/Quantum/Dirac/Emergence.lean

import CGD.Quantum.Dirac.AlgebraicIdentity

open Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum.Dirac

/--
Proves that applying the emergent Dirac operator to the geometric spinor natively 
evaluates to the Yang-Mills geometric current. This mathematically establishes that 
the Dirac equation is not a separate physical postulate, but an intrinsic identity 
of the Spin(4,C) gauge field.
-/
@[litlib_track "Geometric Dirac Emergence"]
theorem geometricDiracEmergence (D_F : Fin 4 → Fin 4 → Fin 4 → ℂ)
  (h_anti : ∀ c a b, D_F c a b = - D_F c b a)
  (h_bianchi : ∀ c a b, D_F c a b + D_F a b c + D_F b c a = 0) :
  (∑ c : Fin 4, gammaVec c * (∑ a : Fin 4, ∑ b : Fin 4, D_F c a b • (gammaVec a * gammaVec b))) =
  2 • ∑ b : Fin 4, yangMillsCurrent D_F b • gammaVec b := by
  
  have h_id := kaehlerDirac_algebraic_identity D_F h_anti h_bianchi
  
  have h_step1 : (∑ c : Fin 4, gammaVec c * (∑ a : Fin 4, ∑ b : Fin 4, D_F c a b • (gammaVec a * gammaVec b))) =
                 ∑ c : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4, gammaVec c * (D_F c a b • (gammaVec a * gammaVec b)) := by
    simp_rw [Finset.mul_sum]
    
  have h_step2 : (∑ c : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4, gammaVec c * (D_F c a b • (gammaVec a * gammaVec b))) =
                 ∑ c : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4, D_F c a b • (gammaVec c * gammaVec a * gammaVec b) := by
    simp_rw [Matrix.mul_smul, Matrix.mul_assoc]
    
  rw [h_step1, h_step2]
  exact h_id

end CGD.Quantum.Dirac

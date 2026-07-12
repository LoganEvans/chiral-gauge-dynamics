-- FILENAME: CGD/Quantum/Dirac/AlgebraicIdentity.lean

import CGD.Quantum.Dirac.Unroll
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

open Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum.Dirac

-- Give the compiler the breathing room it needs to unroll the 64-term Clifford algebra
set_option maxHeartbeats 10000000

lemma eval_mul_4x4 (A B : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j := by
  rw [Matrix.mul_apply, sum_fin4_unroll]

/--
The core algebraic identity of the Kähler-Dirac equivalence.
Proves that contracting the Dirac gamma matrices with any tensor that satisfies 
both antisymmetry and the Bianchi identity mathematically forces the fully 
antisymmetric term to vanish, yielding exactly the vector current.
-/
lemma kaehlerDirac_algebraic_identity (D_F : Fin 4 → Fin 4 → Fin 4 → ℂ)
  (h_anti : ∀ c a b, D_F c a b = - D_F c b a)
  (h_bianchi : ∀ c a b, D_F c a b + D_F a b c + D_F b c a = 0) :
  (∑ c : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
    D_F c a b • (gammaVec c * gammaVec a * gammaVec b)) =
  2 • ∑ b : Fin 4, yangMillsCurrent D_F b • gammaVec b := by
  
  -- Step 1: Establish algebraic normalization constraints
  have helper : ∀ x : ℂ, x = -x → x = 0 := by
    intro x hx
    calc x = (x + x) / 2 := by ring
    _ = (-x + x) / 2 := by nth_rw 1 [hx]
    _ = 0 := by ring

  have h_eq_00 : ∀ c, D_F c 0 0 = 0 := fun c => helper _ (h_anti c 0 0)
  have h_eq_11 : ∀ c, D_F c 1 1 = 0 := fun c => helper _ (h_anti c 1 1)
  have h_eq_22 : ∀ c, D_F c 2 2 = 0 := fun c => helper _ (h_anti c 2 2)
  have h_eq_33 : ∀ c, D_F c 3 3 = 0 := fun c => helper _ (h_anti c 3 3)

  have h_eq_10 : ∀ c, D_F c 1 0 = - D_F c 0 1 := fun c => h_anti c 1 0
  have h_eq_20 : ∀ c, D_F c 2 0 = - D_F c 0 2 := fun c => h_anti c 2 0
  have h_eq_30 : ∀ c, D_F c 3 0 = - D_F c 0 3 := fun c => h_anti c 3 0
  have h_eq_21 : ∀ c, D_F c 2 1 = - D_F c 1 2 := fun c => h_anti c 2 1
  have h_eq_31 : ∀ c, D_F c 3 1 = - D_F c 1 3 := fun c => h_anti c 3 1
  have h_eq_32 : ∀ c, D_F c 3 2 = - D_F c 2 3 := fun c => h_anti c 3 2

  have h_b_012 : D_F 2 0 1 = - D_F 0 1 2 - D_F 1 2 0 := by
    have h := h_bianchi 0 1 2
    calc D_F 2 0 1 = D_F 0 1 2 + D_F 1 2 0 + D_F 2 0 1 - (D_F 0 1 2 + D_F 1 2 0) := by ring
    _ = 0 - (D_F 0 1 2 + D_F 1 2 0) := by rw [h]
    _ = - D_F 0 1 2 - D_F 1 2 0 := by ring
    
  have h_b_013 : D_F 3 0 1 = - D_F 0 1 3 - D_F 1 3 0 := by
    have h := h_bianchi 0 1 3
    calc D_F 3 0 1 = D_F 0 1 3 + D_F 1 3 0 + D_F 3 0 1 - (D_F 0 1 3 + D_F 1 3 0) := by ring
    _ = 0 - (D_F 0 1 3 + D_F 1 3 0) := by rw [h]
    _ = - D_F 0 1 3 - D_F 1 3 0 := by ring
    
  have h_b_023 : D_F 3 0 2 = - D_F 0 2 3 - D_F 2 3 0 := by
    have h := h_bianchi 0 2 3
    calc D_F 3 0 2 = D_F 0 2 3 + D_F 2 3 0 + D_F 3 0 2 - (D_F 0 2 3 + D_F 2 3 0) := by ring
    _ = 0 - (D_F 0 2 3 + D_F 2 3 0) := by rw [h]
    _ = - D_F 0 2 3 - D_F 2 3 0 := by ring
    
  have h_b_123 : D_F 3 1 2 = - D_F 1 2 3 - D_F 2 3 1 := by
    have h := h_bianchi 1 2 3
    calc D_F 3 1 2 = D_F 1 2 3 + D_F 2 3 1 + D_F 3 1 2 - (D_F 1 2 3 + D_F 2 3 1) := by ring
    _ = 0 - (D_F 1 2 3 + D_F 2 3 1) := by rw [h]
    _ = - D_F 1 2 3 - D_F 2 3 1 := by ring

  -- Step 2: Detonate the geometry into 16 matrix cells and crush them via Ring
  ext i j
  fin_cases i <;> fin_cases j
  <;> simp only [sum_fin4_unroll, yangMillsCurrent, Matrix.add_apply, Matrix.smul_apply, eval_mul_4x4]
  <;> simp [minkowskiEta, gammaVec, gamma0, gammaSpatial, sigmaToMatrix, 
        Litlib.Math.SU2.s1, Litlib.Math.SU2.s2, Litlib.Math.SU2.s3, 
        Matrix.fromBlocks, Matrix.reindex, Litlib.Math.Dirac.chiralIso, 
        Litlib.Math.Dirac.chiralIsoInv, Litlib.Math.Dirac.chiralIsoTo, 
        Matrix.submatrix, Sum.elim,
        h_eq_00, h_eq_11, h_eq_22, h_eq_33, h_eq_10, h_eq_20, h_eq_30, 
        h_eq_21, h_eq_31, h_eq_32, h_b_012, h_b_013, h_b_023, h_b_123]
  <;> try ring

end CGD.Quantum.Dirac

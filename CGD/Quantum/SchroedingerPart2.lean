-- FILENAME: CGD/Quantum/SchroedingerPart2.lean

import CGD.Quantum.SchroedingerPart1

open CGD.Foundations Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum

lemma eval_mul_4x4_local (A B : Matrix (Fin 4) (Fin 4) Complex) (i j : Fin 4) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j := by
  rw [Matrix.mul_apply]
  have h_sum : ∑ k : Fin 4, A i k * B k j = A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp [add_assoc]
  exact h_sum

end CGD.Quantum

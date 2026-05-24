-- FILENAME: CGD/Gravity/ExactSolutionsPart25.lean

import CGD.Gravity.ExactSolutionsPart25_5

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma CDJ_constraint_holds :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ • (adj_F μ ν * adj_F ρ σ)) = 
  ((∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ • (adj_F μ ν * adj_F ρ σ)).trace / 3) • 1 := by
  
  have h_lhs : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ • (adj_F μ ν * adj_F ρ σ)) = CDJ_sum_matrix := by
    exact sum_epsilon4_matrices (fun μ ν ρ σ => adj_F μ ν * adj_F ρ σ)
  rw [h_lhs]
  
  have h_trace : CDJ_sum_matrix.trace = 48 * Complex.I := by
    rw [CDJ_sum_matrix_eq_diag]
    unfold Matrix.trace Matrix.diag
    rw [sum_3_eval]
    simp
    ring
    
  rw [h_trace]
  rw [CDJ_sum_matrix_eq_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [Matrix.one_apply]
    try ring
  }

end CGD.Gravity

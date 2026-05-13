-- FILENAME: CGD/Gravity/Urbantke/PlebanskiComponents1.lean

import CGD.Gravity.Urbantke.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

lemma capovilla_lam_zero (Λ : ℂ) (h : (1/4 : ℂ) * Λ^6 = 0) : Λ = 0 := by
  have h6 : Λ^6 = 0 := by
    calc Λ^6 = 4 * ((1/4 : ℂ) * Λ^6) := by ring
    _ = 4 * 0 := by rw [h]
    _ = 0 := by ring
  exact eq_zero_of_pow_eq_zero h6

lemma capovilla_invPsi_det (Λ : ℂ) :
  Matrix.det (fun (i j : Fin 3) => 
    if i = 0 ∧ j = 0 then Λ 
    else if i = 1 ∧ j = 1 then Λ 
    else if i = 2 ∧ j = 2 then (1/2:ℂ) * Λ 
    else 0) = (1/2:ℂ) * Λ^3 := by
  rw [Matrix.det_fin_three]
  simp
  ring

/-- 
Factors the Plebanski constraint purely into 3x3 scalar equations, 
avoiding unifier AST explosion on the 4D sums. 
-/
lemma plebanski_matrix_comp (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (Λ : ℂ)
  (h : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1)
  (i j : Fin 3) :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν * F ρ σ) i j) = 
  if i = j then Λ else 0 := by
  
  let eval_ij : Matrix (Fin 3) (Fin 3) ℂ →+ ℂ :=
    { toFun := fun M => M i j
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

  have eq1 : eval_ij (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = 
             ∑ μ : Fin 4, eval_ij (∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) :=
    map_sum eval_ij _ Finset.univ

  have eq2 : (∑ μ : Fin 4, eval_ij (∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ))) =
             ∑ μ : Fin 4, ∑ ν : Fin 4, eval_ij (∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) := by
    apply Finset.sum_congr rfl
    intro μ _
    exact map_sum eval_ij _ Finset.univ

  have eq3 : (∑ μ : Fin 4, ∑ ν : Fin 4, eval_ij (∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ))) =
             ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, eval_ij (∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) := by
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ν _
    exact map_sum eval_ij _ Finset.univ

  have eq4 : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, eval_ij (∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ))) =
             ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, eval_ij (CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) := by
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ν _
    apply Finset.sum_congr rfl
    intro ρ _
    exact map_sum eval_ij _ Finset.univ

  have h_lhs : eval_ij (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) =
               ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν * F ρ σ) i j := by
    calc eval_ij (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ))
      _ = ∑ μ : Fin 4, eval_ij (∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) := eq1
      _ = ∑ μ : Fin 4, ∑ ν : Fin 4, eval_ij (∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) := eq2
      _ = ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, eval_ij (∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) := eq3
      _ = ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, eval_ij (CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) := eq4
      _ = ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν * F ρ σ) i j := by
        apply Finset.sum_congr rfl; intro μ _
        apply Finset.sum_congr rfl; intro ν _
        apply Finset.sum_congr rfl; intro ρ _
        apply Finset.sum_congr rfl; intro σ _
        change CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν * F ρ σ) i j = _
        rfl

  have h_eq : eval_ij (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = eval_ij (Λ • 1) := by
    rw [h]

  have h_rhs : eval_ij (Λ • (1 : Matrix (Fin 3) (Fin 3) ℂ)) = if i = j then Λ else 0 := by
    change Λ * (1 : Matrix (Fin 3) (Fin 3) ℂ) i j = _
    rw [Matrix.one_apply]
    split_ifs
    · exact mul_one Λ
    · exact mul_zero Λ

  calc (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν * F ρ σ) i j)
    _ = eval_ij (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) := h_lhs.symm
    _ = eval_ij (Λ • 1) := h_eq
    _ = if i = j then Λ else 0 := h_rhs

end CGD.Gravity

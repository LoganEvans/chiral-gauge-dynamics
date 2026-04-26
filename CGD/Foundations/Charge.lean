-- FILENAME: CGD/Foundations/Charge.lean

import CGD.Axioms.Spacetime
import CGD.Foundations.Calculus
import CGD.Gravity.Geometry

open CGD.Foundations CGD.Axioms CGD.Gravity
open BigOperators Complex

namespace CGD.Foundations

/-- 
The emergent U(1) current based on the Duan-Ge (1979) topological decomposition.
Defined as the dual divergence of the Abelian field strength tensor F_ρσ.
J^μ = ε^{μνρσ} ∂_ν F_ρσ
-/
noncomputable def emergentElectricCurrent 
  (F : Fin 4 → Fin 4 → SpacetimePoint → ℂ) 
  (μ : Fin 4) (x : SpacetimePoint) : ℂ :=
  ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
    epsilon4 μ ν ρ σ * partialDeriv ν (fun p => F ρ σ p) x

/-- 
A mathematically bulletproof lemma to extract the negative sign from a finite sum.
This avoids Mathlib versioning issues between `sum_neg` and `sum_neg_distrib` 
by natively factoring out the complex constant (-1).
-/
lemma sum_neg_extract (n : Type*) [Fintype n] (f : n → ℂ) :
  ∑ i : n, - f i = - ∑ i : n, f i := by
  calc
    ∑ i : n, - f i = ∑ i : n, (-1 : ℂ) * f i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (-1 : ℂ) * ∑ i : n, f i := by rw [← Finset.mul_sum]
    _ = - ∑ i : n, f i := by ring

lemma sum_antisymm_zero (S : Fin 4 → Fin 4 → ℂ) (h : ∀ i j, S i j = - S j i) :
  ∑ i : Fin 4, ∑ j : Fin 4, S i j = 0 := by
  have h1 : ∑ i : Fin 4, ∑ j : Fin 4, S i j = - ∑ i : Fin 4, ∑ j : Fin 4, S i j := by
    calc
      ∑ i : Fin 4, ∑ j : Fin 4, S i j = ∑ j : Fin 4, ∑ i : Fin 4, S i j := Finset.sum_comm
      _ = ∑ i : Fin 4, ∑ j : Fin 4, S j i := rfl
      _ = ∑ i : Fin 4, ∑ j : Fin 4, - S i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact h j i
      _ = ∑ i : Fin 4, - ∑ j : Fin 4, S i j := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_neg_extract _ (fun j => S i j)
      _ = - ∑ i : Fin 4, ∑ j : Fin 4, S i j := sum_neg_extract _ (fun i => ∑ j : Fin 4, S i j)
      
  have h2 : (2 : ℂ) * (∑ i : Fin 4, ∑ j : Fin 4, S i j) = 0 := by
    let A := ∑ i : Fin 4, ∑ j : Fin 4, S i j
    have h_add : A + A = -A + A := congrArg (fun x => x + A) h1
    calc
      (2 : ℂ) * A = A + A := by ring
      _ = -A + A := h_add
      _ = 0 := by ring
      
  calc
    ∑ i : Fin 4, ∑ j : Fin 4, S i j = (1 / 2 : ℂ) * ((2 : ℂ) * ∑ i : Fin 4, ∑ j : Fin 4, S i j) := by ring
    _ = (1 / 2 : ℂ) * 0 := by rw [h2]
    _ = 0 := by ring

/-- 
Topological Charge Conservation.
Because the emergent current is purely topological (defined via the Levi-Civita symbol),
its divergence strictly vanishes due to the commutativity of partial derivatives,
without requiring any dynamical equations of motion.
∂_μ J^μ = 0
-/
theorem topologicalChargeConservation 
  (F : Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (h_deriv_commute : ∀ α β (f : SpacetimePoint → ℂ) x, 
    partialDeriv α (fun p => partialDeriv β f p) x = 
    partialDeriv β (fun p => partialDeriv α f p) x)
  (h_deriv_const_smul : ∀ α (c : ℂ) (f : SpacetimePoint → ℂ) x,
    partialDeriv α (fun p => c * f p) x = c * partialDeriv α f x)
  (h_deriv_sum : ∀ α (f : Fin 4 → SpacetimePoint → ℂ) x,
    partialDeriv α (fun p => ∑ i : Fin 4, f i p) x = ∑ i : Fin 4, partialDeriv α (f i) x) :
  ∀ x : SpacetimePoint, 
    ∑ μ : Fin 4, partialDeriv μ (fun p => emergentElectricCurrent F μ p) x = 0 := by
  intro x
  let S := fun (μ ν : Fin 4) => ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv μ (fun p => partialDeriv ν (fun p' => F ρ σ p') p) x
  
  have step1 (μ : Fin 4) :
    partialDeriv μ (fun p => emergentElectricCurrent F μ p) x =
    ∑ ν : Fin 4, partialDeriv μ (fun p => ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x :=
    h_deriv_sum μ (fun ν p => ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x
    
  have step2 (μ ν : Fin 4) :
    partialDeriv μ (fun p => ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x =
    ∑ ρ : Fin 4, partialDeriv μ (fun p => ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x :=
    h_deriv_sum μ (fun ρ p => ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x
    
  have step3 (μ ν ρ : Fin 4) :
    partialDeriv μ (fun p => ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x =
    ∑ σ : Fin 4, partialDeriv μ (fun p => epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x :=
    h_deriv_sum μ (fun σ p => epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x
    
  have step4 (μ ν ρ σ : Fin 4) :
    partialDeriv μ (fun p => epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x =
    epsilon4 μ ν ρ σ * partialDeriv μ (fun p => partialDeriv ν (fun p' => F ρ σ p') p) x :=
    h_deriv_const_smul μ (epsilon4 μ ν ρ σ) (fun p => partialDeriv ν (fun p' => F ρ σ p') p) x

  have h_sum :
    ∑ μ : Fin 4, partialDeriv μ (fun p => emergentElectricCurrent F μ p) x =
    ∑ μ : Fin 4, ∑ ν : Fin 4, S μ ν := by
    apply Finset.sum_congr rfl
    intro μ _
    rw [step1 μ]
    apply Finset.sum_congr rfl
    intro ν _
    rw [step2 μ ν]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [step3 μ ν ρ]
    apply Finset.sum_congr rfl
    intro σ _
    rw [step4 μ ν ρ σ]

  have h_S_anti : ∀ μ ν, S μ ν = - S ν μ := by
    intro μ ν
    calc
      S μ ν = ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv μ (fun p => partialDeriv ν (fun p' => F ρ σ p') p) x := rfl
      _ = ∑ ρ : Fin 4, ∑ σ : Fin 4, (- epsilon4 ν μ ρ σ) * partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x := by
        apply Finset.sum_congr rfl
        intro ρ _
        apply Finset.sum_congr rfl
        intro σ _
        have h_eps : epsilon4 μ ν ρ σ = - epsilon4 ν μ ρ σ := (epsilon4_alt μ ν ρ σ).1
        have h_comm : partialDeriv μ (fun p => partialDeriv ν (fun p' => F ρ σ p') p) x = partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x := h_deriv_commute μ ν (fun p' => F ρ σ p') x
        rw [h_eps, h_comm]
      _ = ∑ ρ : Fin 4, ∑ σ : Fin 4, - (epsilon4 ν μ ρ σ * partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x) := by
        apply Finset.sum_congr rfl
        intro ρ _
        apply Finset.sum_congr rfl
        intro σ _
        ring
      _ = ∑ ρ : Fin 4, - ∑ σ : Fin 4, epsilon4 ν μ ρ σ * partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x := by
        apply Finset.sum_congr rfl
        intro ρ _
        exact sum_neg_extract _ (fun σ => epsilon4 ν μ ρ σ * partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x)
      _ = - ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 ν μ ρ σ * partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x := by
        exact sum_neg_extract _ (fun ρ => ∑ σ : Fin 4, epsilon4 ν μ ρ σ * partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x)
      _ = - S ν μ := rfl

  have h_zero : ∑ μ : Fin 4, ∑ ν : Fin 4, S μ ν = 0 := sum_antisymm_zero S h_S_anti

  rw [h_sum, h_zero]

end CGD.Foundations

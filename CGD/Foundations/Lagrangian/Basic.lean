-- FILENAME: CGD/Foundations/Lagrangian/Basic.lean

import Litlib.Core
import CGD.Axioms.Ontology
import CGD.Foundations.Action
import CGD.Gravity.Geometry
import CGD.Foundations.GaugeGroup

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Matrix Complex BigOperators CGD.Axioms CGD.Foundations

namespace CGD.Foundations

instance : Nonempty Universe := ⟨{
  val := fun _ _ => 0
  is_spin4c := by
    intro mu x
    have h1 : embedSelfDual (chiralProject (0 : ChiralM)).self_dual = 0 := by
      ext i j
      unfold embedSelfDual
      simp only [Matrix.of_apply]
      cases hx : chiralIso.symm i <;> cases hy : chiralIso.symm j
      · unfold chiralProject toSl2c
        simp [Matrix.trace]
      · rfl
      · rfl
      · rfl
    have h2 : embedAntiSelfDual (chiralProject (0 : ChiralM)).anti_self_dual = 0 := by
      ext i j
      unfold embedAntiSelfDual
      simp only [Matrix.of_apply]
      cases hx : chiralIso.symm i <;> cases hy : chiralIso.symm j
      · rfl
      · rfl
      · rfl
      · unfold chiralProject toSl2c
        simp [Matrix.trace]
    change (0 : ChiralM) = embedSelfDual (chiralProject (0 : ChiralM)).self_dual + embedAntiSelfDual (chiralProject (0 : ChiralM)).anti_self_dual
    rw [h1, h2, add_zero]
  sd_is_smooth := by
    intro mu i j
    exact contDiff_const
  asd_is_smooth := by
    intro mu i j
    exact contDiff_const
}⟩

def isSpin4cAlgebra (M : ChiralM) : Prop := 
  ∃ (L R : SL2C), M = embedSelfDual L + embedAntiSelfDual R

lemma sum_ite_mul {α β : Type*} [Ring β] [Fintype α] [DecidableEq α] 
  (a : α) (f : α → β) (g : α → β) :
  (∑ x : α, (if x = a then f x else 0) * g x) = f a * g a := by
  have h : ∀ x, (if x = a then f x else 0) * g x = if x = a then f x * g x else 0 := by
    intro x
    split_ifs
    · rfl
    · exact zero_mul (g x)
  rw [Finset.sum_congr rfl (fun x _ => h x)]
  rw [Finset.sum_eq_single a]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb]
  · intro h_not_in
    exfalso
    exact h_not_in (Finset.mem_univ a)

lemma sum_ite_smul {α M : Type*} [AddCommMonoid M] [Module ℂ M] [Fintype α] [DecidableEq α]
  (a : α) (f : α → ℂ) (g : α → M) :
  (∑ x : α, (if x = a then f x else 0) • g x) = f a • g a := by
  have h : ∀ x, (if x = a then f x else 0) • g x = if x = a then f x • g x else 0 := by
    intro x
    split_ifs
    · rfl
    · exact zero_smul ℂ (g x)
  rw [Finset.sum_congr rfl (fun x _ => h x)]
  rw [Finset.sum_eq_single a]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb]
  · intro h_not_in
    exfalso
    exact h_not_in (Finset.mem_univ a)

lemma ite_and_mul (α μ β ν : Fin 4) : 
  (if α = μ ∧ β = ν then (1:ℂ) else 0) = (if α = μ then (1:ℂ) else 0) * (if β = ν then (1:ℂ) else 0) := by
  by_cases h1 : α = μ
  · by_cases h2 : β = ν
    · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, mul_one]
    · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul]

lemma h_or_ex (μ ν ρ σ α β : Fin 4) (h_diff : μ ≠ ρ ∨ ν ≠ σ) : 
  ¬ ((α = μ ∧ β = ν) ∧ (α = ρ ∧ β = σ)) := by
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  rcases h_diff with hd | hd
  · exact hd (h1.symm.trans h3)
  · exact hd (h2.symm.trans h4)

def F_single (μ ν : Fin 4) (M : ChiralM) : Fin 4 → Fin 4 → ChiralM :=
  fun α β => if α = μ ∧ β = ν then M else 0

def F_double (μ ν ρ σ : Fin 4) (M : ChiralM) : Fin 4 → Fin 4 → ChiralM :=
  fun α β => if (α = μ ∧ β = ν) ∨ (α = ρ ∧ β = σ) then M else 0

lemma isSpin4cAlgebra_zero : isSpin4cAlgebra 0 := by
  use 0, 0
  have h1 : embedSelfDual (0 : SL2C) = 0 := by
    ext i j
    unfold embedSelfDual
    simp only [Matrix.of_apply]
    cases hx : chiralIso.symm i <;> cases hy : chiralIso.symm j <;> rfl
  have h2 : embedAntiSelfDual (0 : SL2C) = 0 := by
    ext i j
    unfold embedAntiSelfDual
    simp only [Matrix.of_apply]
    cases hx : chiralIso.symm i <;> cases hy : chiralIso.symm j <;> rfl
  rw [h1, h2, add_zero]

noncomputable def M0 : ChiralM := embedSelfDual sigma1 + embedAntiSelfDual 0

lemma isSpin4cAlgebra_M0 : isSpin4cAlgebra M0 := ⟨sigma1, 0, rfl⟩

lemma sum_fin_4_eval (f : Fin 4 → ℂ) : ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := by
  have h1 : ∑ i : Fin 4, f i = f 0 + ∑ i : Fin 3, f (i.succ) := Fin.sum_univ_succ f
  have h2 : ∑ i : Fin 3, f (i.succ) = f 1 + ∑ i : Fin 2, f (i.succ.succ) := Fin.sum_univ_succ (fun i => f i.succ)
  have h3 : ∑ i : Fin 2, f (i.succ.succ) = f 2 + ∑ i : Fin 1, f (i.succ.succ.succ) := Fin.sum_univ_succ (fun i => f i.succ.succ)
  have h4 : ∑ i : Fin 1, f (i.succ.succ.succ) = f 3 + ∑ i : Fin 0, f (i.succ.succ.succ.succ) := Fin.sum_univ_succ (fun i => f i.succ.succ.succ)
  have h5 : ∑ i : Fin 0, f (i.succ.succ.succ.succ) = 0 := Finset.sum_empty
  rw [h1, h2, h3, h4, h5]
  ring

lemma chiralIso_symm_0 : chiralIso.symm 0 = Sum.inl 0 := rfl
lemma chiralIso_symm_1 : chiralIso.symm 1 = Sum.inl 1 := rfl
lemma chiralIso_symm_2 : chiralIso.symm 2 = Sum.inr 0 := rfl
lemma chiralIso_symm_3 : chiralIso.symm 3 = Sum.inr 1 := rfl

lemma trace_M0_sq : Matrix.trace (M0 * M0) = 2 := by
  have h_trace : Matrix.trace (M0 * M0) = ∑ i : Fin 4, ∑ j : Fin 4, M0 i j * M0 j i := rfl
  rw [h_trace]
  rw [sum_fin_4_eval]
  simp_rw [sum_fin_4_eval]
  unfold M0 embedSelfDual embedAntiSelfDual
  simp only [Matrix.add_apply, Matrix.of_apply]
  rw [val_sigma1]
  unfold sigmaX mkMat
  simp only [chiralIso_symm_0, chiralIso_symm_1, chiralIso_symm_2, chiralIso_symm_3]
  dsimp
  simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

lemma F_single_is_alg (μ ν : Fin 4) : ∀ α β, isSpin4cAlgebra (F_single μ ν M0 α β) := by
  intro α β
  unfold F_single
  split_ifs
  · exact isSpin4cAlgebra_M0
  · exact isSpin4cAlgebra_zero

lemma F_double_is_alg (μ ν ρ σ : Fin 4) : ∀ α β, isSpin4cAlgebra (F_double μ ν ρ σ M0 α β) := by
  intro α β
  unfold F_double
  split_ifs
  · exact isSpin4cAlgebra_M0
  · exact isSpin4cAlgebra_zero

lemma ite_F_single_sq (μ ν : Fin 4) (M : ChiralM) (α β γ δ : Fin 4) :
  Matrix.trace (F_single μ ν M α β * F_single μ ν M γ δ) =
  (if α = μ ∧ β = ν then (1:ℂ) else 0) * (if γ = μ ∧ δ = ν then (1:ℂ) else 0) * Matrix.trace (M * M) := by
  unfold F_single
  by_cases h1 : α = μ ∧ β = ν
  · by_cases h2 : γ = μ ∧ δ = ν
    · have hf1 : (if α = μ ∧ β = ν then M else 0) = M := if_pos h1
      have hf2 : (if γ = μ ∧ δ = ν then M else 0) = M := if_pos h2
      have hi1 : (if α = μ ∧ β = ν then (1:ℂ) else 0) = 1 := if_pos h1
      have hi2 : (if γ = μ ∧ δ = ν then (1:ℂ) else 0) = 1 := if_pos h2
      rw [hf1, hf2, hi1, hi2]
      ring
    · have hf1 : (if α = μ ∧ β = ν then M else 0) = M := if_pos h1
      have hf2 : (if γ = μ ∧ δ = ν then M else 0) = 0 := if_neg h2
      have hi2 : (if γ = μ ∧ δ = ν then (1:ℂ) else 0) = 0 := if_neg h2
      rw [hf1, hf2, hi2]
      have hz : M * 0 = 0 := Matrix.mul_zero M
      rw [hz, Matrix.trace_zero]
      ring
  · have hf1 : (if α = μ ∧ β = ν then M else 0) = 0 := if_neg h1
    have hi1 : (if α = μ ∧ β = ν then (1:ℂ) else 0) = 0 := if_neg h1
    rw [hf1, hi1]
    have hz : 0 * (if γ = μ ∧ δ = ν then M else 0) = 0 := Matrix.zero_mul _
    rw [hz, Matrix.trace_zero]
    ring

lemma ite_F_double_sq (μ ν ρ σ : Fin 4) (M : ChiralM) (α β γ δ : Fin 4) (h_diff : μ ≠ ρ ∨ ν ≠ σ) :
  Matrix.trace (F_double μ ν ρ σ M α β * F_double μ ν ρ σ M γ δ) =
  ((if α = μ ∧ β = ν then (1:ℂ) else 0) + (if α = ρ ∧ β = σ then (1:ℂ) else 0)) * 
  ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) * 
  Matrix.trace (M * M) := by
  unfold F_double
  have hex_a := h_or_ex μ ν ρ σ α β h_diff
  have hex_g := h_or_ex μ ν ρ σ γ δ h_diff
  
  by_cases ha1 : α = μ ∧ β = ν
  · have ha2 : ¬ (α = ρ ∧ β = σ) := fun h => hex_a ⟨ha1, h⟩
    have hfa : (if α = μ ∧ β = ν ∨ α = ρ ∧ β = σ then M else 0) = M := if_pos (Or.inl ha1)
    have hea : ((if α = μ ∧ β = ν then (1:ℂ) else 0) + (if α = ρ ∧ β = σ then (1:ℂ) else 0)) = 1 := by rw [if_pos ha1, if_neg ha2]; ring
    
    by_cases hg1 : γ = μ ∧ δ = ν
    · have hg2 : ¬ (γ = ρ ∧ δ = σ) := fun h => hex_g ⟨hg1, h⟩
      have hfg : (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = M := if_pos (Or.inl hg1)
      have heg : ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) = 1 := by rw [if_pos hg1, if_neg hg2]; ring
      rw [hfa, hfg, hea, heg]; ring
    · by_cases hg2 : γ = ρ ∧ δ = σ
      · have hfg : (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = M := if_pos (Or.inr hg2)
        have heg : ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) = 1 := by rw [if_neg hg1, if_pos hg2]; ring
        rw [hfa, hfg, hea, heg]; ring
      · have hfg : (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = 0 := if_neg (fun h => h.elim hg1 hg2)
        have heg : ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) = 0 := by rw [if_neg hg1, if_neg hg2]; ring
        rw [hfa, hfg, hea, heg]
        have hz : M * 0 = 0 := Matrix.mul_zero M
        rw [hz, Matrix.trace_zero]; ring
  · by_cases ha2 : α = ρ ∧ β = σ
    · have hfa : (if α = μ ∧ β = ν ∨ α = ρ ∧ β = σ then M else 0) = M := if_pos (Or.inr ha2)
      have hea : ((if α = μ ∧ β = ν then (1:ℂ) else 0) + (if α = ρ ∧ β = σ then (1:ℂ) else 0)) = 1 := by rw [if_neg ha1, if_pos ha2]; ring
      
      by_cases hg1 : γ = μ ∧ δ = ν
      · have hg2 : ¬ (γ = ρ ∧ δ = σ) := fun h => hex_g ⟨hg1, h⟩
        have hfg : (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = M := if_pos (Or.inl hg1)
        have heg : ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) = 1 := by rw [if_pos hg1, if_neg hg2]; ring
        rw [hfa, hfg, hea, heg]; ring
      · by_cases hg2 : γ = ρ ∧ δ = σ
        · have hfg : (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = M := if_pos (Or.inr hg2)
          have heg : ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) = 1 := by rw [if_neg hg1, if_pos hg2]; ring
          rw [hfa, hfg, hea, heg]; ring
        · have hfg : (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = 0 := if_neg (fun h => h.elim hg1 hg2)
          have heg : ((if γ = μ ∧ δ = ν then (1:ℂ) else 0) + (if γ = ρ ∧ δ = σ then (1:ℂ) else 0)) = 0 := by rw [if_neg hg1, if_neg hg2]; ring
          rw [hfa, hfg, hea, heg]
          have hz : M * 0 = 0 := Matrix.mul_zero M
          rw [hz, Matrix.trace_zero]; ring
    · have hfa : (if α = μ ∧ β = ν ∨ α = ρ ∧ β = σ then M else 0) = 0 := if_neg (fun h => h.elim ha1 ha2)
      have hea : ((if α = μ ∧ β = ν then (1:ℂ) else 0) + (if α = ρ ∧ β = σ then (1:ℂ) else 0)) = 0 := by rw [if_neg ha1, if_neg ha2]; ring
      rw [hfa, hea]
      have hz : 0 * (if γ = μ ∧ δ = ν ∨ γ = ρ ∧ δ = σ then M else 0) = 0 := Matrix.zero_mul _
      rw [hz, Matrix.trace_zero]; ring

end CGD.Foundations

-- FILENAME: CGD/Gravity/Urbantke/PlebanskiComponents2.lean

import CGD.Gravity.Urbantke.PlebanskiComponents1

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

lemma plebanski_f_comp (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (Λ : ℂ)
  (h_su2 : ∀ μ ν, 
    F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧
    F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1)
  (h_plebanski : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1) 
  (a b : Fin 3) :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
    CGD.Gravity.epsilon4 μ ν ρ σ * (F_comp F a μ ν * F_comp F b ρ σ)) = 
  if a = b then -Λ/2 else 0 := by
  
  let I (a b : Fin 3) : ℂ :=
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (F_comp F a μ ν * F_comp F b ρ σ))

  have h00 : ∀ μ ν, F μ ν 0 0 = 0 := fun μ ν => (h_su2 μ ν).1
  have h11 : ∀ μ ν, F μ ν 1 1 = 0 := fun μ ν => (h_su2 μ ν).2.1
  have h22 : ∀ μ ν, F μ ν 2 2 = 0 := fun μ ν => (h_su2 μ ν).2.2.1
  have h21 : ∀ μ ν, F μ ν 2 1 = - F μ ν 1 2 := fun μ ν => (h_su2 μ ν).2.2.2.1
  have h20 : ∀ μ ν, F μ ν 2 0 = - F μ ν 0 2 := fun μ ν => (h_su2 μ ν).2.2.2.2.1
  have h10 : ∀ μ ν, F μ ν 1 0 = - F μ ν 0 1 := fun μ ν => (h_su2 μ ν).2.2.2.2.2

  have h01 : ∀ μ ν, F μ ν 0 1 = F_comp F 2 μ ν := fun _ _ => rfl
  have h12 : ∀ μ ν, F μ ν 1 2 = F_comp F 0 μ ν := fun _ _ => rfl
  have h20_comp : ∀ μ ν, F μ ν 2 0 = F_comp F 1 μ ν := fun _ _ => rfl

  have h10_comp : ∀ μ ν, F μ ν 1 0 = - F_comp F 2 μ ν := by intro μ ν; rw [h10, h01]
  have h21_comp : ∀ μ ν, F μ ν 2 1 = - F_comp F 0 μ ν := by intro μ ν; rw [h21, h12]
  have h02_comp : ∀ μ ν, F μ ν 0 2 = - F_comp F 1 μ ν := by
    intro μ ν
    have h := h20 μ ν
    calc F μ ν 0 2 = - (- F μ ν 0 2) := by ring
    _ = - F μ ν 2 0 := by rw [←h]
    _ = - F_comp F 1 μ ν := by rw [h20_comp]

  have h_eval2 : ∀ i j, (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν * F ρ σ) i j) =
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν i 0 * F ρ σ 0 j)) +
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν i 1 * F ρ σ 1 j)) +
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν i 2 * F ρ σ 2 j)) := by
    intro i j
    have h_inner : ∀ μ ν ρ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν * F ρ σ) i j = 
      CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν i 0 * F ρ σ 0 j) + 
      CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν i 1 * F ρ σ 1 j) + 
      CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν i 2 * F ρ σ 2 j) := by
      intro μ ν ρ σ
      rw [Matrix.mul_apply]
      have h_sum := Fin.sum_univ_three (fun k => F μ ν i k * F ρ σ k j)
      rw [h_sum]
      ring
    simp_rw [h_inner, Finset.sum_add_distrib]

  have sum_zero : ∀ (f g : Fin 4 → Fin 4 → ℂ), (∀ μ ν, f μ ν = 0) →
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (f μ ν * g ρ σ)) = 0 := by
    intro f g h
    apply Finset.sum_eq_zero; intro μ _
    apply Finset.sum_eq_zero; intro ν _
    apply Finset.sum_eq_zero; intro ρ _
    apply Finset.sum_eq_zero; intro σ _
    rw [h μ ν]
    ring

  have sum_zero_right : ∀ (f g : Fin 4 → Fin 4 → ℂ), (∀ ρ σ, g ρ σ = 0) →
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (f μ ν * g ρ σ)) = 0 := by
    intro f g h
    apply Finset.sum_eq_zero; intro μ _
    apply Finset.sum_eq_zero; intro ν _
    apply Finset.sum_eq_zero; intro ρ _
    apply Finset.sum_eq_zero; intro σ _
    rw [h ρ σ]
    ring
    
  have sum_I_pos : ∀ (f1 f2 : Fin 4 → Fin 4 → ℂ) (x y : Fin 3),
    (∀ μ ν, f1 μ ν = F_comp F x μ ν) →
    (∀ ρ σ, f2 ρ σ = F_comp F y ρ σ) →
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (f1 μ ν * f2 ρ σ)) = I x y := by
    intro f1 f2 x y h1 h2
    apply Finset.sum_congr rfl; intro μ _
    apply Finset.sum_congr rfl; intro ν _
    apply Finset.sum_congr rfl; intro ρ _
    apply Finset.sum_congr rfl; intro σ _
    rw [h1 μ ν, h2 ρ σ]

  have sum_I_neg1 : ∀ (f1 f2 : Fin 4 → Fin 4 → ℂ) (x y : Fin 3),
    (∀ μ ν, f1 μ ν = - F_comp F x μ ν) →
    (∀ ρ σ, f2 ρ σ = F_comp F y ρ σ) →
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (f1 μ ν * f2 ρ σ)) = - I x y := by
    intro f1 f2 x y h1 h2
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro μ _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro ν _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro ρ _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro σ _
    rw [h1 μ ν, h2 ρ σ]
    ring

  have sum_I_neg2 : ∀ (f1 f2 : Fin 4 → Fin 4 → ℂ) (x y : Fin 3),
    (∀ μ ν, f1 μ ν = F_comp F x μ ν) →
    (∀ ρ σ, f2 ρ σ = - F_comp F y ρ σ) →
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (f1 μ ν * f2 ρ σ)) = - I x y := by
    intro f1 f2 x y h1 h2
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro μ _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro ν _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro ρ _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro σ _
    rw [h1 μ ν, h2 ρ σ]
    ring

  have sum_I_neg_neg : ∀ (f1 f2 : Fin 4 → Fin 4 → ℂ) (x y : Fin 3),
    (∀ μ ν, f1 μ ν = - F_comp F x μ ν) →
    (∀ ρ σ, f2 ρ σ = - F_comp F y ρ σ) →
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ * (f1 μ ν * f2 ρ σ)) = I x y := by
    intro f1 f2 x y h1 h2
    apply Finset.sum_congr rfl; intro μ _
    apply Finset.sum_congr rfl; intro ν _
    apply Finset.sum_congr rfl; intro ρ _
    apply Finset.sum_congr rfl; intro σ _
    rw [h1 μ ν, h2 ρ σ]
    ring

  have eq00 : - I 2 2 - I 1 1 = Λ := by
    have hP := plebanski_matrix_comp F Λ h_plebanski 0 0
    rw [if_pos rfl, h_eval2 0 0] at hP
    have s1 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 0 0 * F ρ σ 0 0)) = 0 :=
      sum_zero (fun μ ν => F μ ν 0 0) (fun ρ σ => F ρ σ 0 0) h00
    have s2 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 0 1 * F ρ σ 1 0)) = - I 2 2 :=
      sum_I_neg2 (fun μ ν => F μ ν 0 1) (fun ρ σ => F ρ σ 1 0) 2 2 h01 h10_comp
    have s3 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 0 2 * F ρ σ 2 0)) = - I 1 1 :=
      sum_I_neg1 (fun μ ν => F μ ν 0 2) (fun ρ σ => F ρ σ 2 0) 1 1 h02_comp h20_comp
    rw [s1, s2, s3] at hP
    calc - I 2 2 - I 1 1 = 0 + - I 2 2 + - I 1 1 := by ring
    _ = Λ := hP

  have eq11 : - I 2 2 - I 0 0 = Λ := by
    have hP := plebanski_matrix_comp F Λ h_plebanski 1 1
    rw [if_pos rfl, h_eval2 1 1] at hP
    have s1 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 1 0 * F ρ σ 0 1)) = - I 2 2 :=
      sum_I_neg1 (fun μ ν => F μ ν 1 0) (fun ρ σ => F ρ σ 0 1) 2 2 h10_comp h01
    have s2 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 1 1 * F ρ σ 1 1)) = 0 :=
      sum_zero (fun μ ν => F μ ν 1 1) (fun ρ σ => F ρ σ 1 1) h11
    have s3 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 1 2 * F ρ σ 2 1)) = - I 0 0 :=
      sum_I_neg2 (fun μ ν => F μ ν 1 2) (fun ρ σ => F ρ σ 2 1) 0 0 h12 h21_comp
    rw [s1, s2, s3] at hP
    calc - I 2 2 - I 0 0 = - I 2 2 + 0 + - I 0 0 := by ring
    _ = Λ := hP

  have eq22 : - I 1 1 - I 0 0 = Λ := by
    have hP := plebanski_matrix_comp F Λ h_plebanski 2 2
    rw [if_pos rfl, h_eval2 2 2] at hP
    have s1 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 2 0 * F ρ σ 0 2)) = - I 1 1 :=
      sum_I_neg2 (fun μ ν => F μ ν 2 0) (fun ρ σ => F ρ σ 0 2) 1 1 h20_comp h02_comp
    have s2 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 2 1 * F ρ σ 1 2)) = - I 0 0 :=
      sum_I_neg1 (fun μ ν => F μ ν 2 1) (fun ρ σ => F ρ σ 1 2) 0 0 h21_comp h12
    have s3 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 2 2 * F ρ σ 2 2)) = 0 :=
      sum_zero (fun μ ν => F μ ν 2 2) (fun ρ σ => F ρ σ 2 2) h22
    rw [s1, s2, s3] at hP
    calc - I 1 1 - I 0 0 = - I 1 1 + - I 0 0 + 0 := by ring
    _ = Λ := hP

  have eq01 : I 1 0 = 0 := by
    have hP := plebanski_matrix_comp F Λ h_plebanski 0 1
    rw [if_neg (by decide), h_eval2 0 1] at hP
    have s1 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 0 0 * F ρ σ 0 1)) = 0 :=
      sum_zero (fun μ ν => F μ ν 0 0) (fun ρ σ => F ρ σ 0 1) h00
    have s2 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 0 1 * F ρ σ 1 1)) = 0 :=
      sum_zero_right (fun μ ν => F μ ν 0 1) (fun ρ σ => F ρ σ 1 1) h11
    have s3 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 0 2 * F ρ σ 2 1)) = I 1 0 :=
      sum_I_neg_neg (fun μ ν => F μ ν 0 2) (fun ρ σ => F ρ σ 2 1) 1 0 h02_comp h21_comp
    rw [s1, s2, s3] at hP
    calc I 1 0 = 0 + 0 + I 1 0 := by ring
    _ = 0 := hP

  have eq10 : I 0 1 = 0 := by
    have hP := plebanski_matrix_comp F Λ h_plebanski 1 0
    rw [if_neg (by decide), h_eval2 1 0] at hP
    have s1 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 1 0 * F ρ σ 0 0)) = 0 :=
      sum_zero_right (fun μ ν => F μ ν 1 0) (fun ρ σ => F ρ σ 0 0) h00
    have s2 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 1 1 * F ρ σ 1 0)) = 0 :=
      sum_zero (fun μ ν => F μ ν 1 1) (fun ρ σ => F ρ σ 1 0) h11
    have s3 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 1 2 * F ρ σ 2 0)) = I 0 1 :=
      sum_I_pos (fun μ ν => F μ ν 1 2) (fun ρ σ => F ρ σ 2 0) 0 1 h12 h20_comp
    rw [s1, s2, s3] at hP
    calc I 0 1 = 0 + 0 + I 0 1 := by ring
    _ = 0 := hP

  have eq02 : I 2 0 = 0 := by
    have hP := plebanski_matrix_comp F Λ h_plebanski 0 2
    rw [if_neg (by decide), h_eval2 0 2] at hP
    have s1 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 0 0 * F ρ σ 0 2)) = 0 :=
      sum_zero (fun μ ν => F μ ν 0 0) (fun ρ σ => F ρ σ 0 2) h00
    have s2 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 0 1 * F ρ σ 1 2)) = I 2 0 :=
      sum_I_pos (fun μ ν => F μ ν 0 1) (fun ρ σ => F ρ σ 1 2) 2 0 h01 h12
    have s3 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 0 2 * F ρ σ 2 2)) = 0 :=
      sum_zero_right (fun μ ν => F μ ν 0 2) (fun ρ σ => F ρ σ 2 2) h22
    rw [s1, s2, s3] at hP
    calc I 2 0 = 0 + I 2 0 + 0 := by ring
    _ = 0 := hP

  have eq20 : I 0 2 = 0 := by
    have hP := plebanski_matrix_comp F Λ h_plebanski 2 0
    rw [if_neg (by decide), h_eval2 2 0] at hP
    have s1 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 2 0 * F ρ σ 0 0)) = 0 :=
      sum_zero_right (fun μ ν => F μ ν 2 0) (fun ρ σ => F ρ σ 0 0) h00
    have s2 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 2 1 * F ρ σ 1 0)) = I 0 2 :=
      sum_I_neg_neg (fun μ ν => F μ ν 2 1) (fun ρ σ => F ρ σ 1 0) 0 2 h21_comp h10_comp
    have s3 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 2 2 * F ρ σ 2 0)) = 0 :=
      sum_zero (fun μ ν => F μ ν 2 2) (fun ρ σ => F ρ σ 2 0) h22
    rw [s1, s2, s3] at hP
    calc I 0 2 = 0 + I 0 2 + 0 := by ring
    _ = 0 := hP

  have eq12 : I 2 1 = 0 := by
    have hP := plebanski_matrix_comp F Λ h_plebanski 1 2
    rw [if_neg (by decide), h_eval2 1 2] at hP
    have s1 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 1 0 * F ρ σ 0 2)) = I 2 1 :=
      sum_I_neg_neg (fun μ ν => F μ ν 1 0) (fun ρ σ => F ρ σ 0 2) 2 1 h10_comp h02_comp
    have s2 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 1 1 * F ρ σ 1 2)) = 0 :=
      sum_zero (fun μ ν => F μ ν 1 1) (fun ρ σ => F ρ σ 1 2) h11
    have s3 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 1 2 * F ρ σ 2 2)) = 0 :=
      sum_zero_right (fun μ ν => F μ ν 1 2) (fun ρ σ => F ρ σ 2 2) h22
    rw [s1, s2, s3] at hP
    calc I 2 1 = I 2 1 + 0 + 0 := by ring
    _ = 0 := hP

  have eq21 : I 1 2 = 0 := by
    have hP := plebanski_matrix_comp F Λ h_plebanski 2 1
    rw [if_neg (by decide), h_eval2 2 1] at hP
    have s1 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 2 0 * F ρ σ 0 1)) = I 1 2 :=
      sum_I_pos (fun μ ν => F μ ν 2 0) (fun ρ σ => F ρ σ 0 1) 1 2 h20_comp h01
    have s2 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 2 1 * F ρ σ 1 1)) = 0 :=
      sum_zero_right (fun μ ν => F μ ν 2 1) (fun ρ σ => F ρ σ 1 1) h11
    have s3 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, CGD.Gravity.epsilon4 μ ν ρ σ * (F μ ν 2 2 * F ρ σ 2 1)) = 0 :=
      sum_zero (fun μ ν => F μ ν 2 2) (fun ρ σ => F ρ σ 2 1) h22
    rw [s1, s2, s3] at hP
    calc I 1 2 = I 1 2 + 0 + 0 := by ring
    _ = 0 := hP

  have hI00 : I 0 0 = -Λ / 2 := by
    calc I 0 0 = (1/2:ℂ) * ((- I 2 2 - I 1 1) - (- I 2 2 - I 0 0) - (- I 1 1 - I 0 0)) := by ring
    _ = (1/2:ℂ) * (Λ - Λ - Λ) := by rw [eq00, eq11, eq22]
    _ = -Λ / 2 := by ring

  have hI11 : I 1 1 = -Λ / 2 := by
    calc I 1 1 = (1/2:ℂ) * ((- I 2 2 - I 0 0) - (- I 2 2 - I 1 1) - (- I 1 1 - I 0 0)) := by ring
    _ = (1/2:ℂ) * (Λ - Λ - Λ) := by rw [eq11, eq00, eq22]
    _ = -Λ / 2 := by ring

  have hI22 : I 2 2 = -Λ / 2 := by
    calc I 2 2 = (1/2:ℂ) * ((- I 1 1 - I 0 0) - (- I 2 2 - I 1 1) - (- I 2 2 - I 0 0)) := by ring
    _ = (1/2:ℂ) * (Λ - Λ - Λ) := by rw [eq22, eq00, eq11]
    _ = -Λ / 2 := by ring

  fin_cases a <;> fin_cases b
  · change I 0 0 = -Λ/2; exact hI00
  · change I 0 1 = 0; exact eq10
  · change I 0 2 = 0; exact eq20
  · change I 1 0 = 0; exact eq01
  · change I 1 1 = -Λ/2; exact hI11
  · change I 1 2 = 0; exact eq21
  · change I 2 0 = 0; exact eq02
  · change I 2 1 = 0; exact eq12
  · change I 2 2 = -Λ/2; exact hI22

end CGD.Gravity

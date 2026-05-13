-- FILENAME: CGD/Gravity/Urbantke/MetricTrace5.lean

import CGD.Gravity.Urbantke.MetricTrace4

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

lemma bubble_a (f : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 3 → ℂ) :
  (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, ∑ a : Fin 3, f A B C D E F_idx a) =
  (∑ a : Fin 3, ∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, f A B C D E F_idx a) := by
  have s1 : ∀ A B C D E, (∑ F_idx : Fin 2, ∑ a : Fin 3, f A B C D E F_idx a) = (∑ a : Fin 3, ∑ F_idx : Fin 2, f A B C D E F_idx a) := fun _ _ _ _ _ => Finset.sum_comm; simp_rw [s1]
  have s2 : ∀ A B C D, (∑ E : Fin 2, ∑ a : Fin 3, ∑ F_idx : Fin 2, f A B C D E F_idx a) = (∑ a : Fin 3, ∑ E : Fin 2, ∑ F_idx : Fin 2, f A B C D E F_idx a) := fun _ _ _ _ => Finset.sum_comm; simp_rw [s2]
  have s3 : ∀ A B C, (∑ D : Fin 2, ∑ a : Fin 3, ∑ E : Fin 2, ∑ F_idx : Fin 2, f A B C D E F_idx a) = (∑ a : Fin 3, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, f A B C D E F_idx a) := fun _ _ _ => Finset.sum_comm; simp_rw [s3]
  have s4 : ∀ A B, (∑ C : Fin 2, ∑ a : Fin 3, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, f A B C D E F_idx a) = (∑ a : Fin 3, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, f A B C D E F_idx a) := fun _ _ => Finset.sum_comm; simp_rw [s4]
  have s5 : ∀ A, (∑ B : Fin 2, ∑ a : Fin 3, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, f A B C D E F_idx a) = (∑ a : Fin 3, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, f A B C D E F_idx a) := fun _ => Finset.sum_comm; simp_rw [s5]
  exact Finset.sum_comm

lemma bubble_b (f : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 3 → Fin 3 → ℂ) :
  (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, ∑ a : Fin 3, ∑ b : Fin 3, f A B C D E F_idx a b) =
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, f A B C D E F_idx a b) := by
  have h1 : (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, ∑ a : Fin 3, ∑ b : Fin 3, f A B C D E F_idx a b) =
            (∑ a : Fin 3, ∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, ∑ b : Fin 3, f A B C D E F_idx a b) := bubble_a (fun A B C D E F_idx a => ∑ b : Fin 3, f A B C D E F_idx a b)
  rw [h1]
  apply Finset.sum_congr rfl; intro a _
  exact bubble_a (fun A B C D E F_idx b => f A B C D E F_idx a b)

lemma bubble_c (f : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
  (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, f A B C D E F_idx a b c) =
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, f A B C D E F_idx a b c) := by
  have h1 : (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, f A B C D E F_idx a b c) =
            (∑ a : Fin 3, ∑ b : Fin 3, ∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, ∑ c : Fin 3, f A B C D E F_idx a b c) := bubble_b (fun A B C D E F_idx a b => ∑ c : Fin 3, f A B C D E F_idx a b c)
  rw [h1]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  exact bubble_a (fun A B C D E F_idx c => f A B C D E F_idx a b c)

lemma inner_eval (F1 F2 F3 tau1 tau2 tau3 : Fin 3 → ℂ) (e1 e2 e3 : ℂ) :
  (∑ a, F1 a * tau1 a) * e1 * (∑ b, F2 b * tau2 b) * e2 * (∑ c, F3 c * tau3 c) * e3 =
  ∑ a, ∑ b, ∑ c, F1 a * F2 b * F3 c * (tau1 a * e1 * tau2 b * e2 * tau3 c * e3) := by
  have h_assoc : (∑ a, F1 a * tau1 a) * e1 * (∑ b, F2 b * tau2 b) * e2 * (∑ c, F3 c * tau3 c) * e3 =
    ((∑ a, F1 a * tau1 a) * e1) * ((∑ b, F2 b * tau2 b) * e2) * ((∑ c, F3 c * tau3 c) * e3) := by ring
  rw [h_assoc]
  have h1 : (∑ a, F1 a * tau1 a) * e1 = ∑ a, F1 a * tau1 a * e1 := Finset.sum_mul _ _ _
  have h2 : (∑ b, F2 b * tau2 b) * e2 = ∑ b, F2 b * tau2 b * e2 := Finset.sum_mul _ _ _
  have h3 : (∑ c, F3 c * tau3 c) * e3 = ∑ c, F3 c * tau3 c * e3 := Finset.sum_mul _ _ _
  rw [h1, h2, h3]
  have h4 : (∑ a, F1 a * tau1 a * e1) * (∑ b, F2 b * tau2 b * e2) = ∑ a, ∑ b, (F1 a * tau1 a * e1) * (F2 b * tau2 b * e2) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.mul_sum]
  rw [h4]
  have h5 : (∑ a, ∑ b, (F1 a * tau1 a * e1) * (F2 b * tau2 b * e2)) * (∑ c, F3 c * tau3 c * e3) = ∑ a, ∑ b, ∑ c, ((F1 a * tau1 a * e1) * (F2 b * tau2 b * e2)) * (F3 c * tau3 c * e3) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.mul_sum]
  rw [h5]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  ring

lemma TE_apply (a : Fin 3) (i j : Fin 2) :
  (TE a) i j = ∑ k : Fin 2, tau a i k * eps2 k j := rfl

lemma trace_TE_expanded (a b c : Fin 3) :
  Matrix.trace (TE a * TE b * TE c) =
  ∑ A : Fin 2, ∑ C : Fin 2, ∑ E : Fin 2,
    (TE a) A C * (TE b) C E * (TE c) E A := by
  have h1 : Matrix.trace (TE a * TE b * TE c) = ∑ A : Fin 2, (TE a * TE b * TE c) A A := rfl
  rw [h1]
  apply Finset.sum_congr rfl; intro A _
  have h2 : (TE a * TE b * TE c) A A = ∑ E : Fin 2, (TE a * TE b) A E * (TE c) E A := rfl
  rw [h2]
  have h3 : ∀ E, (TE a * TE b) A E = ∑ C : Fin 2, (TE a) A C * (TE b) C E := fun _ => rfl
  simp_rw [h3]
  have h4 : ∀ E, (∑ C : Fin 2, (TE a) A C * (TE b) C E) * (TE c) E A = ∑ C : Fin 2, (TE a) A C * (TE b) C E * (TE c) E A := fun _ => Finset.sum_mul _ _ _
  simp_rw [h4]
  rw [Finset.sum_comm]

lemma trace_TE_fully_expanded (a b c : Fin 3) :
  Matrix.trace (TE a * TE b * TE c) =
  ∑ A : Fin 2, ∑ C : Fin 2, ∑ E : Fin 2,
    (∑ B : Fin 2, tau a A B * eps2 B C) *
    (∑ D : Fin 2, tau b C D * eps2 D E) *
    (∑ F_idx : Fin 2, tau c E F_idx * eps2 F_idx A) := by
  rw [trace_TE_expanded]
  apply Finset.sum_congr rfl; intro A _
  apply Finset.sum_congr rfl; intro C _
  apply Finset.sum_congr rfl; intro E _
  have h1 : (TE a) A C = ∑ B : Fin 2, tau a A B * eps2 B C := rfl
  have h2 : (TE b) C E = ∑ D : Fin 2, tau b C D * eps2 D E := rfl
  have h3 : (TE c) E A = ∑ F_idx : Fin 2, tau c E F_idx * eps2 F_idx A := rfl
  rw [h1, h2, h3]

lemma trace_TE_rearranged (a b c : Fin 3) :
  Matrix.trace (TE a * TE b * TE c) =
  ∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2,
    tau a A B * eps2 B C * tau b C D * eps2 D E * tau c E F_idx * eps2 F_idx A := by
  rw [trace_TE_fully_expanded]
  have step1 : ∀ A C E, (∑ B : Fin 2, tau a A B * eps2 B C) * (∑ D : Fin 2, tau b C D * eps2 D E) * (∑ F_idx : Fin 2, tau c E F_idx * eps2 F_idx A) =
    ∑ B : Fin 2, ∑ D : Fin 2, ∑ F_idx : Fin 2, tau a A B * eps2 B C * tau b C D * eps2 D E * tau c E F_idx * eps2 F_idx A := by
    intro A C E
    have h_assoc : (∑ B : Fin 2, tau a A B * eps2 B C) * (∑ D : Fin 2, tau b C D * eps2 D E) * (∑ F_idx : Fin 2, tau c E F_idx * eps2 F_idx A) =
      ((∑ B : Fin 2, tau a A B * eps2 B C) * (∑ D : Fin 2, tau b C D * eps2 D E)) * (∑ F_idx : Fin 2, tau c E F_idx * eps2 F_idx A) := rfl
    rw [h_assoc]
    have h1 : (∑ B : Fin 2, tau a A B * eps2 B C) * (∑ D : Fin 2, tau b C D * eps2 D E) = ∑ B : Fin 2, ∑ D : Fin 2, (tau a A B * eps2 B C) * (tau b C D * eps2 D E) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro B _
      rw [Finset.mul_sum]
    rw [h1]
    have h2 : (∑ B : Fin 2, ∑ D : Fin 2, (tau a A B * eps2 B C) * (tau b C D * eps2 D E)) * (∑ F_idx : Fin 2, tau c E F_idx * eps2 F_idx A) =
      ∑ B : Fin 2, ∑ D : Fin 2, ∑ F_idx : Fin 2, ((tau a A B * eps2 B C) * (tau b C D * eps2 D E)) * (tau c E F_idx * eps2 F_idx A) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro B _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro D _
      rw [Finset.mul_sum]
    rw [h2]
    apply Finset.sum_congr rfl; intro B _
    apply Finset.sum_congr rfl; intro D _
    apply Finset.sum_congr rfl; intro F_idx _
    ring
  simp_rw [step1]
  apply Finset.sum_congr rfl; intro A _
  have s1 : ∀ C, (∑ E : Fin 2, ∑ B : Fin 2, ∑ D : Fin 2, ∑ F_idx : Fin 2, tau a A B * eps2 B C * tau b C D * eps2 D E * tau c E F_idx * eps2 F_idx A) =
                 (∑ B : Fin 2, ∑ E : Fin 2, ∑ D : Fin 2, ∑ F_idx : Fin 2, tau a A B * eps2 B C * tau b C D * eps2 D E * tau c E F_idx * eps2 F_idx A) := fun _ => Finset.sum_comm
  simp_rw [s1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro B _
  apply Finset.sum_congr rfl; intro C _
  rw [Finset.sum_comm]

lemma sum_trace_eq (F1 F2 F3 : Fin 3 → ℂ) :
  (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2,
    (∑ a : Fin 3, F1 a * tau a A B) * eps2 B C *
    (∑ b : Fin 3, F2 b * tau b C D) * eps2 D E *
    (∑ c : Fin 3, F3 c * tau c E F_idx) * eps2 F_idx A) =
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
    F1 a * F2 b * F3 c * (-2 * I * epsilon3 a b c) := by
  have h1 : ∀ A B C D E F_idx, 
    (∑ a : Fin 3, F1 a * tau a A B) * eps2 B C * (∑ b : Fin 3, F2 b * tau b C D) * eps2 D E * (∑ c : Fin 3, F3 c * tau c E F_idx) * eps2 F_idx A =
    ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, F1 a * F2 b * F3 c * (tau a A B * eps2 B C * tau b C D * eps2 D E * tau c E F_idx * eps2 F_idx A) := by
    intro A B C D E F_idx
    exact inner_eval F1 F2 F3 (fun a => tau a A B) (fun b => tau b C D) (fun c => tau c E F_idx) (eps2 B C) (eps2 D E) (eps2 F_idx A)
  
  have h2 : (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2,
    (∑ a : Fin 3, F1 a * tau a A B) * eps2 B C *
    (∑ b : Fin 3, F2 b * tau b C D) * eps2 D E *
    (∑ c : Fin 3, F3 c * tau c E F_idx) * eps2 F_idx A) =
    (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2,
    ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, F1 a * F2 b * F3 c * (tau a A B * eps2 B C * tau b C D * eps2 D E * tau c E F_idx * eps2 F_idx A)) := by
    apply Finset.sum_congr rfl; intro A _
    apply Finset.sum_congr rfl; intro B _
    apply Finset.sum_congr rfl; intro C _
    apply Finset.sum_congr rfl; intro D _
    apply Finset.sum_congr rfl; intro E _
    apply Finset.sum_congr rfl; intro F_idx _
    exact h1 A B C D E F_idx
  rw [h2]
  rw [bubble_c]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  have h_pull : (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, F1 a * F2 b * F3 c * (tau a A B * eps2 B C * tau b C D * eps2 D E * tau c E F_idx * eps2 F_idx A)) =
    (F1 a * F2 b * F3 c) * (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, tau a A B * eps2 B C * tau b C D * eps2 D E * tau c E F_idx * eps2 F_idx A) := by
    simp only [← Finset.mul_sum]
  rw [h_pull]
  have h3 : (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2,
      tau a A B * eps2 B C * tau b C D * eps2 D E * tau c E F_idx * eps2 F_idx A) = Matrix.trace (TE a * TE b * TE c) := (trace_TE_rearranged a b c).symm
  rw [h3]
  rw [trace_TE a b c]

end CGD.Gravity

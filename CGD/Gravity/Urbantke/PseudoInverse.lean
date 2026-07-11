-- FILENAME: CGD/Gravity/Urbantke/PseudoInverse.lean

import CGD.Gravity.Urbantke.PlebanskiComponents2

set_option linter.unusedSimpArgs false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

lemma capovilla_invPsi_eq (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (Λ : ℂ)
  (h_su2 : ∀ μ ν,
    F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧
    F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1)
  (h_plebanski : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1)
  (A B C D : Fin 2) :
  let R_up := fun ρ σ A_idx B_idx => (∑ A' : Fin 2, ∑ B' : Fin 2, eps2_up A_idx A' * eps2_up B_idx B' * capovilla_R F ρ σ A' B');
  (if A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 then Λ
   else if A = 1 ∧ B = 1 ∧ C = 1 ∧ D = 1 then Λ
   else if (A = 0 ∧ B = 1 ∨ A = 1 ∧ B = 0) ∧ (C = 0 ∧ D = 1 ∨ C = 1 ∧ D = 0) then (1/2:ℂ) * Λ
   else 0) =
    (1:ℂ) * (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ α : Fin 4, ∑ β : Fin 4,
      CGD.Gravity.epsilon4 ρ σ α β * R_up ρ σ A B * capovilla_R F α β C D) := by

  have H_eval : (if A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 then Λ
   else if A = 1 ∧ B = 1 ∧ C = 1 ∧ D = 1 then Λ
   else if (A = 0 ∧ B = 1 ∨ A = 1 ∧ B = 0) ∧ (C = 0 ∧ D = 1 ∨ C = 1 ∧ D = 0) then (1/2:ℂ) * Λ
   else 0) =
    (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ α : Fin 4, ∑ β : Fin 4,
      CGD.Gravity.epsilon4 ρ σ α β * (∑ A' : Fin 2, ∑ B' : Fin 2, eps2_up A A' * eps2_up B B' * capovilla_R F ρ σ A' B') * capovilla_R F α β C D) := by

    let P (x y : Fin 4 → Fin 4 → ℂ) : ℂ :=
      ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ α : Fin 4, ∑ β : Fin 4, CGD.Gravity.epsilon4 ρ σ α β * (x ρ σ * y α β)

    have P_add_left : ∀ x1 x2 y, P (fun ρ σ => x1 ρ σ + x2 ρ σ) y = P x1 y + P x2 y := by
      intro x1 x2 y; dsimp [P]
      have h : ∀ ρ σ α β, CGD.Gravity.epsilon4 ρ σ α β * ((x1 ρ σ + x2 ρ σ) * y α β) =
        CGD.Gravity.epsilon4 ρ σ α β * (x1 ρ σ * y α β) + CGD.Gravity.epsilon4 ρ σ α β * (x2 ρ σ * y α β) := by intro ρ σ α β; ring
      simp_rw [h, Finset.sum_add_distrib]

    have P_add_right : ∀ x y1 y2, P x (fun α β => y1 α β + y2 α β) = P x y1 + P x y2 := by
      intro x y1 y2; dsimp [P]
      have h : ∀ ρ σ α β, CGD.Gravity.epsilon4 ρ σ α β * (x ρ σ * (y1 α β + y2 α β)) =
        CGD.Gravity.epsilon4 ρ σ α β * (x ρ σ * y1 α β) + CGD.Gravity.epsilon4 ρ σ α β * (x ρ σ * y2 α β) := by intro ρ σ α β; ring
      simp_rw [h, Finset.sum_add_distrib]

    have P_sub_left : ∀ x1 x2 y, P (fun ρ σ => x1 ρ σ - x2 ρ σ) y = P x1 y - P x2 y := by
      intro x1 x2 y; dsimp [P]
      have h : ∀ ρ σ α β, CGD.Gravity.epsilon4 ρ σ α β * ((x1 ρ σ - x2 ρ σ) * y α β) =
        CGD.Gravity.epsilon4 ρ σ α β * (x1 ρ σ * y α β) - CGD.Gravity.epsilon4 ρ σ α β * (x2 ρ σ * y α β) := by intro ρ σ α β; ring
      simp_rw [h, Finset.sum_sub_distrib]

    have P_sub_right : ∀ x y1 y2, P x (fun α β => y1 α β - y2 α β) = P x y1 - P x y2 := by
      intro x y1 y2; dsimp [P]
      have h : ∀ ρ σ α β, CGD.Gravity.epsilon4 ρ σ α β * (x ρ σ * (y1 α β - y2 α β)) =
        CGD.Gravity.epsilon4 ρ σ α β * (x ρ σ * y1 α β) - CGD.Gravity.epsilon4 ρ σ α β * (x ρ σ * y2 α β) := by intro ρ σ α β; ring
      simp_rw [h, Finset.sum_sub_distrib]

    have P_neg_left : ∀ x y, P (fun ρ σ => - x ρ σ) y = - P x y := by
      intro x y; dsimp [P]
      have h : ∀ ρ σ α β, CGD.Gravity.epsilon4 ρ σ α β * ((- x ρ σ) * y α β) =
        - (CGD.Gravity.epsilon4 ρ σ α β * (x ρ σ * y α β)) := by intro ρ σ α β; ring
      simp_rw [h, Finset.sum_neg_distrib]

    have P_neg_right : ∀ x y, P x (fun α β => - y α β) = - P x y := by
      intro x y; dsimp [P]
      have h : ∀ ρ σ α β, CGD.Gravity.epsilon4 ρ σ α β * (x ρ σ * (- y α β)) =
        - (CGD.Gravity.epsilon4 ρ σ α β * (x ρ σ * y α β)) := by intro ρ σ α β; ring
      simp_rw [h, Finset.sum_neg_distrib]

    have P_smul_left : ∀ (c : ℂ) x y, P (fun ρ σ => c * x ρ σ) y = c * P x y := by
      intro c x y; dsimp [P]
      have h : ∀ ρ σ α β, CGD.Gravity.epsilon4 ρ σ α β * ((c * x ρ σ) * y α β) =
        c * (CGD.Gravity.epsilon4 ρ σ α β * (x ρ σ * y α β)) := by intro ρ σ α β; ring
      simp_rw [h, ← Finset.mul_sum]

    have P_smul_right : ∀ (c : ℂ) x y, P x (fun α β => c * y α β) = c * P x y := by
      intro c x y; dsimp [P]
      have h : ∀ ρ σ α β, CGD.Gravity.epsilon4 ρ σ α β * (x ρ σ * (c * y α β)) =
        c * (CGD.Gravity.epsilon4 ρ σ α β * (x ρ σ * y α β)) := by intro ρ σ α β; ring
      simp_rw [h, ← Finset.mul_sum]

    have p00 : P (F_comp F 0) (F_comp F 0) = -Λ/2 := by have h := plebanski_f_comp F Λ h_su2 h_plebanski 0 0; norm_num at h; exact h
    have p11 : P (F_comp F 1) (F_comp F 1) = -Λ/2 := by have h := plebanski_f_comp F Λ h_su2 h_plebanski 1 1; norm_num at h; exact h
    have p22 : P (F_comp F 2) (F_comp F 2) = -Λ/2 := by have h := plebanski_f_comp F Λ h_su2 h_plebanski 2 2; norm_num at h; exact h
    have p01 : P (F_comp F 0) (F_comp F 1) = 0 := by have h := plebanski_f_comp F Λ h_su2 h_plebanski 0 1; norm_num at h; exact h
    have p10 : P (F_comp F 1) (F_comp F 0) = 0 := by have h := plebanski_f_comp F Λ h_su2 h_plebanski 1 0; norm_num at h; exact h
    have p02 : P (F_comp F 0) (F_comp F 2) = 0 := by have h := plebanski_f_comp F Λ h_su2 h_plebanski 0 2; norm_num at h; exact h
    have p20 : P (F_comp F 2) (F_comp F 0) = 0 := by have h := plebanski_f_comp F Λ h_su2 h_plebanski 2 0; norm_num at h; exact h
    have p12 : P (F_comp F 1) (F_comp F 2) = 0 := by have h := plebanski_f_comp F Λ h_su2 h_plebanski 1 2; norm_num at h; exact h
    have p21 : P (F_comp F 2) (F_comp F 1) = 0 := by have h := plebanski_f_comp F Λ h_su2 h_plebanski 2 1; norm_num at h; exact h

    have t000 : tau 0 0 0 = -1 := rfl
    have t001 : tau 0 0 1 = 0 := rfl
    have t010 : tau 0 1 0 = 0 := rfl
    have t011 : tau 0 1 1 = 1 := rfl

    have t100 : tau 1 0 0 = I := rfl
    have t101 : tau 1 0 1 = 0 := rfl
    have t110 : tau 1 1 0 = 0 := rfl
    have t111 : tau 1 1 1 = I := rfl

    have t200 : tau 2 0 0 = 0 := rfl
    have t201 : tau 2 0 1 = 1 := rfl
    have t210 : tau 2 1 0 = 1 := rfl
    have t211 : tau 2 1 1 = 0 := rfl

    have h_cap_00 : ∀ α β, capovilla_R F α β 0 0 = - F_comp F 0 α β + I * F_comp F 1 α β := by
      intro α β; unfold capovilla_R; rw [CGD.Foundations.sum_fin_3_expand]
      change F_comp F 0 α β * tau 0 0 0 + F_comp F 1 α β * tau 1 0 0 + F_comp F 2 α β * tau 2 0 0 = _
      rw [t000, t100, t200]; ring

    have h_cap_01 : ∀ α β, capovilla_R F α β 0 1 = F_comp F 2 α β := by
      intro α β; unfold capovilla_R; rw [CGD.Foundations.sum_fin_3_expand]
      change F_comp F 0 α β * tau 0 0 1 + F_comp F 1 α β * tau 1 0 1 + F_comp F 2 α β * tau 2 0 1 = _
      rw [t001, t101, t201]; ring

    have h_cap_10 : ∀ α β, capovilla_R F α β 1 0 = F_comp F 2 α β := by
      intro α β; unfold capovilla_R; rw [CGD.Foundations.sum_fin_3_expand]
      change F_comp F 0 α β * tau 0 1 0 + F_comp F 1 α β * tau 1 1 0 + F_comp F 2 α β * tau 2 1 0 = _
      rw [t010, t110, t210]; ring

    have h_cap_11 : ∀ α β, capovilla_R F α β 1 1 = F_comp F 0 α β + I * F_comp F 1 α β := by
      intro α β; unfold capovilla_R; rw [CGD.Foundations.sum_fin_3_expand]
      change F_comp F 0 α β * tau 0 1 1 + F_comp F 1 α β * tau 1 1 1 + F_comp F 2 α β * tau 2 1 1 = _
      rw [t011, t111, t211]; ring

    have e00 : eps2_up 0 0 = 0 := rfl
    have e01 : eps2_up 0 1 = 1 := rfl
    have e10 : eps2_up 1 0 = -1 := rfl
    have e11 : eps2_up 1 1 = 0 := rfl

    have h_rup_00 : ∀ ρ σ, (∑ A' : Fin 2, ∑ B' : Fin 2, eps2_up 0 A' * eps2_up 0 B' * capovilla_R F ρ σ A' B') = capovilla_R F ρ σ 1 1 := by
      intro ρ σ; rw [CGD.Foundations.sum_fin_2_expand]
      have h0 : (∑ B' : Fin 2, eps2_up 0 0 * eps2_up 0 B' * capovilla_R F ρ σ 0 B') = 0 := by
        rw [CGD.Foundations.sum_fin_2_expand, e00, e01]; ring
      have h1 : (∑ B' : Fin 2, eps2_up 0 1 * eps2_up 0 B' * capovilla_R F ρ σ 1 B') = capovilla_R F ρ σ 1 1 := by
        rw [CGD.Foundations.sum_fin_2_expand, e00, e01]; ring
      rw [h0, h1]; ring

    have h_rup_01 : ∀ ρ σ, (∑ A' : Fin 2, ∑ B' : Fin 2, eps2_up 0 A' * eps2_up 1 B' * capovilla_R F ρ σ A' B') = - capovilla_R F ρ σ 1 0 := by
      intro ρ σ; rw [CGD.Foundations.sum_fin_2_expand]
      have h0 : (∑ B' : Fin 2, eps2_up 0 0 * eps2_up 1 B' * capovilla_R F ρ σ 0 B') = 0 := by
        rw [CGD.Foundations.sum_fin_2_expand, e00, e10, e11]; ring
      have h1 : (∑ B' : Fin 2, eps2_up 0 1 * eps2_up 1 B' * capovilla_R F ρ σ 1 B') = - capovilla_R F ρ σ 1 0 := by
        rw [CGD.Foundations.sum_fin_2_expand, e01, e10, e11]; ring
      rw [h0, h1]; ring

    have h_rup_10 : ∀ ρ σ, (∑ A' : Fin 2, ∑ B' : Fin 2, eps2_up 1 A' * eps2_up 0 B' * capovilla_R F ρ σ A' B') = - capovilla_R F ρ σ 0 1 := by
      intro ρ σ; rw [CGD.Foundations.sum_fin_2_expand]
      have h0 : (∑ B' : Fin 2, eps2_up 1 0 * eps2_up 0 B' * capovilla_R F ρ σ 0 B') = - capovilla_R F ρ σ 0 1 := by
        rw [CGD.Foundations.sum_fin_2_expand, e10, e00, e01]; ring
      have h1 : (∑ B' : Fin 2, eps2_up 1 1 * eps2_up 0 B' * capovilla_R F ρ σ 1 B') = 0 := by
        rw [CGD.Foundations.sum_fin_2_expand, e11, e00, e01]; ring
      rw [h0, h1]; ring

    have h_rup_11 : ∀ ρ σ, (∑ A' : Fin 2, ∑ B' : Fin 2, eps2_up 1 A' * eps2_up 1 B' * capovilla_R F ρ σ A' B') = capovilla_R F ρ σ 0 0 := by
      intro ρ σ; rw [CGD.Foundations.sum_fin_2_expand]
      have h0 : (∑ B' : Fin 2, eps2_up 1 0 * eps2_up 1 B' * capovilla_R F ρ σ 0 B') = capovilla_R F ρ σ 0 0 := by
        rw [CGD.Foundations.sum_fin_2_expand, e10, e11]; ring
      have h1 : (∑ B' : Fin 2, eps2_up 1 1 * eps2_up 1 B' * capovilla_R F ρ σ 1 B') = 0 := by
        rw [CGD.Foundations.sum_fin_2_expand, e11, e10]; ring
      rw [h0, h1]; ring

    have h_rhs_eq_P : ∀ (A_val B_val C_val D_val : Fin 2), (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ α : Fin 4, ∑ β : Fin 4,
      CGD.Gravity.epsilon4 ρ σ α β * (∑ A' : Fin 2, ∑ B' : Fin 2, eps2_up A_val A' * eps2_up B_val B' * capovilla_R F ρ σ A' B') * capovilla_R F α β C_val D_val) =
      P (fun ρ σ => ∑ A' : Fin 2, ∑ B' : Fin 2, eps2_up A_val A' * eps2_up B_val B' * capovilla_R F ρ σ A' B') (fun α β => capovilla_R F α β C_val D_val) := by
      intro A_val B_val C_val D_val
      dsimp [P]
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro σ _
      apply Finset.sum_congr rfl; intro α _
      apply Finset.sum_congr rfl; intro β _
      ring

    match A, B, C, D with
    | 0, 0, 0, 0 =>
      rw [h_rhs_eq_P 0 0 0 0]
      change Λ = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 0, 0, 0, 1 =>
      rw [h_rhs_eq_P 0 0 0 1]
      change (0:ℂ) = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 0, 0, 1, 0 =>
      rw [h_rhs_eq_P 0 0 1 0]
      change (0:ℂ) = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 0, 0, 1, 1 =>
      rw [h_rhs_eq_P 0 0 1 1]
      change (0:ℂ) = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 0, 1, 0, 0 =>
      rw [h_rhs_eq_P 0 1 0 0]
      change (0:ℂ) = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 0, 1, 0, 1 =>
      rw [h_rhs_eq_P 0 1 0 1]
      change (1/2:ℂ) * Λ = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 0, 1, 1, 0 =>
      rw [h_rhs_eq_P 0 1 1 0]
      change (1/2:ℂ) * Λ = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 0, 1, 1, 1 =>
      rw [h_rhs_eq_P 0 1 1 1]
      change (0:ℂ) = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 1, 0, 0, 0 =>
      rw [h_rhs_eq_P 1 0 0 0]
      change (0:ℂ) = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 1, 0, 0, 1 =>
      rw [h_rhs_eq_P 1 0 0 1]
      change (1/2:ℂ) * Λ = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 1, 0, 1, 0 =>
      rw [h_rhs_eq_P 1 0 1 0]
      change (1/2:ℂ) * Λ = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 1, 0, 1, 1 =>
      rw [h_rhs_eq_P 1 0 1 1]
      change (0:ℂ) = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 1, 1, 0, 0 =>
      rw [h_rhs_eq_P 1 1 0 0]
      change (0:ℂ) = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 1, 1, 0, 1 =>
      rw [h_rhs_eq_P 1 1 0 1]
      change (0:ℂ) = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 1, 1, 1, 0 =>
      rw [h_rhs_eq_P 1 1 1 0]
      change (0:ℂ) = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    | 1, 1, 1, 1 =>
      rw [h_rhs_eq_P 1 1 1 1]
      change Λ = P _ _
      simp only [h_rup_00, h_rup_01, h_rup_10, h_rup_11, h_cap_00, h_cap_01, h_cap_10, h_cap_11, P_add_left, P_add_right, P_sub_left, P_sub_right, P_neg_left, P_neg_right, P_smul_left, P_smul_right, p00, p11, p22, p01, p10, p02, p20, p12, p21]
      ring_nf
      try simp only [Complex.I_sq]
      try ring

  have H_final : (if A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 then Λ
   else if A = 1 ∧ B = 1 ∧ C = 1 ∧ D = 1 then Λ
   else if (A = 0 ∧ B = 1 ∨ A = 1 ∧ B = 0) ∧ (C = 0 ∧ D = 1 ∨ C = 1 ∧ D = 0) then (1/2:ℂ) * Λ
   else 0) = 1 * (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ α : Fin 4, ∑ β : Fin 4,
      CGD.Gravity.epsilon4 ρ σ α β * (∑ A' : Fin 2, ∑ B' : Fin 2, eps2_up A A' * eps2_up B B' * capovilla_R F ρ σ A' B') * capovilla_R F α β C D) := by
    rw [H_eval]
    ring
  exact H_final

end CGD.Gravity

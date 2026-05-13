-- FILENAME: CGD/Gravity/Urbantke/Determinant2.lean

import CGD.Gravity.Urbantke.Determinant1

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

/--
IMPLEMENTER NOTE:
The fundamental algebraic invariant of the Urbantke metric.
This theorem proves that for any tensor F representing an su(2) 2-form, 
if F satisfies the Unimodular Plebanski constraint (F ∧ F = Λ I), 
the determinant of its constructed 4x4 Urbantke metric is uniquely fixed 
to a specific scalar value `det_val` dependent ONLY on Λ.
-/
theorem urbantke_det_uniqueness 
  [udi : Litlib.Y1991.capovilla1991pure.UrbantkeDeterminantIdentity Unit CGD.Gravity.epsilon4 eps2 eps2_up]
  (Λ : ℂ) :
  ∃ (det_val : ℂ), 
    ∀ (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ),
      (∀ μ ν, F μ ν = - F ν μ) →
      (∀ μ ν, 
        F μ ν 0 0 = 0 ∧ F μ ν 1 1 = 0 ∧ F μ ν 2 2 = 0 ∧
        F μ ν 2 1 = - F μ ν 1 2 ∧ F μ ν 2 0 = - F μ ν 0 2 ∧ F μ ν 1 0 = - F μ ν 0 1) →
      ((∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
        CGD.Gravity.epsilon4 μ ν ρ σ • (F μ ν * F ρ σ)) = Λ • 1) →
      (cgdUnimodularMetricAdapter F).det = det_val := by
  use (81 / 64 : ℂ) * Λ^6
  intro F h_antisymm h_su2 h_plebanski
  
  have h_symm : ∀ A B : Fin 2, clump A B = clump B A := by
    intro A B; fin_cases A <;> fin_cases B <;> rfl
  have h_surj : Function.Surjective (fun (p : Fin 2 × Fin 2) => clump p.1 p.2) := by
    intro y; fin_cases y
    · exact ⟨(0, 0), rfl⟩
    · exact ⟨(1, 1), rfl⟩
    · exact ⟨(0, 1), rfl⟩
  
  let R : Unit → Fin 4 → Fin 4 → Fin 2 → Fin 2 → ℂ := fun _ μ ν A B => capovilla_R F μ ν A B
  
  let g : Unit → Fin 4 → Fin 4 → ℂ := fun _ μ ν => 
    (I / 2 : ℂ) * (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
      ∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2,
        CGD.Gravity.epsilon4 α β γ δ * R () μ α A B * eps2 B C * R () β γ C D * eps2 D E * R () δ ν E F_idx * eps2 F_idx A)

  let eta : Unit → ℂ := fun _ => (3 * I / 2 : ℂ)
  let invPsi : Unit → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ := fun _ A B C D => 
    (3 * I / 2 : ℂ) * (if A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 then Λ
    else if A = 1 ∧ B = 1 ∧ C = 1 ∧ D = 1 then Λ
    else if (A = 0 ∧ B = 1 ∨ A = 1 ∧ B = 0) ∧ (C = 0 ∧ D = 1 ∨ C = 1 ∧ D = 0) then (1/2:ℂ) * Λ
    else 0)
  let invPsi_3x3 : Unit → Fin 3 → Fin 3 → ℂ := fun _ i j => 
    (3 * I / 2 : ℂ) * (if i = 0 ∧ j = 0 then Λ 
    else if i = 1 ∧ j = 1 then Λ 
    else if i = 2 ∧ j = 2 then (1/2:ℂ) * Λ 
    else 0)

  have h_g_eq : ∀ x μ ν, g x μ ν = (1 / 3 : ℂ) * eta x * 
      (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4,
        ∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2,
          CGD.Gravity.epsilon4 α β γ δ * R x μ α A B * eps2 B C * R x β γ C D * eps2 D E * R x δ ν E F_idx * eps2 F_idx A) := by
    intro x μ ν
    cases x
    dsimp [g, eta]
    calc (I / 2 : ℂ) * (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, ∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, CGD.Gravity.epsilon4 α β γ δ * R () μ α A B * eps2 B C * R () β γ C D * eps2 D E * R () δ ν E F_idx * eps2 F_idx A)
      _ = (1 / 3 : ℂ) * (3 * I / 2 : ℂ) * (∑ α : Fin 4, ∑ β : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 4, ∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2, CGD.Gravity.epsilon4 α β γ δ * R () μ α A B * eps2 B C * R () β γ C D * eps2 D E * R () δ ν E F_idx * eps2 F_idx A) := by ring

  have h_invPsi_eq : ∀ x A B C D,
      let R_up := fun ρ σ A_idx B_idx => (∑ A' : Fin 2, ∑ B' : Fin 2, eps2_up A_idx A' * eps2_up B_idx B' * R x ρ σ A' B');
      invPsi x A B C D =
        eta x * (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ α : Fin 4, ∑ β : Fin 4,
          CGD.Gravity.epsilon4 ρ σ α β * R_up ρ σ A B * R x α β C D) := by
    intro x A B C D
    cases x
    dsimp [invPsi, eta]
    have h_cap := capovilla_invPsi_eq F Λ h_antisymm h_su2 h_plebanski A B C D
    have h_cap_rearrange : (if A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 then Λ else if A = 1 ∧ B = 1 ∧ C = 1 ∧ D = 1 then Λ else if (A = 0 ∧ B = 1 ∨ A = 1 ∧ B = 0) ∧ (C = 0 ∧ D = 1 ∨ C = 1 ∧ D = 0) then (1 / 2 : ℂ) * Λ else 0) =
      (1:ℂ) * (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ α : Fin 4, ∑ β : Fin 4, CGD.Gravity.epsilon4 ρ σ α β * (∑ A' : Fin 2, ∑ B' : Fin 2, eps2_up A A' * eps2_up B B' * capovilla_R F ρ σ A' B') * capovilla_R F α β C D) := h_cap
    calc (3 * I / 2 : ℂ) * (if A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 then Λ else if A = 1 ∧ B = 1 ∧ C = 1 ∧ D = 1 then Λ else if (A = 0 ∧ B = 1 ∨ A = 1 ∧ B = 0) ∧ (C = 0 ∧ D = 1 ∨ C = 1 ∧ D = 0) then (1 / 2 : ℂ) * Λ else 0)
      _ = (3 * I / 2 : ℂ) * (1 * ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ α : Fin 4, ∑ β : Fin 4, CGD.Gravity.epsilon4 ρ σ α β * (∑ A' : Fin 2, ∑ B' : Fin 2, eps2_up A A' * eps2_up B B' * capovilla_R F ρ σ A' B') * capovilla_R F α β C D) := by rw [h_cap_rearrange]
      _ = (3 * I / 2 : ℂ) * (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ α : Fin 4, ∑ β : Fin 4, CGD.Gravity.epsilon4 ρ σ α β * (∑ A' : Fin 2, ∑ B' : Fin 2, eps2_up A A' * eps2_up B B' * R () ρ σ A' B') * R () α β C D) := by ring

  have h_invPsi_3x3_eq : ∀ x A B C D, invPsi_3x3 x (clump A B) (clump C D) = invPsi x A B C D := by
    intro x A B C D
    cases x
    fin_cases A <;> fin_cases B <;> fin_cases C <;> fin_cases D <;> rfl

  have h_det_id := udi.determinant_identity R g eta invPsi invPsi_3x3 clump h_symm h_surj h_g_eq h_invPsi_eq h_invPsi_3x3_eq ()
  
  have h_det_smul : Matrix.det (invPsi_3x3 ()) = (3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3) := by
    dsimp [invPsi_3x3]
    rw [Matrix.det_fin_three]
    simp
    ring
  
  have h_g_adapter : g () = cgdUnimodularMetricAdapter F := by
    ext μ ν
    exact (capovilla_g_eq F μ ν h_antisymm).symm

  have h_det_g_adapter : Matrix.det (g ()) = Matrix.det (cgdUnimodularMetricAdapter F) := by
    rw [h_g_adapter]
  
  have h_eta_val : eta () = 3 * I / 2 := rfl
  have h_left : Matrix.det (g ()) * (eta ())^2 = Matrix.det (g ()) * (-9 / 4 : ℂ) := by
    calc Matrix.det (g ()) * (eta ())^2 = Matrix.det (g ()) * (3 * I / 2)^2 := by rw [h_eta_val]
      _ = Matrix.det (g ()) * (9 * I^2 / 4) := by ring
      _ = Matrix.det (g ()) * (-9 / 4) := by rw [Complex.I_sq]; ring

  have h_right : (Matrix.det (invPsi_3x3 ()))^2 = (-729 / 256 : ℂ) * Λ^6 := by
    calc (Matrix.det (invPsi_3x3 ()))^2 = ((3 * I / 2)^3 * ((1/2:ℂ) * Λ^3))^2 := by rw [h_det_smul]
      _ = ((27 * I^3 / 8) * ((1/2:ℂ) * Λ^3))^2 := by ring
      _ = ((27 * (I^2 * I) / 8) * ((1/2:ℂ) * Λ^3))^2 := by ring
      _ = ((27 * ((-1) * I) / 8) * ((1/2:ℂ) * Λ^3))^2 := by rw [Complex.I_sq]
      _ = ((-27 * I / 8) * ((1/2:ℂ) * Λ^3))^2 := by ring
      _ = (-27 * I / 16 * Λ^3)^2 := by ring
      _ = (729 * I^2 / 256) * Λ^6 := by ring
      _ = (729 * (-1) / 256) * Λ^6 := by rw [Complex.I_sq]
      _ = (-729 / 256 : ℂ) * Λ^6 := by ring
  
  calc Matrix.det (cgdUnimodularMetricAdapter F) = Matrix.det (g ()) := h_det_g_adapter.symm
  _ = (-4 / 9 : ℂ) * (Matrix.det (g ()) * (-9 / 4 : ℂ)) := by ring
  _ = (-4 / 9 : ℂ) * (Matrix.det (g ()) * (eta ())^2) := by rw [h_left]
  _ = (-4 / 9 : ℂ) * (Matrix.det (invPsi_3x3 ()))^2 := by rw [h_det_id]
  _ = (-4 / 9 : ℂ) * ((-729 / 256 : ℂ) * Λ^6) := by rw [h_right]
  _ = (81 / 64 : ℂ) * Λ^6 := by ring

end CGD.Gravity

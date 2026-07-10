-- FILENAME: CGD/Cosmology/ParityInversion.lean

import Litlib.Core
import CGD.Cosmology.Definitions
import CGD.Gravity.Geometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CGD.Axioms.PhysicalUniverse

set_option linter.unusedSimpArgs false

open CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms CGD.Foundations

namespace CGD.Cosmology

noncomputable def pontryaginDensity (F : Fin 4 → Fin 4 → SL2C) : Complex :=
  ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsilon4 μ ν ρ σ * Matrix.trace ((F μ ν).val * (F ρ σ).val)

@[simp] lemma f_0_0 : (0 : Fin 4) = 0 ↔ True := by simp
@[simp] lemma f_0_1 : (0 : Fin 4) = 1 ↔ False := by decide
@[simp] lemma f_0_2 : (0 : Fin 4) = 2 ↔ False := by decide
@[simp] lemma f_0_3 : (0 : Fin 4) = 3 ↔ False := by decide
@[simp] lemma f_1_0 : (1 : Fin 4) = 0 ↔ False := by decide
@[simp] lemma f_1_1 : (1 : Fin 4) = 1 ↔ True := by simp
@[simp] lemma f_1_2 : (1 : Fin 4) = 2 ↔ False := by decide
@[simp] lemma f_1_3 : (1 : Fin 4) = 3 ↔ False := by decide
@[simp] lemma f_2_0 : (2 : Fin 4) = 0 ↔ False := by decide
@[simp] lemma f_2_1 : (2 : Fin 4) = 1 ↔ False := by decide
@[simp] lemma f_2_2 : (2 : Fin 4) = 2 ↔ True := by simp
@[simp] lemma f_2_3 : (2 : Fin 4) = 3 ↔ False := by decide
@[simp] lemma f_3_0 : (3 : Fin 4) = 0 ↔ False := by decide
@[simp] lemma f_3_1 : (3 : Fin 4) = 1 ↔ False := by decide
@[simp] lemma f_3_2 : (3 : Fin 4) = 2 ↔ False := by decide
@[simp] lemma f_3_3 : (3 : Fin 4) = 3 ↔ True := by simp

lemma sum_fin_4 (f : Fin 4 → Complex) : ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := by
  simp only[Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + f 3)) = f 0 + f 1 + f 2 + f 3
  ring

lemma trace_neg_val (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace (-A) = - Matrix.trace A := by
  unfold Matrix.trace Matrix.diag
  simp only[Fin.sum_univ_two, Matrix.neg_apply]
  ring

lemma neg_mul_val (A B : Matrix (Fin 2) (Fin 2) ℂ) : -A * B = -(A * B) := neg_mul A B
lemma mul_neg_val (A B : Matrix (Fin 2) (Fin 2) ℂ) : A * -B = -(A * B) := mul_neg A B

lemma eps_zero_12_int (k l : Fin 4) (i : Fin 4) : epsilon4_int i i k l = 0 := by revert i k l; decide
@[simp] lemma eps_zero_12 (k l : Fin 4) (i : Fin 4) : epsilon4 i i k l = 0 := by
  unfold epsilon4; exact_mod_cast eps_zero_12_int k l i

lemma eps_zero_13_int (j l : Fin 4) (i : Fin 4) : epsilon4_int i j i l = 0 := by revert i j l; decide
@[simp] lemma eps_zero_13 (j l : Fin 4) (i : Fin 4) : epsilon4 i j i l = 0 := by
  unfold epsilon4; exact_mod_cast eps_zero_13_int j l i

lemma eps_zero_14_int (j k : Fin 4) (i : Fin 4) : epsilon4_int i j k i = 0 := by revert i j k; decide
@[simp] lemma eps_zero_14 (j k : Fin 4) (i : Fin 4) : epsilon4 i j k i = 0 := by
  unfold epsilon4; exact_mod_cast eps_zero_14_int j k i

lemma eps_zero_23_int (i l : Fin 4) (j : Fin 4) : epsilon4_int i j j l = 0 := by revert i j l; decide
@[simp] lemma eps_zero_23 (i l : Fin 4) (j : Fin 4) : epsilon4 i j j l = 0 := by
  unfold epsilon4; exact_mod_cast eps_zero_23_int i l j

lemma eps_zero_24_int (i k : Fin 4) (j : Fin 4) : epsilon4_int i j k j = 0 := by revert i j k; decide
@[simp] lemma eps_zero_24 (i k : Fin 4) (j : Fin 4) : epsilon4 i j k j = 0 := by
  unfold epsilon4; exact_mod_cast eps_zero_24_int i k j

lemma eps_zero_34_int (i j : Fin 4) (k : Fin 4) : epsilon4_int i j k k = 0 := by revert i j k; decide
@[simp] lemma eps_zero_34 (i j : Fin 4) (k : Fin 4) : epsilon4 i j k k = 0 := by
  unfold epsilon4; exact_mod_cast eps_zero_34_int i j k

lemma P_F_eq (F P_F : Fin 4 → Fin 4 → SL2C)
  (h_parity_0i : ∀ i : Fin 4, i ≠ 0 → (P_F 0 i).val = -(F 0 i).val ∧ (P_F i 0).val = -(F i 0).val)
  (h_parity_ij : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → (P_F i j).val = (F i j).val)
  (h_parity_00 : (P_F 0 0).val = (F 0 0).val)
  (μ ν : Fin 4) :
  (P_F μ ν).val =
    if μ = 0 ∧ ν = 0 then (F 0 0).val
    else if μ = 0 then -(F 0 ν).val
    else if ν = 0 then -(F μ 0).val
    else (F μ ν).val := by
  split_ifs with h1 h2 h3
  · rcases h1 with ⟨rfl, rfl⟩
    exact h_parity_00
  · have h_nu : ν ≠ 0 := by rintro rfl; exact h1 ⟨h2, rfl⟩
    subst h2
    exact (h_parity_0i ν h_nu).1
  · have h_mu : μ ≠ 0 := h2
    subst h3
    exact (h_parity_0i μ h_mu).2
  · have h_mu : μ ≠ 0 := h2
    have h_nu : ν ≠ 0 := h3
    exact h_parity_ij μ ν h_mu h_nu

/--
Negating the electric (temporal) components of the field strength tensor while preserving the magnetic (spatial) components inverts the sign of the fully antisymmetric topological density. This directly links the parity inversion of the local geometry to the negation of the topological charge (Pontryagin density), seamlessly mapping the geometric arrow of time to matter/antimatter asymmetry.
-/
@[litlib_track "Geometric Parity Inversion"]
theorem kinematicParityInversion (pu : PhysicalUniverse) :
  ∀ (x : SpacetimePoint) (P_F : Fin 4 → Fin 4 → SL2C),
    isParityInvertedTensor (fun m n => curvatureSl2c pu.toUniverse.sd_sector m n x) P_F x →
    pontryaginDensity P_F = - pontryaginDensity (fun mu nu => curvatureSl2c pu.toUniverse.sd_sector mu nu x) := by
  intro x P_F ⟨h_parity_0i, h_parity_ij, h_parity_00⟩
  have h_PF : ∀ μ ν, (P_F μ ν).val =
    if μ = 0 ∧ ν = 0 then (curvatureSl2c pu.toUniverse.sd_sector 0 0 x).val
    else if μ = 0 then -(curvatureSl2c pu.toUniverse.sd_sector 0 ν x).val
    else if ν = 0 then -(curvatureSl2c pu.toUniverse.sd_sector μ 0 x).val
    else (curvatureSl2c pu.toUniverse.sd_sector μ ν x).val := by
      intro m n
      exact P_F_eq _ _ h_parity_0i h_parity_ij h_parity_00 m n

  unfold pontryaginDensity
  simp only [sum_fin_4]
  simp only [h_PF]
  simp only[f_0_0, f_0_1, f_0_2, f_0_3, f_1_0, f_1_1, f_1_2, f_1_3, f_2_0, f_2_1, f_2_2, f_2_3, f_3_0, f_3_1, f_3_2, f_3_3, and_true, and_false, false_and, if_true, if_false]
  simp only[eps_zero_12, eps_zero_13, eps_zero_14, eps_zero_23, eps_zero_24, eps_zero_34]
  simp only[zero_mul, add_zero, zero_add]
  simp only[neg_mul_val, mul_neg_val, trace_neg_val, neg_mul, mul_neg]
  ring

end CGD.Cosmology

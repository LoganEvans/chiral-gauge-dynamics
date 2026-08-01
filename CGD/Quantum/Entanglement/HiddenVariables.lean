-- FILENAME: CGD/Quantum/Entanglement/HiddenVariables.lean

import Litlib.Core
import CGD.Quantum.Entanglement.CHSH
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

open MeasureTheory
open Litlib.Y1964.bell1964einstein
open scoped InnerProductSpace

namespace CGD.Quantum

noncomputable def hvVecA (i : Fin 3) : ℝ := match i.val with | 0 => 1 | _ => 0
noncomputable def hvA : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm hvVecA

@[simp] lemma hvA_0 : hvA 0 = 1 := rfl
@[simp] lemma hvA_1 : hvA 1 = 0 := rfl
@[simp] lemma hvA_2 : hvA 2 = 0 := rfl

lemma norm_hvA : ‖hvA‖ = 1 := by
  have H : ‖hvA‖^2 = 1 := by rw [norm_sq_eq_sum, hvA_0, hvA_1, hvA_2]; norm_num
  nlinarith [norm_nonneg hvA]

noncomputable def hvVecD (i : Fin 3) : ℝ := match i.val with | 1 => 1 | _ => 0
noncomputable def hvD : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm hvVecD

@[simp] lemma hvD_0 : hvD 0 = 0 := rfl
@[simp] lemma hvD_1 : hvD 1 = 1 := rfl
@[simp] lemma hvD_2 : hvD 2 = 0 := rfl

lemma norm_hvD : ‖hvD‖ = 1 := by
  have H : ‖hvD‖^2 = 1 := by rw [norm_sq_eq_sum, hvD_0, hvD_1, hvD_2]; norm_num
  nlinarith [norm_nonneg hvD]

noncomputable def hvVecB (i : Fin 3) : ℝ := match i.val with | 0 => 4/5 | 1 => 3/5 | _ => 0
noncomputable def hvB : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm hvVecB

@[simp] lemma hvB_0 : hvB 0 = 4/5 := rfl
@[simp] lemma hvB_1 : hvB 1 = 3/5 := rfl
@[simp] lemma hvB_2 : hvB 2 = 0 := rfl

lemma norm_hvB : ‖hvB‖ = 1 := by
  have H : ‖hvB‖^2 = 1 := by rw [norm_sq_eq_sum, hvB_0, hvB_1, hvB_2]; norm_num
  nlinarith [norm_nonneg hvB]

noncomputable def hvVecC (i : Fin 3) : ℝ := match i.val with | 0 => 4/5 | 1 => -3/5 | _ => 0
noncomputable def hvC : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm hvVecC

@[simp] lemma hvC_0 : hvC 0 = 4/5 := rfl
@[simp] lemma hvC_1 : hvC 1 = -3/5 := rfl
@[simp] lemma hvC_2 : hvC 2 = 0 := rfl

lemma norm_hvC : ‖hvC‖ = 1 := by
  have H : ‖hvC‖^2 = 1 := by rw [norm_sq_eq_sum, hvC_0, hvC_1, hvC_2]; norm_num
  nlinarith [norm_nonneg hvC]

lemma chsh_pointwise (A_a A_d B_b B_c : ℝ) (hAa : A_a = 1 ∨ A_a = -1) (hAd : A_d = 1 ∨ A_d = -1) (hBb : B_b = 1 ∨ B_b = -1) (hBc : B_c = 1 ∨ B_c = -1) :
  - (A_a * B_b) - (A_a * B_c) - (A_d * B_b) + (A_d * B_c) ≤ 2 := by
  rcases hAa with rfl | rfl <;> rcases hAd with rfl | rfl <;> rcases hBb with rfl | rfl <;> rcases hBc with rfl | rfl <;> norm_num

@[litlib_track "Integrated CHSH Absolute Bound"]
lemma chsh_integral_bound (Λ : Type*) [MeasurableSpace Λ] (μ : Measure Λ)
  (A B : EuclideanSpace ℝ (Fin 3) → Λ → ℝ)
  (h_mu : μ Set.univ = 1)
  (hA : ∀ a lam, ‖a‖ = 1 → A a lam = 1 ∨ A a lam = -1)
  (hB : ∀ b lam, ‖b‖ = 1 → B b lam = 1 ∨ B b lam = -1)
  (h_int : ∀ x y, ‖x‖ = 1 → ‖y‖ = 1 → Integrable (fun lam => A x lam * B y lam) μ)
  (a d b c : EuclideanSpace ℝ (Fin 3))
  (ha : ‖a‖ = 1) (hd : ‖d‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
  - (∫ lam, A a lam * B b lam ∂μ) - (∫ lam, A a lam * B c lam ∂μ) -
  (∫ lam, A d lam * B b lam ∂μ) + (∫ lam, A d lam * B c lam ∂μ) ≤ 2 := by
  
  have i1 := h_int a b ha hb
  have i2 := h_int a c ha hc
  have i3 := h_int d b hd hb
  have i4 := h_int d c hd hc
  
  have int_neg_1 : Integrable (fun lam => -(A a lam * B b lam)) μ := Integrable.neg i1
  have int_sub_2 : Integrable (fun lam => -(A a lam * B b lam) - (A a lam * B c lam)) μ := Integrable.sub int_neg_1 i2
  have int_sub_3 : Integrable (fun lam => -(A a lam * B b lam) - (A a lam * B c lam) - (A d lam * B b lam)) μ := Integrable.sub int_sub_2 i3
  
  have H_split : ∫ lam, -(A a lam * B b lam) - (A a lam * B c lam) - (A d lam * B b lam) + (A d lam * B c lam) ∂μ =
      - (∫ lam, A a lam * B b lam ∂μ) - (∫ lam, A a lam * B c lam ∂μ) -
      (∫ lam, A d lam * B b lam ∂μ) + (∫ lam, A d lam * B c lam ∂μ) := by
    rw [integral_add int_sub_3 i4, integral_sub int_sub_2 i3, integral_sub int_neg_1 i2, integral_neg]
      
  rw [← H_split]
  haveI : IsProbabilityMeasure μ := ⟨h_mu⟩
  have h_int_const : Integrable (fun _ : Λ => (2 : ℝ)) μ := integrable_const (2 : ℝ)
  
  have h_int_f : Integrable (fun lam => -(A a lam * B b lam) - (A a lam * B c lam) - (A d lam * B b lam) + (A d lam * B c lam)) μ := Integrable.add int_sub_3 i4
    
  have h_le : ∀ lam, -(A a lam * B b lam) - (A a lam * B c lam) - (A d lam * B b lam) + (A d lam * B c lam) ≤ 2 := by
    intro lam
    apply chsh_pointwise (A a lam) (A d lam) (B b lam) (B c lam)
    · exact hA a lam ha
    · exact hA d lam hd
    · exact hB b lam hb
    · exact hB c lam hc
    
  have h_mono := integral_mono h_int_f h_int_const h_le
  
  have h_int_2 : ∫ _ : Λ, (2 : ℝ) ∂μ = 2 := by
    rw [integral_const]
    change (μ Set.univ).toReal • (2 : ℝ) = 2
    rw [h_mu]
    have h_one : (1 : ENNReal).toReal = 1 := ENNReal.toReal_one
    rw [h_one]
    exact one_smul ℝ (2 : ℝ)
    
  rw [h_int_2] at h_mono
  exact h_mono

@[litlib_track "LHV Cannot Represent Exact Singlet"]
theorem cannot_represent_exactly_proof (Λ : Type*) [MeasurableSpace Λ] :
  ¬ ∃ (μ : Measure Λ) (A B : EuclideanSpace ℝ (Fin 3) → Λ → ℝ),
    (μ Set.univ = 1) ∧
    (∀ a lam, ‖a‖ = 1 → A a lam = 1 ∨ A a lam = -1) ∧
    (∀ b lam, ‖b‖ = 1 → B b lam = 1 ∨ B b lam = -1) ∧
    (∀ a b, ‖a‖ = 1 → ‖b‖ = 1 → Integrable (fun lam => A a lam * B b lam) μ) ∧
    (∀ a b, ‖a‖ = 1 → ‖b‖ = 1 →
      ∫ lam, A a lam * B b lam ∂μ = - ∑ i : Fin 3, a i * b i) := by
  intro h_exists
  rcases h_exists with ⟨μ, A, B, h_mu, hA, hB, h_int, h_eq⟩
  have h_bound := chsh_integral_bound Λ μ A B h_mu hA hB h_int hvA hvD hvB hvC norm_hvA norm_hvD norm_hvB norm_hvC
  
  rw [h_eq hvA hvB norm_hvA norm_hvB] at h_bound
  rw [h_eq hvA hvC norm_hvA norm_hvC] at h_bound
  rw [h_eq hvD hvB norm_hvD norm_hvB] at h_bound
  rw [h_eq hvD hvC norm_hvD norm_hvC] at h_bound
  
  have h_ab : (∑ i : Fin 3, hvA i * hvB i) = 4/5 := by
    have H : (∑ i : Fin 3, hvA i * hvB i) = hvA 0 * hvB 0 + hvA 1 * hvB 1 + hvA 2 * hvB 2 := by simp [Fin.sum_univ_succ]
    rw [H]; norm_num
  have h_ac : (∑ i : Fin 3, hvA i * hvC i) = 4/5 := by
    have H : (∑ i : Fin 3, hvA i * hvC i) = hvA 0 * hvC 0 + hvA 1 * hvC 1 + hvA 2 * hvC 2 := by simp [Fin.sum_univ_succ]
    rw [H]; norm_num
  have h_db : (∑ i : Fin 3, hvD i * hvB i) = 3/5 := by
    have H : (∑ i : Fin 3, hvD i * hvB i) = hvD 0 * hvB 0 + hvD 1 * hvB 1 + hvD 2 * hvB 2 := by simp [Fin.sum_univ_succ]
    rw [H]; norm_num
  have h_dc : (∑ i : Fin 3, hvD i * hvC i) = -3/5 := by
    have H : (∑ i : Fin 3, hvD i * hvC i) = hvD 0 * hvC 0 + hvD 1 * hvC 1 + hvD 2 * hvC 2 := by simp [Fin.sum_univ_succ]
    rw [H]; norm_num
  
  rw [h_ab, h_ac, h_db, h_dc] at h_bound
  revert h_bound
  norm_num

@[litlib_track "LHV Cannot Represent Arbitrarily Closely"]
theorem cannot_represent_approx_proof (Λ : Type*) [MeasurableSpace Λ] :
  ¬ ∀ (ε : ℝ), ε > 0 →
    ∃ (μ : Measure Λ) (A B : EuclideanSpace ℝ (Fin 3) → Λ → ℝ),
      (μ Set.univ = 1) ∧
      (∀ a lam, ‖a‖ = 1 → A a lam = 1 ∨ A a lam = -1) ∧
      (∀ b lam, ‖b‖ = 1 → B b lam = 1 ∨ B b lam = -1) ∧
      (∀ a b, ‖a‖ = 1 → ‖b‖ = 1 → Integrable (fun lam => A a lam * B b lam) μ) ∧
      (∀ a b, ‖a‖ = 1 → ‖b‖ = 1 →
        |(∫ lam, A a lam * B b lam ∂μ) - (- ∑ i : Fin 3, a i * b i)| < ε) := by
  intro h_forall
  have h_exists := h_forall (1/10 : ℝ) (by norm_num)
  rcases h_exists with ⟨μ, A, B, h_mu, hA, hB, h_int, h_approx⟩
  have h_bound := chsh_integral_bound Λ μ A B h_mu hA hB h_int hvA hvD hvB hvC norm_hvA norm_hvD norm_hvB norm_hvC
  
  have h_ab := h_approx hvA hvB norm_hvA norm_hvB
  have h_ac := h_approx hvA hvC norm_hvA norm_hvC
  have h_db := h_approx hvD hvB norm_hvD norm_hvB
  have h_dc := h_approx hvD hvC norm_hvD norm_hvC
  
  have dot_ab : (∑ i : Fin 3, hvA i * hvB i) = 4/5 := by
    have H : (∑ i : Fin 3, hvA i * hvB i) = hvA 0 * hvB 0 + hvA 1 * hvB 1 + hvA 2 * hvB 2 := by simp [Fin.sum_univ_succ]
    rw [H]; norm_num
  have dot_ac : (∑ i : Fin 3, hvA i * hvC i) = 4/5 := by
    have H : (∑ i : Fin 3, hvA i * hvC i) = hvA 0 * hvC 0 + hvA 1 * hvC 1 + hvA 2 * hvC 2 := by simp [Fin.sum_univ_succ]
    rw [H]; norm_num
  have dot_db : (∑ i : Fin 3, hvD i * hvB i) = 3/5 := by
    have H : (∑ i : Fin 3, hvD i * hvB i) = hvD 0 * hvB 0 + hvD 1 * hvB 1 + hvD 2 * hvB 2 := by simp [Fin.sum_univ_succ]
    rw [H]; norm_num
  have dot_dc : (∑ i : Fin 3, hvD i * hvC i) = -3/5 := by
    have H : (∑ i : Fin 3, hvD i * hvC i) = hvD 0 * hvC 0 + hvD 1 * hvC 1 + hvD 2 * hvC 2 := by simp [Fin.sum_univ_succ]
    rw [H]; norm_num
    
  rw [dot_ab] at h_ab
  rw [dot_ac] at h_ac
  rw [dot_db] at h_db
  rw [dot_dc] at h_dc
  
  have I_ab_lt : (∫ lam, A hvA lam * B hvB lam ∂μ) < -7/10 := by
    have H1 := (abs_lt.mp h_ab).2
    linarith
  have I_ac_lt : (∫ lam, A hvA lam * B hvC lam ∂μ) < -7/10 := by
    have H1 := (abs_lt.mp h_ac).2
    linarith
  have I_db_lt : (∫ lam, A hvD lam * B hvB lam ∂μ) < -1/2 := by
    have H1 := (abs_lt.mp h_db).2
    linarith
  have I_dc_gt : (∫ lam, A hvD lam * B hvC lam ∂μ) > 1/2 := by
    have H1 := (abs_lt.mp h_dc).1
    linarith
    
  linarith

@[litlib_track "CGD Geometric Trace Derives Bell's Conclusion"]
theorem cgdDerivesBellConclusion :
  Litlib.Y1964.bell1964einstein.Theorem_Conclusion :=
  {
    cannot_represent_exactly := cannot_represent_exactly_proof
    cannot_represent_arbitrarily_closely := cannot_represent_approx_proof
  }

end CGD.Quantum

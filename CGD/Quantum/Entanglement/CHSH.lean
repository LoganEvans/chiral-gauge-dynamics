-- FILENAME: CGD/Quantum/Entanglement/CHSH.lean

import CGD.Quantum.Entanglement.Algebra
import Litlib.Core
import Litlib.Y1964.bell1964einstein.Signature

set_option autoImplicit false

open Litlib.Y1964.bell1964einstein

namespace CGD.Quantum

noncomputable def vecA (i : Fin 3) : ℝ := match i.val with | 0 => 1 | _ => 0
noncomputable def valA : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm vecA

@[simp] lemma valA_0 : valA 0 = 1 := rfl
@[simp] lemma valA_1 : valA 1 = 0 := rfl
@[simp] lemma valA_2 : valA 2 = 0 := rfl

lemma norm_valA : ‖valA‖ = 1 := by
  have H : ‖valA‖^2 = 1 := by rw [norm_sq_eq_sum, valA_0, valA_1, valA_2]; norm_num
  nlinarith [norm_nonneg valA]

noncomputable def vecB (i : Fin 3) : ℝ := match i.val with | 0 => 4/5 | 1 => 3/5 | _ => 0
noncomputable def valB : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm vecB

@[simp] lemma valB_0 : valB 0 = 4/5 := rfl
@[simp] lemma valB_1 : valB 1 = 3/5 := rfl
@[simp] lemma valB_2 : valB 2 = 0 := rfl

lemma norm_valB : ‖valB‖ = 1 := by
  have H : ‖valB‖^2 = 1 := by rw [norm_sq_eq_sum, valB_0, valB_1, valB_2]; norm_num
  nlinarith [norm_nonneg valB]

noncomputable def vecC (i : Fin 3) : ℝ := match i.val with | 0 => -4/5 | 1 => 3/5 | _ => 0
noncomputable def valC : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm vecC

@[simp] lemma valC_0 : valC 0 = -4/5 := rfl
@[simp] lemma valC_1 : valC 1 = 3/5 := rfl
@[simp] lemma valC_2 : valC 2 = 0 := rfl

lemma norm_valC : ‖valC‖ = 1 := by
  have H : ‖valC‖^2 = 1 := by rw [norm_sq_eq_sum, valC_0, valC_1, valC_2]; norm_num
  nlinarith [norm_nonneg valC]

lemma corr_AB : cgdMacroscopicCorrelation valA valB = 4/5 := by
  rw [cgd_corr_eq_dot, valA_0, valA_1, valA_2, valB_0, valB_1, valB_2]; norm_num

lemma corr_AC : cgdMacroscopicCorrelation valA valC = -4/5 := by
  rw [cgd_corr_eq_dot, valA_0, valA_1, valA_2, valC_0, valC_1, valC_2]; norm_num

lemma corr_BC : cgdMacroscopicCorrelation valB valC = -7/25 := by
  rw [cgd_corr_eq_dot, valB_0, valB_1, valB_2, valC_0, valC_1, valC_2]; norm_num

@[litlib_track "Algebraic Trigonometric Violation Witness"]
lemma cgdAlgebraicViolationWitness :
  ∃ (a b c : EuclideanSpace ℝ (Fin 3)), 
    ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ ‖c‖ = 1 ∧ 
    1 + cgdMacroscopicCorrelation b c < |cgdMacroscopicCorrelation a b - cgdMacroscopicCorrelation a c| := by
  use valA, valB, valC
  refine ⟨norm_valA, norm_valB, norm_valC, ?_⟩
  rw [corr_AB, corr_AC, corr_BC]
  norm_num

@[litlib_track "CGD Violates Bell Inequality Bound"]
theorem cgdViolatesBellInequality : ¬ Eq15 cgdMacroscopicCorrelation := by
  intro h
  rcases cgdAlgebraicViolationWitness with ⟨a, b, c, ha, hb, hc, h_viol⟩
  have h_bound := h.bellInequality a b c ha hb hc
  linarith [h_viol, h_bound]

end CGD.Quantum

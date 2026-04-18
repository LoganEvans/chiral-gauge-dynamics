-- FILENAME: CGD/AntiSelfDualSector/SelfInteracting.lean

import CGD.Axioms.Spacetime
import CGD.Axioms.Ontology
import CGD.Foundations.GaugeGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

set_option linter.unusedSimpArgs false

open CGD.Axioms CGD.Foundations Matrix BigOperators

namespace CGD.AntiSelfDualSector

lemma trace_2x2 (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace A = A 0 0 + A 1 1 := by
  dsimp[Matrix.trace, Matrix.diag]; rw[Fin.sum_univ_two]

lemma mul_2x2 (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw[Matrix.mul_apply, Fin.sum_univ_two]

lemma c11_eq_neg_c00 (C : Matrix (Fin 2) (Fin 2) ℂ) (hTr : Matrix.trace C = 0) : C 1 1 = - C 0 0 := by
  have h_add : C 0 0 + C 1 1 = 0 := by rw [← trace_2x2]; exact hTr
  calc C 1 1 = C 0 0 + C 1 1 - C 0 0 := by ring
    _ = 0 - C 0 0 := by rw [h_add]
    _ = - C 0 0 := by ring

lemma c10_eq_neg_star_c01 (C : Matrix (Fin 2) (Fin 2) ℂ) (hAnti : C.conjTranspose = -C) : C 1 0 = - star (C 0 1) := by
  have h : C.conjTranspose 0 1 = (-C) 0 1 := congr_fun (congr_fun hAnti 0) 1
  change star (C 1 0) = - C 0 1 at h
  have h2 : star (star (C 1 0)) = star (- C 0 1) := congr_arg star h
  simp only [star_star, star_neg] at h2
  exact h2

lemma re_c00_eq_zero (C : Matrix (Fin 2) (Fin 2) ℂ) (hAnti : C.conjTranspose = -C) : (C 0 0).re = 0 := by
  have h : C.conjTranspose 0 0 = (-C) 0 0 := congr_fun (congr_fun hAnti 0) 0
  change star (C 0 0) = - C 0 0 at h
  have h_re : (star (C 0 0)).re = (- C 0 0).re := congr_arg Complex.re h
  have h_re2 : (C 0 0).re = - (C 0 0).re := by
    calc (C 0 0).re = (star (C 0 0)).re := rfl
      _ = (- C 0 0).re := h_re
      _ = - (C 0 0).re := rfl
  linarith

lemma star_mul_self_eq (z : ℂ) : star z * z = (((z.re^2 + z.im^2 : ℝ) : ℂ)) := by
  apply Complex.ext
  · have h1 : (star z * z).re = z.re * z.re - (-z.im) * z.im := rfl
    have h2 : (((z.re^2 + z.im^2 : ℝ) : ℂ)).re = z.re^2 + z.im^2 := rfl
    rw [h1, h2]; ring
  · have h1 : (star z * z).im = z.re * z.im + (-z.im) * z.re := rfl
    have h2 : (((z.re^2 + z.im^2 : ℝ) : ℂ)).im = 0 := rfl
    rw [h1, h2]; ring

lemma sq_of_re_zero (z : ℂ) (hRe : z.re = 0) : z * z = - (((z.im^2 : ℝ) : ℂ)) := by
  apply Complex.ext
  · have h1 : (z * z).re = z.re * z.re - z.im * z.im := rfl
    have h2 : (- (((z.im^2 : ℝ) : ℂ))).re = - z.im^2 := rfl
    rw [h1, h2, hRe]; ring
  · have h1 : (z * z).im = z.re * z.im + z.im * z.re := rfl
    have h2 : (- (((z.im^2 : ℝ) : ℂ))).im = 0 := by simp only [Complex.neg_im, Complex.ofReal_im, neg_zero]
    rw [h1, h2, hRe]; ring

lemma trace_sq_eval (C : Matrix (Fin 2) (Fin 2) ℂ) (hTr : Matrix.trace C = 0) (hAnti : C.conjTranspose = -C) :
  Matrix.trace (C * C) = (-2 : ℂ) * (((C 0 0).im^2 + (C 0 1).re^2 + (C 0 1).im^2 : ℝ) : ℂ) := by
  rw [trace_2x2, mul_2x2, mul_2x2]
  have hc11 := c11_eq_neg_c00 C hTr
  have hc10 := c10_eq_neg_star_c01 C hAnti
  have hRe := re_c00_eq_zero C hAnti
  rw [hc11, hc10]
  have h1 : C 0 0 * C 0 0 = - (((C 0 0).im^2 : ℝ) : ℂ) := sq_of_re_zero _ hRe
  have h2 : (- C 0 0) * (- C 0 0) = - (((C 0 0).im^2 : ℝ) : ℂ) := by
    calc (- C 0 0) * (- C 0 0) = C 0 0 * C 0 0 := by ring
    _ = - (((C 0 0).im^2 : ℝ) : ℂ) := h1
  have h3 : C 0 1 * - star (C 0 1) = - (star (C 0 1) * C 0 1) := by ring
  have h4 : - star (C 0 1) * C 0 1 = - (star (C 0 1) * C 0 1) := by ring
  rw [h1, h2, h3, h4]
  have h5 : star (C 0 1) * C 0 1 = (((C 0 1).re^2 + (C 0 1).im^2 : ℝ) : ℂ) := star_mul_self_eq _
  rw [h5]
  push_cast
  ring

lemma sum_sq_eq_zero (x y z : ℝ) (h : x^2 + y^2 + z^2 = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  have h1 : 0 ≤ x^2 := sq_nonneg x
  have h2 : 0 ≤ y^2 := sq_nonneg y
  have h3 : 0 ≤ z^2 := sq_nonneg z
  have h4 : x^2 = 0 := by linarith
  have h5 : y^2 = 0 := by linarith
  have h6 : z^2 = 0 := by linarith
  exact ⟨sq_eq_zero_iff.mp h4, sq_eq_zero_iff.mp h5, sq_eq_zero_iff.mp h6⟩

lemma c_eq_zero_of_trace_sq_zero (C : Matrix (Fin 2) (Fin 2) ℂ) (hTr : Matrix.trace C = 0) (hAnti : C.conjTranspose = -C)
  (hZ : Matrix.trace (C * C) = 0) : C = 0 := by
  have hEval := trace_sq_eval C hTr hAnti
  rw [hZ] at hEval
  have h_eq : ((C 0 0).im^2 + (C 0 1).re^2 + (C 0 1).im^2 : ℝ) = 0 := by
    have step1 : (-2 : ℂ) * (((C 0 0).im^2 + (C 0 1).re^2 + (C 0 1).im^2 : ℝ) : ℂ) = 0 := hEval.symm
    cases mul_eq_zero.mp step1 with
    | inl h2 => norm_num at h2
    | inr hZero => exact Complex.ofReal_eq_zero.mp hZero
  have h_sqs := sum_sq_eq_zero _ _ _ h_eq
  have h00im : (C 0 0).im = 0 := h_sqs.1
  have h01re : (C 0 1).re = 0 := h_sqs.2.1
  have h01im : (C 0 1).im = 0 := h_sqs.2.2
  have hRe := re_c00_eq_zero C hAnti
  have hc00 : C 0 0 = 0 := Complex.ext hRe h00im
  have hc01 : C 0 1 = 0 := Complex.ext h01re h01im
  have hc11 : C 1 1 = 0 := by rw [c11_eq_neg_c00 C hTr, hc00, neg_zero]
  have hc10 : C 1 0 = 0 := by rw [c10_eq_neg_star_c01 C hAnti, hc01]; simp
  ext i j
  fin_cases i <;> fin_cases j
  · exact hc00
  · exact hc01
  · exact hc10
  · exact hc11

lemma isSu2_comm (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : isSu2 A) (hB : isSu2 B) :
  isSu2 (A * B - B * A) := by
  unfold isSu2 at *
  rcases hA with ⟨hA_tr, hA_anti⟩
  rcases hB with ⟨hB_tr, hB_anti⟩
  constructor
  · rw [Matrix.trace_sub, Matrix.trace_mul_comm]
    exact sub_self _
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    rw [hA_anti, hB_anti]
    have h1 : (-B) * (-A) = B * A := neg_mul_neg B A
    have h2 : (-A) * (-B) = A * B := neg_mul_neg A B
    rw [h1, h2]
    exact (neg_sub (A * B) (B * A)).symm

lemma math_su2_commutator_squared_trace (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : isSu2 A) (hB : isSu2 B) (hNz : A * B - B * A ≠ 0) :
  Matrix.trace ((A * B - B * A) * (A * B - B * A)) ≠ 0 := by
  intro hZ
  have hC_su2 := isSu2_comm A B hA hB
  have hC_eq_0 := c_eq_zero_of_trace_sq_zero _ hC_su2.1 hC_su2.2 hZ
  exact hNz hC_eq_0

/-- 🟡 KINEMATIC: AntiSelfDual Matter is SIDM Physical -/
theorem kinematicSIDMTrace (u : Universe)
  (x : SpacetimePoint) (μ ν : Fin 4)
  (h_anti_self_dual_su2 : ∀ m p, isSu2 (u.anti_self_dual m p).val)
  (h_comm : ((u.anti_self_dual μ x).val * (u.anti_self_dual ν x).val - (u.anti_self_dual ν x).val * (u.anti_self_dual μ x).val) ≠ 0) :
  Matrix.trace (((u.anti_self_dual μ x).val * (u.anti_self_dual ν x).val - (u.anti_self_dual ν x).val * (u.anti_self_dual μ x).val) *
                ((u.anti_self_dual μ x).val * (u.anti_self_dual ν x).val - (u.anti_self_dual ν x).val * (u.anti_self_dual μ x).val)) ≠ 0 := by
  exact math_su2_commutator_squared_trace _ _ (h_anti_self_dual_su2 μ x) (h_anti_self_dual_su2 ν x) h_comm

end CGD.AntiSelfDualSector

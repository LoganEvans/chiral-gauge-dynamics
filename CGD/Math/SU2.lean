-- FILENAME: CGD/Math/SU2.lean

import CGD.Foundations.GaugeGroup
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

open Complex Matrix CGD.Foundations CGD.Math

namespace CGD.Math

lemma su2_trace_sq_nonneg (M : Matrix (Fin 2) (Fin 2) ℂ) (h : isSu2 M) :
  -(Matrix.trace (M * M)).re ≥ 0 := by
  rcases h with ⟨h_tr, h_adj⟩

  -- Extract trace equation
  have h_tr_eq : M 0 0 + M 1 1 = 0 := by
    have : Matrix.trace M = ∑ i, M i i := rfl
    have eval : ∑ i, M i i = M 0 0 + M 1 1 := Fin.sum_univ_two (fun i => M i i)
    rw [this, eval] at h_tr
    exact h_tr

  have h_m11 : M 1 1 = - M 0 0 := by
    calc M 1 1 = (M 0 0 + M 1 1) - M 0 0 := by ring
    _ = 0 - M 0 0 := by rw [h_tr_eq]
    _ = - M 0 0 := by ring

  -- Extract adjoint equations
  have h_adj_00 : star (M 0 0) = - M 0 0 := by
    have : M.conjTranspose 0 0 = (-M) 0 0 := by rw [h_adj]
    have lhs : M.conjTranspose 0 0 = star (M 0 0) := rfl
    have rhs : (-M) 0 0 = - M 0 0 := rfl
    rw [lhs, rhs] at this
    exact this

  have h_adj_10 : star (M 0 1) = - M 1 0 := by
    have : M.conjTranspose 1 0 = (-M) 1 0 := by rw [h_adj]
    have lhs : M.conjTranspose 1 0 = star (M 0 1) := rfl
    have rhs : (-M) 1 0 = - M 1 0 := rfl
    rw [lhs, rhs] at this
    exact this

  have h_m10 : M 1 0 = - star (M 0 1) := by
    calc M 1 0 = - (- M 1 0) := by ring
    _ = - star (M 0 1) := by rw [←h_adj_10]

  -- Expand trace(M*M)
  have h_tr_M2 : Matrix.trace (M * M) = M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 1 0 * M 0 1 + M 1 1 * M 1 1 := by
    have step1 : Matrix.trace (M * M) = ∑ i, (M * M) i i := rfl
    have step1_eval : ∑ i, (M * M) i i = (M * M) 0 0 + (M * M) 1 1 := Fin.sum_univ_two (fun i => (M * M) i i)
    have step2_0 : (M * M) 0 0 = ∑ j, M 0 j * M j 0 := rfl
    have step2_0_eval : ∑ j, M 0 j * M j 0 = M 0 0 * M 0 0 + M 0 1 * M 1 0 := Fin.sum_univ_two (fun j => M 0 j * M j 0)
    have step2_1 : (M * M) 1 1 = ∑ j, M 1 j * M j 1 := rfl
    have step2_1_eval : ∑ j, M 1 j * M j 1 = M 1 0 * M 0 1 + M 1 1 * M 1 1 := Fin.sum_univ_two (fun j => M 1 j * M j 1)
    rw [step1, step1_eval, step2_0, step2_0_eval, step2_1, step2_1_eval]
    ring

  -- Substitute components
  have h_tr_M2_sub : Matrix.trace (M * M) = (2 : ℂ) * (M 0 0 * M 0 0) - (2 : ℂ) * (M 0 1 * star (M 0 1)) := by
    calc Matrix.trace (M * M) = M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 1 0 * M 0 1 + M 1 1 * M 1 1 := h_tr_M2
    _ = M 0 0 * M 0 0 + M 0 1 * (- star (M 0 1)) + (- star (M 0 1)) * M 0 1 + (- M 0 0) * (- M 0 0) := by rw [h_m11, h_m10]
    _ = 2 * (M 0 0 * M 0 0) - 2 * (M 0 1 * star (M 0 1)) := by ring

  -- Analyze M 0 0
  have h_m00_re : (M 0 0).re = 0 := by
    have h1 : (star (M 0 0)).re = (- M 0 0).re := by rw [h_adj_00]
    have h2 : (star (M 0 0)).re = (M 0 0).re := rfl
    have h3 : (- M 0 0).re = - (M 0 0).re := rfl
    linarith [h1, h2, h3]

  have h_m00_sq_re : (M 0 0 * M 0 0).re = - ((M 0 0).im * (M 0 0).im) := by
    have : (M 0 0 * M 0 0).re = (M 0 0).re * (M 0 0).re - (M 0 0).im * (M 0 0).im := rfl
    rw [this, h_m00_re]
    ring

  -- Analyze M 0 1
  have h_m01_sq_re : (M 0 1 * star (M 0 1)).re = (M 0 1).re * (M 0 1).re + (M 0 1).im * (M 0 1).im := by
    have : (M 0 1 * star (M 0 1)).re = (M 0 1).re * (star (M 0 1)).re - (M 0 1).im * (star (M 0 1)).im := rfl
    have hre : (star (M 0 1)).re = (M 0 1).re := rfl
    have him : (star (M 0 1)).im = - (M 0 1).im := rfl
    rw [this, hre, him]
    ring

  -- Take real parts
  have h_lin : ∀ A B : ℂ, ((2:ℂ) * A - (2:ℂ) * B).re = 2 * A.re - 2 * B.re := by
    intro A B
    have eqA : ((2:ℂ) * A).re = 2 * A.re := by
      have : ((2:ℂ) * A).re = (2 : ℂ).re * A.re - (2 : ℂ).im * A.im := rfl
      have re2 : (2 : ℂ).re = 2 := rfl
      have im2 : (2 : ℂ).im = 0 := rfl
      rw [this, re2, im2]
      ring
    have eqB : ((2:ℂ) * B).re = 2 * B.re := by
      have : ((2:ℂ) * B).re = (2 : ℂ).re * B.re - (2 : ℂ).im * B.im := rfl
      have re2 : (2 : ℂ).re = 2 := rfl
      have im2 : (2 : ℂ).im = 0 := rfl
      rw [this, re2, im2]
      ring
    have eqSub : ((2:ℂ) * A - (2:ℂ) * B).re = ((2:ℂ) * A).re - ((2:ℂ) * B).re := rfl
    rw [eqSub, eqA, eqB]

  have h_final_re : (Matrix.trace (M * M)).re = 2 * (M 0 0 * M 0 0).re - 2 * (M 0 1 * star (M 0 1)).re := by
    calc (Matrix.trace (M * M)).re = ((2:ℂ) * (M 0 0 * M 0 0) - (2:ℂ) * (M 0 1 * star (M 0 1))).re := by rw [h_tr_M2_sub]
    _ = 2 * (M 0 0 * M 0 0).re - 2 * (M 0 1 * star (M 0 1)).re := by rw [h_lin]

  -- Conclude
  have h_LHS : -(Matrix.trace (M * M)).re = 2 * ((M 0 0).im * (M 0 0).im) + 2 * ((M 0 1).re * (M 0 1).re) + 2 * ((M 0 1).im * (M 0 1).im) := by
    calc -(Matrix.trace (M * M)).re = - (2 * (M 0 0 * M 0 0).re - 2 * (M 0 1 * star (M 0 1)).re) := by rw [h_final_re]
    _ = - (2 * (- ((M 0 0).im * (M 0 0).im)) - 2 * ((M 0 1).re * (M 0 1).re + (M 0 1).im * (M 0 1).im)) := by rw [h_m00_sq_re, h_m01_sq_re]
    _ = 2 * ((M 0 0).im * (M 0 0).im) + 2 * ((M 0 1).re * (M 0 1).re) + 2 * ((M 0 1).im * (M 0 1).im) := by ring

  rw [h_LHS]

  have p1 : 0 ≤ (M 0 0).im * (M 0 0).im := mul_self_nonneg _
  have p2 : 0 ≤ (M 0 1).re * (M 0 1).re := mul_self_nonneg _
  have p3 : 0 ≤ (M 0 1).im * (M 0 1).im := mul_self_nonneg _
  linarith

lemma su2_trace_sq_pos (M : Matrix (Fin 2) (Fin 2) ℂ) (h1 : isSu2 M) (h2 : M ≠ 0) :
  -(Matrix.trace (M * M)).re > 0 := by
  rcases h1 with ⟨h_tr, h_adj⟩

  have h_tr_eq : M 0 0 + M 1 1 = 0 := by
    have : Matrix.trace M = ∑ i, M i i := rfl
    have eval : ∑ i, M i i = M 0 0 + M 1 1 := Fin.sum_univ_two (fun i => M i i)
    rw [this, eval] at h_tr
    exact h_tr

  have h_m11 : M 1 1 = - M 0 0 := by
    calc M 1 1 = (M 0 0 + M 1 1) - M 0 0 := by ring
    _ = 0 - M 0 0 := by rw [h_tr_eq]
    _ = - M 0 0 := by ring

  have h_adj_00 : star (M 0 0) = - M 0 0 := by
    have : M.conjTranspose 0 0 = (-M) 0 0 := by rw [h_adj]
    exact this

  have h_adj_10 : star (M 0 1) = - M 1 0 := by
    have : M.conjTranspose 1 0 = (-M) 1 0 := by rw [h_adj]
    exact this

  have h_m10 : M 1 0 = - star (M 0 1) := by
    calc M 1 0 = - (- M 1 0) := by ring
    _ = - star (M 0 1) := by rw [←h_adj_10]

  have h_tr_M2 : Matrix.trace (M * M) = M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 1 0 * M 0 1 + M 1 1 * M 1 1 := by
    have step1 : Matrix.trace (M * M) = ∑ i, (M * M) i i := rfl
    have step1_eval : ∑ i, (M * M) i i = (M * M) 0 0 + (M * M) 1 1 := Fin.sum_univ_two (fun i => (M * M) i i)
    have step2_0 : (M * M) 0 0 = M 0 0 * M 0 0 + M 0 1 * M 1 0 := Fin.sum_univ_two (fun j => M 0 j * M j 0)
    have step2_1 : (M * M) 1 1 = M 1 0 * M 0 1 + M 1 1 * M 1 1 := Fin.sum_univ_two (fun j => M 1 j * M j 1)
    rw [step1, step1_eval, step2_0, step2_1]
    ring

  have h_tr_M2_sub : Matrix.trace (M * M) = (2 : ℂ) * (M 0 0 * M 0 0) - (2 : ℂ) * (M 0 1 * star (M 0 1)) := by
    calc Matrix.trace (M * M) = M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 1 0 * M 0 1 + M 1 1 * M 1 1 := h_tr_M2
    _ = M 0 0 * M 0 0 + M 0 1 * (- star (M 0 1)) + (- star (M 0 1)) * M 0 1 + (- M 0 0) * (- M 0 0) := by rw [h_m11, h_m10]
    _ = 2 * (M 0 0 * M 0 0) - 2 * (M 0 1 * star (M 0 1)) := by ring

  have h_m00_re : (M 0 0).re = 0 := by
    have h1 : (star (M 0 0)).re = (- M 0 0).re := by rw [h_adj_00]
    have h2 : (star (M 0 0)).re = (M 0 0).re := rfl
    have h3 : (- M 0 0).re = - (M 0 0).re := rfl
    linarith [h1, h2, h3]

  have h_m00_sq_re : (M 0 0 * M 0 0).re = - ((M 0 0).im * (M 0 0).im) := by
    have : (M 0 0 * M 0 0).re = (M 0 0).re * (M 0 0).re - (M 0 0).im * (M 0 0).im := rfl
    rw [this, h_m00_re]
    ring

  have h_m01_sq_re : (M 0 1 * star (M 0 1)).re = (M 0 1).re * (M 0 1).re + (M 0 1).im * (M 0 1).im := by
    have : (M 0 1 * star (M 0 1)).re = (M 0 1).re * (star (M 0 1)).re - (M 0 1).im * (star (M 0 1)).im := rfl
    have hre : (star (M 0 1)).re = (M 0 1).re := rfl
    have him : (star (M 0 1)).im = - (M 0 1).im := rfl
    rw [this, hre, him]
    ring

  have h_lin : ∀ A B : ℂ, ((2:ℂ) * A - (2:ℂ) * B).re = 2 * A.re - 2 * B.re := by
    intro A B
    have eqA : ((2:ℂ) * A).re = 2 * A.re := by
      have : ((2:ℂ) * A).re = (2 : ℂ).re * A.re - (2 : ℂ).im * A.im := rfl
      have re2 : (2 : ℂ).re = 2 := rfl
      have im2 : (2 : ℂ).im = 0 := rfl
      rw [this, re2, im2]
      ring
    have eqB : ((2:ℂ) * B).re = 2 * B.re := by
      have : ((2:ℂ) * B).re = (2 : ℂ).re * B.re - (2 : ℂ).im * B.im := rfl
      have re2 : (2 : ℂ).re = 2 := rfl
      have im2 : (2 : ℂ).im = 0 := rfl
      rw [this, re2, im2]
      ring
    have eqSub : ((2:ℂ) * A - (2:ℂ) * B).re = ((2:ℂ) * A).re - ((2:ℂ) * B).re := rfl
    rw [eqSub, eqA, eqB]

  have h_final_re : (Matrix.trace (M * M)).re = 2 * (M 0 0 * M 0 0).re - 2 * (M 0 1 * star (M 0 1)).re := by
    calc (Matrix.trace (M * M)).re = ((2:ℂ) * (M 0 0 * M 0 0) - (2:ℂ) * (M 0 1 * star (M 0 1))).re := by rw [h_tr_M2_sub]
    _ = 2 * (M 0 0 * M 0 0).re - 2 * (M 0 1 * star (M 0 1)).re := by rw [h_lin]

  have h_LHS : -(Matrix.trace (M * M)).re = 2 * ((M 0 0).im * (M 0 0).im) + 2 * ((M 0 1).re * (M 0 1).re) + 2 * ((M 0 1).im * (M 0 1).im) := by
    calc -(Matrix.trace (M * M)).re = - (2 * (M 0 0 * M 0 0).re - 2 * (M 0 1 * star (M 0 1)).re) := by rw [h_final_re]
    _ = - (2 * (- ((M 0 0).im * (M 0 0).im)) - 2 * ((M 0 1).re * (M 0 1).re + (M 0 1).im * (M 0 1).im)) := by rw [h_m00_sq_re, h_m01_sq_re]
    _ = 2 * ((M 0 0).im * (M 0 0).im) + 2 * ((M 0 1).re * (M 0 1).re) + 2 * ((M 0 1).im * (M 0 1).im) := by ring

  rw [h_LHS]

  have p1 : 0 ≤ (M 0 0).im * (M 0 0).im := mul_self_nonneg _
  have p2 : 0 ≤ (M 0 1).re * (M 0 1).re := mul_self_nonneg _
  have p3 : 0 ≤ (M 0 1).im * (M 0 1).im := mul_self_nonneg _

  -- Proof by contradiction: if the sum of non-negative squares is NOT > 0, it must be ≤ 0.
  -- Since it's a sum of squares, it must be exactly 0, which forces all terms to be 0.
  by_contra h_not_pos
  push_neg at h_not_pos

  have h_sum_zero : 2 * ((M 0 0).im * (M 0 0).im) + 2 * ((M 0 1).re * (M 0 1).re) + 2 * ((M 0 1).im * (M 0 1).im) = 0 := by
    linarith [h_not_pos, p1, p2, p3]

  have z1 : (M 0 0).im = 0 := by
    have : 2 * ((M 0 0).im * (M 0 0).im) ≤ 0 := by linarith [p2, p3, h_sum_zero]
    have sq_zero : (M 0 0).im * (M 0 0).im = 0 := by linarith [p1]
    exact mul_self_eq_zero.mp sq_zero

  have z2 : (M 0 1).re = 0 := by
    have : 2 * ((M 0 1).re * (M 0 1).re) ≤ 0 := by linarith [p1, p3, h_sum_zero]
    have sq_zero : (M 0 1).re * (M 0 1).re = 0 := by linarith [p2]
    exact mul_self_eq_zero.mp sq_zero

  have z3 : (M 0 1).im = 0 := by
    have : 2 * ((M 0 1).im * (M 0 1).im) ≤ 0 := by linarith [p1, p2, h_sum_zero]
    have sq_zero : (M 0 1).im * (M 0 1).im = 0 := by linarith [p3]
    exact mul_self_eq_zero.mp sq_zero

  have hz_00 : M 0 0 = 0 := Complex.ext h_m00_re z1
  have hz_01 : M 0 1 = 0 := Complex.ext z2 z3
  have hz_11 : M 1 1 = 0 := by rw [h_m11, hz_00, neg_zero]

  have hz_10 : M 1 0 = 0 := by
    calc M 1 0 = - star (M 0 1) := h_m10
    _ = - star (0 : ℂ) := by rw [hz_01]
    _ = 0 := by simp

  have hM_zero : M = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact hz_00
    · exact hz_01
    · exact hz_10
    · exact hz_11

  exact h2 hM_zero

end CGD.Math

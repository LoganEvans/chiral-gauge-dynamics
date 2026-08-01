-- FILENAME: CGD/Quantum/Entanglement/Algebra.lean

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Complex Matrix

namespace CGD.Quantum

noncomputable def cgdMatrix (v : EuclideanSpace ℝ (Fin 3)) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i = 0 ∧ j = 0 then Complex.I * (v 2 : ℂ)
    else if i = 0 ∧ j = 1 then (v 1 : ℂ) + Complex.I * (v 0 : ℂ)
    else if i = 1 ∧ j = 0 then -(v 1 : ℂ) + Complex.I * (v 0 : ℂ)
    else -Complex.I * (v 2 : ℂ)

noncomputable def cgdMacroscopicCorrelation (a b : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ( (1 / 2 : ℂ) * Matrix.trace (cgdMatrix a * (cgdMatrix b).conjTranspose) ).re

lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace M = M 0 0 + M 1 1 := by
  rw [Matrix.trace]
  exact Fin.sum_univ_two (fun i => M i i)

lemma mul_fin2 (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Matrix.mul_apply]
  exact Fin.sum_univ_two (fun k => A i k * B k j)

lemma conjTranspose_eval (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
  A.conjTranspose i j = star (A j i) := rfl

lemma cgdMatrix_0_0 (v : EuclideanSpace ℝ (Fin 3)) : cgdMatrix v 0 0 = Complex.I * (v 2 : ℂ) := rfl

lemma cgdMatrix_0_1 (v : EuclideanSpace ℝ (Fin 3)) : cgdMatrix v 0 1 = (v 1 : ℂ) + Complex.I * (v 0 : ℂ) := rfl

lemma cgdMatrix_1_0 (v : EuclideanSpace ℝ (Fin 3)) : cgdMatrix v 1 0 = -(v 1 : ℂ) + Complex.I * (v 0 : ℂ) := rfl

lemma cgdMatrix_1_1 (v : EuclideanSpace ℝ (Fin 3)) : cgdMatrix v 1 1 = -Complex.I * (v 2 : ℂ) := rfl

lemma cgd_corr_eq_dot (u v : EuclideanSpace ℝ (Fin 3)) :
  cgdMacroscopicCorrelation u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  unfold cgdMacroscopicCorrelation
  rw [trace_fin2, mul_fin2, mul_fin2]
  rw [conjTranspose_eval, conjTranspose_eval, conjTranspose_eval, conjTranspose_eval]
  rw [cgdMatrix_0_0, cgdMatrix_0_1, cgdMatrix_1_0, cgdMatrix_1_1]
  rw [cgdMatrix_0_0, cgdMatrix_0_1, cgdMatrix_1_0, cgdMatrix_1_1]
  have h_half : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have h_half_im : ((1 / 2 : ℂ)).im = 0 := by norm_num
  have h_star_re : ∀ z : ℂ, (star z).re = z.re := fun z => rfl
  have h_star_im : ∀ z : ℂ, (star z).im = -z.im := fun z => rfl
  simp only [h_half, h_half_im, h_star_re, h_star_im,
             Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
             Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
             Complex.neg_re, Complex.neg_im]
  ring

lemma norm_sq_eq_sum (v : EuclideanSpace ℝ (Fin 3)) :
  ‖v‖^2 = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_succ]
  ring

end CGD.Quantum

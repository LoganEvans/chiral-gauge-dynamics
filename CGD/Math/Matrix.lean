-- FILENAME: CGD/Math/Matrix.lean

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Matrix.Normed

open Complex Matrix

namespace CGD.Math

lemma sum_fin_2_expand {M} [AddCommMonoid M] (f : Fin 2 → M) :
  (∑ i : Fin 2, f i) = f 0 + f 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

lemma sum_fin_3_expand {M} [AddCommMonoid M] (f : Fin 3 → M) :
  (∑ i : Fin 3, f i) = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]
  rfl

lemma sum_fin_4_expand {M} [AddCommMonoid M] (f : Fin 4 → M) :
  (∑ i : Fin 4, f i) = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [add_zero, add_assoc]
  rfl

lemma trace_2x2 (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace M = M 0 0 + M 1 1 := by
  unfold Matrix.trace Matrix.diag
  rw [sum_fin_2_expand]

lemma mul_2x2 (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  change (∑ k : Fin 2, A i k * B k j) = _
  rw [sum_fin_2_expand]

lemma trace_mul_2x2 (A B : Matrix (Fin 2) (Fin 2) ℂ) :
  Matrix.trace (A * B) = A 0 0 * B 0 0 + A 0 1 * B 1 0 + A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  rw [trace_2x2, mul_2x2, mul_2x2]
  ring

noncomputable instance matNormedAddCommGroup : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (NormedAddCommGroup (Fin 2 → Fin 2 → ℂ))

noncomputable instance matNormedSpaceC : NormedSpace ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (NormedSpace ℂ (Fin 2 → Fin 2 → ℂ))

noncomputable instance matNormedSpaceR : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (NormedSpace ℝ (Fin 2 → Fin 2 → ℂ))

end CGD.Math

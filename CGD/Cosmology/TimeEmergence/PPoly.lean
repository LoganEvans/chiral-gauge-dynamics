-- FILENAME: CGD/Cosmology/TimeEmergence/PPoly.lean

import Litlib.Core
import CGD.Cosmology.Definitions
import CGD.Gravity.Geometry
import CGD.Foundations.Math
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import CGD.Axioms.Ontology
import CGD.Axioms.Phenomenology

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Cosmology

noncomputable def pMat (x y z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j =>
    if i = 0 ∧ j = 1 then x else if i = 0 ∧ j = 2 then y else if i = 0 ∧ j = 3 then z
    else if i = 1 ∧ j = 0 then -x else if i = 1 ∧ j = 2 then z else if i = 1 ∧ j = 3 then -y
    else if i = 2 ∧ j = 0 then -y else if i = 2 ∧ j = 1 then -z else if i = 2 ∧ j = 3 then x
    else if i = 3 ∧ j = 0 then -z else if i = 3 ∧ j = 1 then y else if i = 3 ∧ j = 2 then -x
    else 0

lemma eval_mul_4x4_3 (A B C : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
  (A * B * C) i j =
    (A i 0 * B 0 0 + A i 1 * B 1 0 + A i 2 * B 2 0 + A i 3 * B 3 0) * C 0 j +
    (A i 0 * B 0 1 + A i 1 * B 1 1 + A i 2 * B 2 1 + A i 3 * B 3 1) * C 1 j +
    (A i 0 * B 0 2 + A i 1 * B 1 2 + A i 2 * B 2 2 + A i 3 * B 3 2) * C 2 j +
    (A i 0 * B 0 3 + A i 1 * B 1 3 + A i 2 * B 2 3 + A i 3 * B 3 3) * C 3 j := by
  simp only [Matrix.mul_apply, sum_fin_4_expand]

lemma P_poly_is_id (x0 x1 x2 y0 y1 y2 z0 z1 z2 : ℂ) :
  ∃ c : ℂ, ((2:ℂ) • (pMat x0 x1 x2 * pMat y0 y1 y2 * pMat z0 z1 z2
                - pMat x0 x1 x2 * pMat z0 z1 z2 * pMat y0 y1 y2
                - pMat y0 y1 y2 * pMat x0 x1 x2 * pMat z0 z1 z2
                + pMat y0 y1 y2 * pMat z0 z1 z2 * pMat x0 x1 x2
                + pMat z0 z1 z2 * pMat x0 x1 x2 * pMat y0 y1 y2
                - pMat z0 z1 z2 * pMat y0 y1 y2 * pMat x0 x1 x2) : Matrix (Fin 4) (Fin 4) ℂ) = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  use 12 * (x0 * y1 * z2 - x0 * y2 * z1 - x1 * y0 * z2 + x1 * y2 * z0 + x2 * y0 * z1 - x2 * y1 * z0)
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp only[Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    simp only [eval_mul_4x4_3]
    simp [pMat, Matrix.one_apply]
    ring
  }

end CGD.Cosmology

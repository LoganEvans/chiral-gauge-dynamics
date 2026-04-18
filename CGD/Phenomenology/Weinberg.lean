-- FILENAME: CGD/Phenomenology/Weinberg.lean

import CGD.Foundations.GaugeGroup
import CGD.Axioms.Spacetime
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CGD.Axioms.Ontology

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Complex Matrix BigOperators
open CGD.Axioms CGD.Foundations

namespace CGD.Phenomenology

variable {n : Type*}[Fintype n][DecidableEq n]

lemma trace_add' (A B : Matrix n n ℂ) : Matrix.trace (A + B) = Matrix.trace A + Matrix.trace B := by
  simp[Matrix.trace, Matrix.diag, Finset.sum_add_distrib]

lemma trace_sub' (A B : Matrix n n ℂ) : Matrix.trace (A - B) = Matrix.trace A - Matrix.trace B := by
  simp[Matrix.trace, Matrix.diag, Finset.sum_sub_distrib]

noncomputable def comm (A B : Matrix n n ℂ) : Matrix n n ℂ := A * B - B * A
noncomputable def fMode (dM M1 M2 : Matrix n n ℂ) : Matrix n n ℂ := dM + comm M1 M2
noncomputable def fV (dV V1 V2 A1 A2 : Matrix n n ℂ) : Matrix n n ℂ := dV + comm V1 V2 + comm A1 A2
noncomputable def dVA (dA V1 V2 A1 A2 : Matrix n n ℂ) : Matrix n n ℂ := dA + comm V1 A2 + comm A1 V2

lemma trace_parallelogram (X Y : Matrix n n ℂ) :
  Matrix.trace ((X + Y) * (X + Y)) + Matrix.trace ((X - Y) * (X - Y)) =
  2 * Matrix.trace (X * X) + 2 * Matrix.trace (Y * Y) := by
  have expand1 : (X + Y) * (X + Y) = X * X + X * Y + Y * X + Y * Y := by
    ext i j
    simp only[Matrix.add_apply, Matrix.mul_apply, smul_eq_mul]
    simp only[add_mul, mul_add]
    simp only[Finset.sum_add_distrib]
    ring
  have expand2 : (X - Y) * (X - Y) = X * X - X * Y - Y * X + Y * Y := by
    ext i j
    simp only[Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, smul_eq_mul]
    simp only[add_mul, mul_add, sub_mul, mul_sub]
    simp only[Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw[expand1, expand2]
  simp[trace_add', trace_sub']
  ring

/-- 🟡 KINEMATIC: Vector-Axial kinetic tracing identity perfectly splits. (Pure Math) -/
theorem algebraicWeinbergDecomposition (_u : Universe) (_x : SpacetimePoint) (_mu _nu : Fin 4) :
  ∀ (dV dA V1 V2 A1 A2 : Matrix (Fin 2) (Fin 2) Complex),
    Matrix.trace (fMode (dV + dA) (V1 + A1) (V2 + A2) * fMode (dV + dA) (V1 + A1) (V2 + A2)) +
    Matrix.trace (fMode (dV - dA) (V1 - A1) (V2 - A2) * fMode (dV - dA) (V1 - A1) (V2 - A2)) =
    2 * Matrix.trace (fV dV V1 V2 A1 A2 * fV dV V1 V2 A1 A2) +
    2 * Matrix.trace (dVA dA V1 V2 A1 A2 * dVA dA V1 V2 A1 A2) := by
  intros dV dA V1 V2 A1 A2
  let X := fV dV V1 V2 A1 A2
  let Y := dVA dA V1 V2 A1 A2
  have h1 : fMode (dV + dA) (V1 + A1) (V2 + A2) = X + Y := by
    unfold X Y fMode fV dVA comm
    ext i j
    simp only[Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, smul_eq_mul]
    simp only[add_mul, mul_add, sub_mul, mul_sub]
    simp only[Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  have h2 : fMode (dV - dA) (V1 - A1) (V2 - A2) = X - Y := by
    unfold X Y fMode fV dVA comm
    ext i j
    simp only[Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, smul_eq_mul]
    simp only[add_mul, mul_add, sub_mul, mul_sub]
    simp only[Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw[h1, h2]
  exact trace_parallelogram X Y

/-- 🔵 ALGEBRAIC: Weinberg Sum Splitting (If Chiral symmetry is broken L ≠ R, the Axial vector A cannot be zero). -/
theorem algebraicWeinbergSumSplitting (V1 A1 : Matrix (Fin 2) (Fin 2) ℂ) :
  let L := V1 + A1;
  let R := V1 - A1;
  L ≠ R → A1 ≠ 0 := by
  intros L R h_neq h_eq
  apply h_neq
  change V1 + A1 = V1 - A1
  rw [h_eq, add_zero, sub_zero]

/-- 🔵 ALGEBRAIC: Axial Truncation Error (Pure Vector Dominance truncates out exactly 2A^2). -/
theorem algebraicAxialTruncationError (V A : Matrix (Fin 2) (Fin 2) ℂ) :
  2 * Matrix.trace (V * V) + 2 * Matrix.trace (A * A) - 2 * Matrix.trace (V * V) = 2 * Matrix.trace (A * A) := by
  ring

end CGD.Phenomenology

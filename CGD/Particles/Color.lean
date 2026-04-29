-- FILENAME: CGD/Particles/Color.lean

import CGD.Foundations.GaugeGroup
import CGD.Particles.Definitions
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Litlib.Core

open CGD.Axioms CGD.Foundations CGD.Gravity Matrix Complex BigOperators

set_option linter.unusedSimpArgs false

namespace CGD.Particles

/-- Pure equation compiler exhaustiveness for Fin 3. -/
lemma fin3_eq_zero : ∀ (x : Fin 3), x ≠ 1 → x ≠ 2 → x = 0
| 0, _, _ => rfl
| 1, h1, _ => False.elim (h1 rfl)
| 2, _, h2 => False.elim (h2 rfl)

lemma sum_fin_2 (f : Fin 2 → Complex) : ∑ i : Fin 2, f i = f 0 + f 1 := by
  rw[Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp

lemma sum_fin_3_expand (f : Fin 3 → Complex) : ∑ i : Fin 3, f i = f 0 + f 1 + f 2 := by
  rw[Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp[add_assoc, add_comm]

lemma mul_2x2 (A B : Matrix (Fin 2) (Fin 2) Complex) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw[Matrix.mul_apply, sum_fin_2]

lemma trace_2x2 (M : Matrix (Fin 2) (Fin 2) Complex) : Matrix.trace M = M 0 0 + M 1 1 := by
  change ∑ i : Fin 2, M i i = _
  rw[sum_fin_2]

lemma sl2c_trace (X : SL2C) : X.1 0 0 + X.1 1 1 = 0 := by
  have h := X.property
  change ∑ i : Fin 2, X.1 i i = 0 at h
  rw [sum_fin_2] at h
  exact h

lemma sl2c_val_1_1 (X : SL2C) : X.1 1 1 = -X.1 0 0 := by
  have h := sl2c_trace X
  calc X.1 1 1 = X.1 0 0 + X.1 1 1 - X.1 0 0 := by ring
    _ = (0 : Complex) - X.1 0 0 := by rw [h]
    _ = -X.1 0 0 := by ring

lemma bracket_eq_sub (A B : SL2C) : ⁅A, B⁆.1 = A.1 * B.1 - B.1 * A.1 := rfl

lemma s1_00 : sigma1.1 0 0 = 0 := rfl
lemma s1_01 : sigma1.1 0 1 = 1 := rfl
lemma s1_10 : sigma1.1 1 0 = 1 := rfl
lemma s1_11 : sigma1.1 1 1 = 0 := rfl

lemma s2_00 : sigma2.1 0 0 = 0 := rfl
lemma s2_01 : sigma2.1 0 1 = -I := rfl
lemma s2_10 : sigma2.1 1 0 = I := rfl
lemma s2_11 : sigma2.1 1 1 = 0 := rfl

lemma s3_00 : sigma3.1 0 0 = 1 := rfl
lemma s3_01 : sigma3.1 0 1 = 0 := rfl
lemma s3_10 : sigma3.1 1 0 = 0 := rfl
lemma s3_11 : sigma3.1 1 1 = -1 := rfl

lemma eval_project_0 (F : Fin 4 → Fin 4 → SL2C) (mu alpha : Fin 4) :
  project F 0 mu alpha = 0.5 * ((F mu alpha).1 0 1 + (F mu alpha).1 1 0) := by
  unfold project getPauli
  change 0.5 * Matrix.trace ((F mu alpha).1 * sigma1.1) = _
  rw[trace_2x2, mul_2x2, mul_2x2, s1_00, s1_01, s1_10, s1_11]
  ring

lemma eval_project_1 (F : Fin 4 → Fin 4 → SL2C) (mu alpha : Fin 4) :
  project F 1 mu alpha = 0.5 * I * ((F mu alpha).1 0 1 - (F mu alpha).1 1 0) := by
  unfold project getPauli
  change 0.5 * Matrix.trace ((F mu alpha).1 * sigma2.1) = _
  rw[trace_2x2, mul_2x2, mul_2x2, s2_00, s2_01, s2_10, s2_11]
  ring

lemma eval_project_2 (F : Fin 4 → Fin 4 → SL2C) (mu alpha : Fin 4) :
  project F 2 mu alpha = (F mu alpha).1 0 0 := by
  unfold project getPauli
  change 0.5 * Matrix.trace ((F mu alpha).1 * sigma3.1) = _
  rw[trace_2x2, mul_2x2, mul_2x2, s3_00, s3_01, s3_10, s3_11]
  have h := sl2c_val_1_1 (F mu alpha)
  calc 0.5 * (((F mu alpha).1 0 0 * 1 + (F mu alpha).1 0 1 * 0) + ((F mu alpha).1 1 0 * 0 + (F mu alpha).1 1 1 * -1))
    _ = 0.5 * ((F mu alpha).1 0 0 - (F mu alpha).1 1 1) := by ring
    _ = 0.5 * ((F mu alpha).1 0 0 - -(F mu alpha).1 0 0) := by rw [h]
    _ = (F mu alpha).1 0 0 := by ring

lemma triple_sum_eps (f : Fin 3 → Fin 3 → Fin 3 → Complex) :
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * f a b c) =
  f 0 1 2 - f 0 2 1 - f 1 0 2 + f 1 2 0 + f 2 0 1 - f 2 1 0 := by
  rw[sum_fin_3_expand]
  rw[sum_fin_3_expand, sum_fin_3_expand, sum_fin_3_expand]
  rw[sum_fin_3_expand, sum_fin_3_expand, sum_fin_3_expand]
  rw[sum_fin_3_expand, sum_fin_3_expand, sum_fin_3_expand]
  rw[sum_fin_3_expand, sum_fin_3_expand, sum_fin_3_expand]
  unfold epsilon3 epsilon3_int
  ring

/--
The scalar triple product of the Pauli projections of three trace-free 2x2 matrices 
is strictly proportional to the trace of their Lie bracket. If the field is single color 
(all components commute), the triple product identically vanishes.
-/
lemma single_color_triple_product_zero (F : Fin 4 → Fin 4 → SL2C) (h : isSingleColor F)
  (mu nu : Fin 4) (alpha beta gamma delta : Fin 4) :
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
    epsilon3 a b c * project F a mu alpha * project F b nu beta * project F c gamma delta = 0 := by

  let X := F mu alpha
  let Y := F nu beta

  have h_comm : ⁅X, Y⁆ = 0 := h mu alpha nu beta
  have h_comm_val : X.1 * Y.1 - Y.1 * X.1 = 0 := by
    calc X.1 * Y.1 - Y.1 * X.1 = ⁅X, Y⁆.1 := bracket_eq_sub X Y |>.symm
      _ = (0 : SL2C).1 := by rw [h_comm]
      _ = 0 := rfl

  have h00 : (X.1 * Y.1 - Y.1 * X.1) 0 0 = 0 := by rw [h_comm_val]; rfl
  have h01 : (X.1 * Y.1 - Y.1 * X.1) 0 1 = 0 := by rw [h_comm_val]; rfl
  have h10 : (X.1 * Y.1 - Y.1 * X.1) 1 0 = 0 := by rw[h_comm_val]; rfl

  have x11 := sl2c_val_1_1 X
  have y11 := sl2c_val_1_1 Y

  simp only[Matrix.sub_apply, mul_2x2, x11, y11, Matrix.zero_apply] at h00 h01 h10

  have eq1 : X.1 0 1 * Y.1 1 0 = X.1 1 0 * Y.1 0 1 := by
    apply sub_eq_zero.mp
    calc X.1 0 1 * Y.1 1 0 - X.1 1 0 * Y.1 0 1
      _ = (X.1 0 0 * Y.1 0 0 + X.1 0 1 * Y.1 1 0) - (Y.1 0 0 * X.1 0 0 + Y.1 0 1 * X.1 1 0) := by ring
      _ = 0 := h00

  have eq2 : X.1 0 0 * Y.1 0 1 = X.1 0 1 * Y.1 0 0 := by
    apply sub_eq_zero.mp
    have h_double : 2 * (X.1 0 0 * Y.1 0 1 - X.1 0 1 * Y.1 0 0) = 0 := by
      calc 2 * (X.1 0 0 * Y.1 0 1 - X.1 0 1 * Y.1 0 0)
        _ = (X.1 0 0 * Y.1 0 1 + X.1 0 1 * (-Y.1 0 0)) - (Y.1 0 0 * X.1 0 1 + Y.1 0 1 * (-X.1 0 0)) := by ring
        _ = 0 := h01
    cases mul_eq_zero.mp h_double with
    | inl h2 => norm_num at h2
    | inr h_eq => exact h_eq

  have eq3 : X.1 1 0 * Y.1 0 0 = X.1 0 0 * Y.1 1 0 := by
    apply sub_eq_zero.mp
    have h_double : 2 * (X.1 1 0 * Y.1 0 0 - X.1 0 0 * Y.1 1 0) = 0 := by
      calc 2 * (X.1 1 0 * Y.1 0 0 - X.1 0 0 * Y.1 1 0)
        _ = (X.1 1 0 * Y.1 0 0 + (-X.1 0 0) * Y.1 1 0) - (Y.1 1 0 * X.1 0 0 + (-Y.1 0 0) * X.1 1 0) := by ring
        _ = 0 := h10
    cases mul_eq_zero.mp h_double with
    | inl h2 => norm_num at h2
    | inr h_eq => exact h_eq

  have z2 : X.1 0 1 * Y.1 0 0 - X.1 0 0 * Y.1 0 1 = 0 := by
    calc X.1 0 1 * Y.1 0 0 - X.1 0 0 * Y.1 0 1
      _ = X.1 0 1 * Y.1 0 0 - X.1 0 1 * Y.1 0 0 := by rw [eq2]
      _ = 0 := by ring

  have z3 : X.1 1 0 * Y.1 0 0 - X.1 0 0 * Y.1 1 0 = 0 := by
    calc X.1 1 0 * Y.1 0 0 - X.1 0 0 * Y.1 1 0
      _ = X.1 1 0 * Y.1 0 0 - X.1 1 0 * Y.1 0 0 := by rw [eq3]
      _ = 0 := by ring

  have z1_rev : X.1 1 0 * Y.1 0 1 - X.1 0 1 * Y.1 1 0 = 0 := by
    calc X.1 1 0 * Y.1 0 1 - X.1 0 1 * Y.1 1 0
      _ = X.1 1 0 * Y.1 0 1 - X.1 1 0 * Y.1 0 1 := by rw [eq1]
      _ = 0 := by ring

  have z2_rev : X.1 0 0 * Y.1 0 1 - X.1 0 1 * Y.1 0 0 = 0 := by
    calc X.1 0 0 * Y.1 0 1 - X.1 0 1 * Y.1 0 0
      _ = X.1 0 0 * Y.1 0 1 - X.1 0 0 * Y.1 0 1 := by rw[← eq2]
      _ = 0 := by ring

  have z3_rev : X.1 0 0 * Y.1 1 0 - X.1 1 0 * Y.1 0 0 = 0 := by
    calc X.1 0 0 * Y.1 1 0 - X.1 1 0 * Y.1 0 0
      _ = X.1 0 0 * Y.1 1 0 - X.1 0 0 * Y.1 1 0 := by rw [← eq3]
      _ = 0 := by ring

  have cross1 : project F 1 mu alpha * project F 2 nu beta - project F 2 mu alpha * project F 1 nu beta = 0 := by
    rw[eval_project_1 F mu alpha, eval_project_2 F mu alpha, eval_project_1 F nu beta, eval_project_2 F nu beta]
    calc (0.5 * I * (X.1 0 1 - X.1 1 0)) * Y.1 0 0 - X.1 0 0 * (0.5 * I * (Y.1 0 1 - Y.1 1 0))
      _ = 0.5 * I * ((X.1 0 1 * Y.1 0 0 - X.1 0 0 * Y.1 0 1) - (X.1 1 0 * Y.1 0 0 - X.1 0 0 * Y.1 1 0)) := by ring
      _ = 0.5 * I * (0 - 0) := by rw [z2, z3]
      _ = 0 := by ring

  have cross2 : project F 2 mu alpha * project F 0 nu beta - project F 0 mu alpha * project F 2 nu beta = 0 := by
    rw[eval_project_2 F mu alpha, eval_project_0 F mu alpha, eval_project_2 F nu beta, eval_project_0 F nu beta]
    calc X.1 0 0 * (0.5 * (Y.1 0 1 + Y.1 1 0)) - (0.5 * (X.1 0 1 + X.1 1 0)) * Y.1 0 0
      _ = 0.5 * ((X.1 0 0 * Y.1 0 1 - X.1 0 1 * Y.1 0 0) + (X.1 0 0 * Y.1 1 0 - X.1 1 0 * Y.1 0 0)) := by ring
      _ = 0.5 * (0 + 0) := by rw[z2_rev, z3_rev]
      _ = 0 := by ring

  have cross3 : project F 0 mu alpha * project F 1 nu beta - project F 1 mu alpha * project F 0 nu beta = 0 := by
    rw[eval_project_0 F mu alpha, eval_project_1 F mu alpha, eval_project_0 F nu beta, eval_project_1 F nu beta]
    calc 0.5 * (X.1 0 1 + X.1 1 0) * (0.5 * I * (Y.1 0 1 - Y.1 1 0)) -
         (0.5 * I * (X.1 0 1 - X.1 1 0)) * (0.5 * (Y.1 0 1 + Y.1 1 0))
      _ = 0.5 * I * (X.1 1 0 * Y.1 0 1 - X.1 0 1 * Y.1 1 0) := by ring
      _ = 0.5 * I * 0 := by rw [z1_rev]
      _ = 0 := by ring

  have h_assoc : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * project F a mu alpha * project F b nu beta * project F c gamma delta) =
                 (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (project F a mu alpha * project F b nu beta * project F c gamma delta)) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    ring
  rw [h_assoc]

  have h_sum := triple_sum_eps (fun a b c => project F a mu alpha * project F b nu beta * project F c gamma delta)
  rw[h_sum]

  calc project F 0 mu alpha * project F 1 nu beta * project F 2 gamma delta -
       project F 0 mu alpha * project F 2 nu beta * project F 1 gamma delta -
       project F 1 mu alpha * project F 0 nu beta * project F 2 gamma delta +
       project F 1 mu alpha * project F 2 nu beta * project F 0 gamma delta +
       project F 2 mu alpha * project F 0 nu beta * project F 1 gamma delta -
       project F 2 mu alpha * project F 1 nu beta * project F 0 gamma delta
    _ = (project F 0 mu alpha * project F 1 nu beta - project F 1 mu alpha * project F 0 nu beta) * project F 2 gamma delta +
        (project F 1 mu alpha * project F 2 nu beta - project F 2 mu alpha * project F 1 nu beta) * project F 0 gamma delta +
        (project F 2 mu alpha * project F 0 nu beta - project F 0 mu alpha * project F 2 nu beta) * project F 1 gamma delta := by ring
    _ = 0 * project F 2 gamma delta + 0 * project F 0 gamma delta + 0 * project F 1 gamma delta := by rw[cross3, cross1, cross2]
    _ = 0 := by ring

lemma sum_swap_3_4 (f : Fin 3 → Fin 4 → Complex) :
  (∑ a : Fin 3, ∑ α : Fin 4, f a α) = ∑ α : Fin 4, ∑ a : Fin 3, f a α := Finset.sum_comm

lemma single_color_space_term_zero (F : Fin 4 -> Fin 4 -> SL2C) (h : isSingleColor F) (mu nu : Fin 4) :
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * ∑ alpha : Fin 4, ∑ beta : Fin 4, ∑ gamma : Fin 4, ∑ delta : Fin 4, epsilon4 alpha beta gamma delta * project F a mu alpha * project F b nu beta * project F c gamma delta) = 0 := by
  simp_rw [Finset.mul_sum]
  simp_rw[sum_swap_3_4]

  have h_zero : ∀ alpha beta gamma delta,
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (epsilon4 alpha beta gamma delta * project F a mu alpha * project F b nu beta * project F c gamma delta)) = 0 := by
    intros alpha beta gamma delta
    have h_inner := single_color_triple_product_zero F h mu nu alpha beta gamma delta

    calc (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (epsilon4 alpha beta gamma delta * project F a mu alpha * project F b nu beta * project F c gamma delta))
      _ = (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon4 alpha beta gamma delta * (epsilon3 a b c * project F a mu alpha * project F b nu beta * project F c gamma delta)) := by
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        apply Finset.sum_congr rfl; intro c _
        ring
      _ = epsilon4 alpha beta gamma delta * (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * project F a mu alpha * project F b nu beta * project F c gamma delta) := by
        simp_rw[← Finset.mul_sum]
      _ = epsilon4 alpha beta gamma delta * 0 := by rw[h_inner]
      _ = 0 := by ring

  apply Finset.sum_eq_zero; intro alpha _
  apply Finset.sum_eq_zero; intro beta _
  apply Finset.sum_eq_zero; intro gamma _
  apply Finset.sum_eq_zero; intro delta _
  exact h_zero alpha beta gamma delta

lemma metric_eq_zero_matrix (F : Fin 4 -> Fin 4 -> SL2C) (h : isSingleColor F) :
  urbantkeMetric F = 0 := by
  ext mu nu
  unfold urbantkeMetric
  exact single_color_space_term_zero F h mu nu

Litlib.theorem
  description "Metric Confinement of Abelian Fields"
/--
Demonstrates that the Urbantke metric determinant fundamentally requires non-commuting Lie algebra generators. For an Abelian (single-color) field, the Lie bracket vanishes, algebraically forcing the macroscopic spacetime volume to zero. Physical spacetime geometries therefore require non-Abelian fields (such as multi-color hadrons) to expand into stable configurations, geometrically manifesting color confinement.
-/
theorem kinematicSingleColorDegeneracy (_u : Universe) :
  ∀ (F : Fin 4 → Fin 4 → SL2C),
    isSingleColor F →
    (urbantkeMetric F).det = 0 := by
  intro F h_red
  have h_zero := metric_eq_zero_matrix F h_red
  rw[h_zero]
  exact Matrix.det_zero ⟨0⟩

Litlib.theorem
  description "Non-Abelian Volume Requirement"
/--
Demonstrates that a non-zero macroscopic spacetime volume strictly requires non-Abelian fields.
-/
theorem kinematicMultiColorRequirement (_u : Universe) :
  ∀ (F : Fin 4 → Fin 4 → SL2C),
    (urbantkeMetric F).det ≠ 0 →
    ¬ isSingleColor F := by
  intro F h_vol h_single
  have h_zero := kinematicSingleColorDegeneracy _u F h_single
  exact h_vol h_zero

end CGD.Particles

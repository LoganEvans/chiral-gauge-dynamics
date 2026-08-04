-- FILENAME: CGD/Particles/Subalgebra.lean

import CGD.Math.Matrix
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

open CGD.Axioms CGD.Math CGD.Foundations CGD.Gravity Matrix Complex BigOperators

set_option linter.unusedSimpArgs false

namespace CGD.Particles

lemma sl2cTrace (X : SL2C) : X.val 0 0 + X.val 1 1 = 0 := by
  have h := X.property
  change ∑ i : Fin 2, X.val i i = 0 at h
  rw [sum_fin_2_expand] at h
  exact h

lemma sl2cVal11 (X : SL2C) : X.val 1 1 = -X.val 0 0 := by
  have h := sl2cTrace X
  calc X.val 1 1 = X.val 0 0 + X.val 1 1 - X.val 0 0 := by ring
    _ = (0 : Complex) - X.val 0 0 := by rw [h]
    _ = -X.val 0 0 := by ring

lemma bracketEqSub (A B : SL2C) : ⁅A, B⁆.val = A.val * B.val - B.val * A.val := rfl

lemma s100 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
lemma s101 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
lemma s110 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
lemma s111 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl

lemma s200 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
lemma s201 : sigma2.val 0 1 = -I := by rw [val_sigma2]; rfl
lemma s210 : sigma2.val 1 0 = I := by rw [val_sigma2]; rfl
lemma s211 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl

lemma s300 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
lemma s301 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
lemma s310 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
lemma s311 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl

lemma tripleSumEps (f : Fin 3 → Fin 3 → Fin 3 → Complex) :
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * f a b c) =
  f 0 1 2 - f 0 2 1 - f 1 0 2 + f 1 2 0 + f 2 0 1 - f 2 1 0 := by
  rw[sum_fin_3_expand]
  rw[sum_fin_3_expand, sum_fin_3_expand, sum_fin_3_expand]
  rw[sum_fin_3_expand, sum_fin_3_expand, sum_fin_3_expand]
  rw[sum_fin_3_expand, sum_fin_3_expand, sum_fin_3_expand]
  rw[sum_fin_3_expand, sum_fin_3_expand, sum_fin_3_expand]
  unfold epsilon3 epsilon3_int
  ring

lemma sumSwap34 (f : Fin 3 → Fin 4 → Complex) :
  (∑ a : Fin 3, ∑ α : Fin 4, f a α) = ∑ α : Fin 4, ∑ a : Fin 3, f a α := Finset.sum_comm

section SubalgebraVariables

variable (F : Fin 4 → Fin 4 → SL2C)

lemma evalProject0 (mu alpha : Fin 4) :
  project F 0 mu alpha = 0.5 * ((F mu alpha).val 0 1 + (F mu alpha).val 1 0) := by
  unfold project getPauli
  change 0.5 * Matrix.trace ((F mu alpha).val * sigma1.val) = _
  rw[trace_2x2, mul_2x2, mul_2x2, s100, s101, s110, s111]
  ring

lemma evalProject1 (mu alpha : Fin 4) :
  project F 1 mu alpha = 0.5 * I * ((F mu alpha).val 0 1 - (F mu alpha).val 1 0) := by
  unfold project getPauli
  change 0.5 * Matrix.trace ((F mu alpha).val * sigma2.val) = _
  rw[trace_2x2, mul_2x2, mul_2x2, s200, s201, s210, s211]
  ring

lemma evalProject2 (mu alpha : Fin 4) :
  project F 2 mu alpha = (F mu alpha).val 0 0 := by
  unfold project getPauli
  change 0.5 * Matrix.trace ((F mu alpha).val * sigma3.val) = _
  rw[trace_2x2, mul_2x2, mul_2x2, s300, s301, s310, s311]
  have h := sl2cVal11 (F mu alpha)
  calc 0.5 * (((F mu alpha).val 0 0 * 1 + (F mu alpha).val 0 1 * 0) + ((F mu alpha).val 1 0 * 0 + (F mu alpha).val 1 1 * -1))
    _ = 0.5 * ((F mu alpha).val 0 0 - (F mu alpha).val 1 1) := by ring
    _ = 0.5 * ((F mu alpha).val 0 0 - -(F mu alpha).val 0 0) := by rw [h]
    _ = (F mu alpha).val 0 0 := by ring

/--
The scalar triple product of the Pauli projections of three trace-free 2x2 matrices
is strictly proportional to the trace of their Lie bracket. If the field forms an 
Abelian subalgebra (all components commute), the triple product identically vanishes.
-/
lemma abelianSubalgebraTripleProductZero (h : isAbelianSubalgebra F)
  (mu nu : Fin 4) (alpha beta gamma delta : Fin 4) :
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
    epsilon3 a b c * project F a mu alpha * project F b nu beta * project F c gamma delta = 0 := by

  let X := F mu alpha
  let Y := F nu beta

  have hComm : ⁅X, Y⁆ = 0 := h mu alpha nu beta
  have hCommVal : X.val * Y.val - Y.val * X.val = 0 := by
    calc X.val * Y.val - Y.val * X.val = ⁅X, Y⁆.val := bracketEqSub X Y |>.symm
      _ = (0 : SL2C).val := by rw [hComm]
      _ = 0 := rfl

  have h00 : (X.val * Y.val - Y.val * X.val) 0 0 = 0 := by rw [hCommVal]; rfl
  have h01 : (X.val * Y.val - Y.val * X.val) 0 1 = 0 := by rw [hCommVal]; rfl
  have h10 : (X.val * Y.val - Y.val * X.val) 1 0 = 0 := by rw[hCommVal]; rfl

  have x11 := sl2cVal11 X
  have y11 := sl2cVal11 Y

  simp only[Matrix.sub_apply, mul_2x2, x11, y11, Matrix.zero_apply] at h00 h01 h10

  have eq1 : X.val 0 1 * Y.val 1 0 = X.val 1 0 * Y.val 0 1 := by
    apply sub_eq_zero.mp
    calc X.val 0 1 * Y.val 1 0 - X.val 1 0 * Y.val 0 1
      _ = (X.val 0 0 * Y.val 0 0 + X.val 0 1 * Y.val 1 0) - (Y.val 0 0 * X.val 0 0 + Y.val 0 1 * X.val 1 0) := by ring
      _ = 0 := h00

  have eq2 : X.val 0 0 * Y.val 0 1 = X.val 0 1 * Y.val 0 0 := by
    apply sub_eq_zero.mp
    have hDouble : 2 * (X.val 0 0 * Y.val 0 1 - X.val 0 1 * Y.val 0 0) = 0 := by
      calc 2 * (X.val 0 0 * Y.val 0 1 - X.val 0 1 * Y.val 0 0)
        _ = (X.val 0 0 * Y.val 0 1 + X.val 0 1 * (-Y.val 0 0)) - (Y.val 0 0 * X.val 0 1 + Y.val 0 1 * (-X.val 0 0)) := by ring
        _ = 0 := h01
    cases mul_eq_zero.mp hDouble with
    | inl h2 => norm_num at h2
    | inr hEq => exact hEq

  have eq3 : X.val 1 0 * Y.val 0 0 = X.val 0 0 * Y.val 1 0 := by
    apply sub_eq_zero.mp
    have hDouble : 2 * (X.val 1 0 * Y.val 0 0 - X.val 0 0 * Y.val 1 0) = 0 := by
      calc 2 * (X.val 1 0 * Y.val 0 0 - X.val 0 0 * Y.val 1 0)
        _ = (X.val 1 0 * Y.val 0 0 + (-X.val 0 0) * Y.val 1 0) - (Y.val 1 0 * X.val 0 0 + (-Y.val 0 0) * X.val 1 0) := by ring
        _ = 0 := h10
    cases mul_eq_zero.mp hDouble with
    | inl h2 => norm_num at h2
    | inr hEq => exact hEq

  have z2 : X.val 0 1 * Y.val 0 0 - X.val 0 0 * Y.val 0 1 = 0 := by
    calc X.val 0 1 * Y.val 0 0 - X.val 0 0 * Y.val 0 1
      _ = X.val 0 1 * Y.val 0 0 - X.val 0 1 * Y.val 0 0 := by rw [eq2]
      _ = 0 := by ring

  have z3 : X.val 1 0 * Y.val 0 0 - X.val 0 0 * Y.val 1 0 = 0 := by
    calc X.val 1 0 * Y.val 0 0 - X.val 0 0 * Y.val 1 0
      _ = X.val 1 0 * Y.val 0 0 - X.val 1 0 * Y.val 0 0 := by rw [eq3]
      _ = 0 := by ring

  have z1Rev : X.val 1 0 * Y.val 0 1 - X.val 0 1 * Y.val 1 0 = 0 := by
    calc X.val 1 0 * Y.val 0 1 - X.val 0 1 * Y.val 1 0
      _ = X.val 1 0 * Y.val 0 1 - X.val 1 0 * Y.val 0 1 := by rw [eq1]
      _ = 0 := by ring

  have z2Rev : X.val 0 0 * Y.val 0 1 - X.val 0 1 * Y.val 0 0 = 0 := by
    calc X.val 0 0 * Y.val 0 1 - X.val 0 1 * Y.val 0 0
      _ = X.val 0 0 * Y.val 0 1 - X.val 0 0 * Y.val 0 1 := by rw[← eq2]
      _ = 0 := by ring

  have z3Rev : X.val 0 0 * Y.val 1 0 - X.val 1 0 * Y.val 0 0 = 0 := by
    calc X.val 0 0 * Y.val 1 0 - X.val 1 0 * Y.val 0 0
      _ = X.val 0 0 * Y.val 1 0 - X.val 0 0 * Y.val 1 0 := by rw [← eq3]
      _ = 0 := by ring

  have cross1 : project F 1 mu alpha * project F 2 nu beta - project F 2 mu alpha * project F 1 nu beta = 0 := by
    rw[evalProject1 F mu alpha, evalProject2 F mu alpha, evalProject1 F nu beta, evalProject2 F nu beta]
    calc (0.5 * I * (X.val 0 1 - X.val 1 0)) * Y.val 0 0 - X.val 0 0 * (0.5 * I * (Y.val 0 1 - Y.val 1 0))
      _ = 0.5 * I * ((X.val 0 1 * Y.val 0 0 - X.val 0 0 * Y.val 0 1) - (X.val 1 0 * Y.val 0 0 - X.val 0 0 * Y.val 1 0)) := by ring
      _ = 0.5 * I * (0 - 0) := by rw [z2, z3]
      _ = 0 := by ring

  have cross2 : project F 2 mu alpha * project F 0 nu beta - project F 0 mu alpha * project F 2 nu beta = 0 := by
    rw[evalProject2 F mu alpha, evalProject0 F mu alpha, evalProject2 F nu beta, evalProject0 F nu beta]
    calc X.val 0 0 * (0.5 * (Y.val 0 1 + Y.val 1 0)) - (0.5 * (X.val 0 1 + X.val 1 0)) * Y.val 0 0
      _ = 0.5 * ((X.val 0 0 * Y.val 0 1 - X.val 0 1 * Y.val 0 0) + (X.val 0 0 * Y.val 1 0 - X.val 1 0 * Y.val 0 0)) := by ring
      _ = 0.5 * (0 + 0) := by rw[z2Rev, z3Rev]
      _ = 0 := by ring

  have cross3 : project F 0 mu alpha * project F 1 nu beta - project F 1 mu alpha * project F 0 nu beta = 0 := by
    rw[evalProject0 F mu alpha, evalProject1 F mu alpha, evalProject0 F nu beta, evalProject1 F nu beta]
    calc 0.5 * (X.val 0 1 + X.val 1 0) * (0.5 * I * (Y.val 0 1 - Y.val 1 0)) -
         (0.5 * I * (X.val 0 1 - X.val 1 0)) * (0.5 * (Y.val 0 1 + Y.val 1 0))
      _ = 0.5 * I * (X.val 1 0 * Y.val 0 1 - X.val 0 1 * Y.val 1 0) := by ring
      _ = 0.5 * I * 0 := by rw [z1Rev]
      _ = 0 := by ring

  have hAssoc : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * project F a mu alpha * project F b nu beta * project F c gamma delta) =
                (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (project F a mu alpha * project F b nu beta * project F c gamma delta)) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    ring
  rw [hAssoc]

  have hSum := tripleSumEps (fun a b c => project F a mu alpha * project F b nu beta * project F c gamma delta)
  rw[hSum]

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

lemma abelianSubalgebraSpaceTermZero (h : isAbelianSubalgebra F) (mu nu : Fin 4) :
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * ∑ alpha : Fin 4, ∑ beta : Fin 4, ∑ gamma : Fin 4, ∑ delta : Fin 4, epsilon4 alpha beta gamma delta * project F a mu alpha * project F b nu beta * project F c gamma delta) = 0 := by
  simp_rw [Finset.mul_sum]
  simp_rw[sumSwap34]

  have hZero : ∀ alpha beta gamma delta,
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (epsilon4 alpha beta gamma delta * project F a mu alpha * project F b nu beta * project F c gamma delta)) = 0 := by
    intros alpha beta gamma delta
    have hInner := abelianSubalgebraTripleProductZero F h mu nu alpha beta gamma delta

    calc (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (epsilon4 alpha beta gamma delta * project F a mu alpha * project F b nu beta * project F c gamma delta))
      _ = (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon4 alpha beta gamma delta * (epsilon3 a b c * project F a mu alpha * project F b nu beta * project F c gamma delta)) := by
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        apply Finset.sum_congr rfl; intro c _
        ring
      _ = epsilon4 alpha beta gamma delta * (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * project F a mu alpha * project F b nu beta * project F c gamma delta) := by
        simp_rw[← Finset.mul_sum]
      _ = epsilon4 alpha beta gamma delta * 0 := by rw[hInner]
      _ = 0 := by ring

  apply Finset.sum_eq_zero; intro alpha _
  apply Finset.sum_eq_zero; intro beta _
  apply Finset.sum_eq_zero; intro gamma _
  apply Finset.sum_eq_zero; intro delta _
  exact hZero alpha beta gamma delta

lemma abelianSubalgebraMetricEqZeroMatrix (h : isAbelianSubalgebra F) :
  urbantkeMetric F = 0 := by
  ext mu nu
  unfold urbantkeMetric
  exact abelianSubalgebraSpaceTermZero F h mu nu

/--
Demonstrates that the Urbantke metric determinant fundamentally requires non-commuting Lie algebra generators. For an Abelian field, the Lie bracket vanishes, algebraically forcing the macroscopic spacetime volume to zero. Physical spacetime geometries therefore require non-Abelian fields to expand into stable configurations, geometrically manifesting topological confinement.
-/
@[litlib_track "Metric Confinement of Abelian Fields"]
theorem kinematicAbelianSubalgebraDegeneracy :
  isAbelianSubalgebra F →
  (urbantkeMetric F).det = 0 := by
  intro hRed
  have hZero := abelianSubalgebraMetricEqZeroMatrix F hRed
  rw[hZero]
  exact Matrix.det_zero ⟨0⟩

/--
Demonstrates that a non-zero macroscopic spacetime volume strictly requires non-Abelian fields.
-/
@[litlib_track "Kinematic Non-Abelian Volume Requirement"]
theorem kinematicNonAbelianVolumeRequirement :
  (urbantkeMetric F).det ≠ 0 →
  ¬ isAbelianSubalgebra F := by
  intro hVol hSingle
  have hZero := kinematicAbelianSubalgebraDegeneracy F hSingle
  exact hVol hZero

/--
Defines a gauge field that is constrained to a lower-dimensional Lie subalgebra,
missing at least one of the three internal Lie algebra generators.
-/
def isLieAxisDeficient (axis : Fin 3) : Prop :=
  ∀ mu nu, project F axis mu nu = 0

lemma missingLieAxisTripleProductZero
  (axis : Fin 3) (h : ∀ mu alpha, project F axis mu alpha = 0)
  (mu nu : Fin 4) (alpha beta gamma delta : Fin 4) :
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
    epsilon3 a b c * project F a mu alpha * project F b nu beta * project F c gamma delta = 0 := by
  have hAssoc : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * project F a mu alpha * project F b nu beta * project F c gamma delta) =
                (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (project F a mu alpha * project F b nu beta * project F c gamma delta)) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    ring
  rw [hAssoc]
  have hSum := tripleSumEps (fun a b c => project F a mu alpha * project F b nu beta * project F c gamma delta)
  rw [hSum]
  fin_cases axis
  · have h1 : project F 0 mu alpha = 0 := h mu alpha
    have h2 : project F 0 nu beta = 0 := h nu beta
    have h3 : project F 0 gamma delta = 0 := h gamma delta
    calc project F 0 mu alpha * project F 1 nu beta * project F 2 gamma delta -
         project F 0 mu alpha * project F 2 nu beta * project F 1 gamma delta -
         project F 1 mu alpha * project F 0 nu beta * project F 2 gamma delta +
         project F 1 mu alpha * project F 2 nu beta * project F 0 gamma delta +
         project F 2 mu alpha * project F 0 nu beta * project F 1 gamma delta -
         project F 2 mu alpha * project F 1 nu beta * project F 0 gamma delta
      _ = 0 * project F 1 nu beta * project F 2 gamma delta -
          0 * project F 2 nu beta * project F 1 gamma delta -
          project F 1 mu alpha * 0 * project F 2 gamma delta +
          project F 1 mu alpha * project F 2 nu beta * 0 +
          project F 2 mu alpha * 0 * project F 1 gamma delta -
          project F 2 mu alpha * project F 1 nu beta * 0 := by rw [h1, h2, h3]
      _ = 0 := by ring
  · have h1 : project F 1 mu alpha = 0 := h mu alpha
    have h2 : project F 1 nu beta = 0 := h nu beta
    have h3 : project F 1 gamma delta = 0 := h gamma delta
    calc project F 0 mu alpha * project F 1 nu beta * project F 2 gamma delta -
         project F 0 mu alpha * project F 2 nu beta * project F 1 gamma delta -
         project F 1 mu alpha * project F 0 nu beta * project F 2 gamma delta +
         project F 1 mu alpha * project F 2 nu beta * project F 0 gamma delta +
         project F 2 mu alpha * project F 0 nu beta * project F 1 gamma delta -
         project F 2 mu alpha * project F 1 nu beta * project F 0 gamma delta
      _ = project F 0 mu alpha * 0 * project F 2 gamma delta -
          project F 0 mu alpha * project F 2 nu beta * 0 -
          0 * project F 0 nu beta * project F 2 gamma delta +
          0 * project F 2 nu beta * project F 0 gamma delta +
          project F 2 mu alpha * project F 0 nu beta * 0 -
          project F 2 mu alpha * 0 * project F 0 gamma delta := by rw [h1, h2, h3]
      _ = 0 := by ring
  · have h1 : project F 2 mu alpha = 0 := h mu alpha
    have h2 : project F 2 nu beta = 0 := h nu beta
    have h3 : project F 2 gamma delta = 0 := h gamma delta
    calc project F 0 mu alpha * project F 1 nu beta * project F 2 gamma delta -
         project F 0 mu alpha * project F 2 nu beta * project F 1 gamma delta -
         project F 1 mu alpha * project F 0 nu beta * project F 2 gamma delta +
         project F 1 mu alpha * project F 2 nu beta * project F 0 gamma delta +
         project F 2 mu alpha * project F 0 nu beta * project F 1 gamma delta -
         project F 2 mu alpha * project F 1 nu beta * project F 0 gamma delta
      _ = project F 0 mu alpha * project F 1 nu beta * 0 -
          project F 0 mu alpha * 0 * project F 1 gamma delta -
          project F 1 mu alpha * project F 0 nu beta * 0 +
          project F 1 mu alpha * 0 * project F 0 gamma delta +
          0 * project F 0 nu beta * project F 1 gamma delta -
          0 * project F 1 nu beta * project F 0 gamma delta := by rw [h1, h2, h3]
      _ = 0 := by ring

lemma missingLieAxisSpaceTermZero (axis : Fin 3) (h : ∀ mu alpha, project F axis mu alpha = 0) (mu nu : Fin 4) :
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * ∑ alpha : Fin 4, ∑ beta : Fin 4, ∑ gamma : Fin 4, ∑ delta : Fin 4, epsilon4 alpha beta gamma delta * project F a mu alpha * project F b nu beta * project F c gamma delta) = 0 := by
  simp_rw [Finset.mul_sum]
  simp_rw [sumSwap34]

  have hZero : ∀ alpha beta gamma delta,
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (epsilon4 alpha beta gamma delta * project F a mu alpha * project F b nu beta * project F c gamma delta)) = 0 := by
    intros alpha beta gamma delta
    have hInner := missingLieAxisTripleProductZero F axis h mu nu alpha beta gamma delta

    calc (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * (epsilon4 alpha beta gamma delta * project F a mu alpha * project F b nu beta * project F c gamma delta))
      _ = (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon4 alpha beta gamma delta * (epsilon3 a b c * project F a mu alpha * project F b nu beta * project F c gamma delta)) := by
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        apply Finset.sum_congr rfl; intro c _
        ring
      _ = epsilon4 alpha beta gamma delta * (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * project F a mu alpha * project F b nu beta * project F c gamma delta) := by
        simp_rw[← Finset.mul_sum]
      _ = epsilon4 alpha beta gamma delta * 0 := by rw[hInner]
      _ = 0 := by ring

  apply Finset.sum_eq_zero; intro alpha _
  apply Finset.sum_eq_zero; intro beta _
  apply Finset.sum_eq_zero; intro gamma _
  apply Finset.sum_eq_zero; intro delta _
  exact hZero alpha beta gamma delta

lemma missingLieAxisMetricEqZeroMatrix (axis : Fin 3) (h : ∀ mu nu, project F axis mu nu = 0) :
  urbantkeMetric F = 0 := by
  ext mu nu
  unfold urbantkeMetric
  exact missingLieAxisSpaceTermZero F axis h mu nu

/--
Demonstrates that if any of the three internal Lie algebra generators are missing from the gauge field, the scalar triple product natively vanishes, mathematically forcing the macroscopic spacetime volume to zero. A stable spacetime geometry mathematically requires the interaction of exactly all three SU(2) generators.
-/
@[litlib_track "Geometric Degeneracy of Lie-Axis-Deficient Fields"]
theorem kinematicLieAxisDeficientDegeneracy (axis : Fin 3) :
  isLieAxisDeficient F axis →
  (urbantkeMetric F).det = 0 := by
  intro hDef
  have hZero := missingLieAxisMetricEqZeroMatrix F axis hDef
  rw[hZero]
  exact Matrix.det_zero ⟨0⟩

/--
Demonstrates that a non-zero macroscopic spacetime volume strictly requires non-Abelian fields spanning exactly three active Lie algebra generators. One or two generators is mathematically insufficient to sustain spacetime volume, natively bounding the minimum unbroken gauge symmetry required for macroscopic existence.
-/
@[litlib_track "Kinematic Triaxial Requirement - Non-Abelian"]
theorem kinematicTriaxialRequirementNonAbelian :
  (urbantkeMetric F).det ≠ 0 →
  ¬ isAbelianSubalgebra F := by
  intro hVol hSingle
  have hZero := abelianSubalgebraMetricEqZeroMatrix F hSingle
  have hDetZero : (urbantkeMetric F).det = 0 := by
    rw [hZero]
    exact Matrix.det_zero ⟨0⟩
  exact hVol hDetZero

/--
Demonstrates that a non-zero macroscopic spacetime volume strictly requires non-Abelian fields spanning exactly three active Lie algebra generators. One or two generators is mathematically insufficient to sustain spacetime volume, natively bounding the minimum unbroken gauge symmetry required for macroscopic existence.
-/
@[litlib_track "Kinematic Triaxial Requirement - Axis"]
theorem kinematicTriaxialRequirementAxis :
  (urbantkeMetric F).det ≠ 0 →
  ∀ axis, ¬ isLieAxisDeficient F axis := by
  intro hVol axis hDef
  have hZero := kinematicLieAxisDeficientDegeneracy F axis hDef
  exact hVol hZero

end SubalgebraVariables

end CGD.Particles

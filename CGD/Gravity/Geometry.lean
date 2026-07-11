-- FILENAME: CGD/Gravity/Geometry.lean

import CGD.Foundations.Spacetime
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Litlib.Math.Matrix4

open Complex Matrix BigOperators
open CGD.Foundations

namespace CGD.Gravity

/-- 4-dimensional Levi-Civita tensor over Int for O(1) kernel evaluation -/
def epsilon4_int : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Int
| 0, 1, 2, 3 => 1
| 0, 2, 3, 1 => 1
| 0, 3, 1, 2 => 1
| 1, 0, 3, 2 => 1
| 1, 2, 0, 3 => 1
| 1, 3, 2, 0 => 1
| 2, 0, 1, 3 => 1
| 2, 1, 3, 0 => 1
| 2, 3, 0, 1 => 1
| 3, 0, 2, 1 => 1
| 3, 1, 0, 2 => 1
| 3, 2, 1, 0 => 1
| 0, 1, 3, 2 => -1
| 0, 2, 1, 3 => -1
| 0, 3, 2, 1 => -1
| 1, 0, 2, 3 => -1
| 1, 2, 3, 0 => -1
| 1, 3, 0, 2 => -1
| 2, 0, 3, 1 => -1
| 2, 1, 0, 3 => -1
| 2, 3, 1, 0 => -1
| 3, 0, 1, 2 => -1
| 3, 1, 2, 0 => -1
| 3, 2, 0, 1 => -1
| _, _, _, _ => 0

lemma epsilon4_int_alt (α β γ δ : Fin 4) :
  epsilon4_int α β γ δ = -epsilon4_int β α γ δ ∧
  epsilon4_int α β γ δ = -epsilon4_int α γ β δ ∧
  epsilon4_int α β γ δ = -epsilon4_int α β δ γ := by
  -- `decide` evaluates the 256 boolean int equations instantly via the kernel
  fin_cases α <;> fin_cases β <;> fin_cases γ <;> fin_cases δ <;> decide

/-- 4-dimensional Levi-Civita tensor cast to Complex -/
noncomputable def epsilon4 (i j k l : Fin 4) : Complex := epsilon4_int i j k l

lemma epsilon4_0123 : epsilon4 0 1 2 3 = 1 := by
  unfold epsilon4 epsilon4_int
  norm_num

lemma epsilon4_alt (α β γ δ : Fin 4) :
  epsilon4 α β γ δ = -epsilon4 β α γ δ ∧
  epsilon4 α β γ δ = -epsilon4 α γ β δ ∧
  epsilon4 α β γ δ = -epsilon4 α β δ γ := by
  have h := epsilon4_int_alt α β γ δ
  rcases h with ⟨h1, h2, h3⟩
  unfold epsilon4
  -- Push the integer equalities safely into the Complex domain
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

noncomputable def lorentzGenerators : Fin 6 → Matrix (Fin 4) (Fin 4) Complex
| 0 => Matrix.of ![![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
| 1 => Matrix.of ![![0, 0, 1, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]]
| 2 => Matrix.of ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0]]
| 3 => Matrix.of ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, 1, 0]]
| 4 => Matrix.of ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, -1, 0, 0]]
| 5 => Matrix.of ![![0, 0, 0, 0], ![0, 0, -1, 0], ![0, 1, 0, 0], ![0, 0, 0, 0]]

def isLorentzian (g : Matrix (Fin 4) (Fin 4) Complex) : Prop :=
  (∀ i j, (g i j).im = 0) ∧ (g.det.re < 0) ∧ (g.det.im = 0)

abbrev SpacetimeIndex := Fin 4
abbrev InternalIndex := Fin 4
abbrev TetradField := InternalIndex → SpacetimeIndex → SpacetimePoint → ℂ
abbrev SpinConnection := InternalIndex → InternalIndex → SpacetimeIndex → SpacetimePoint → ℂ

noncomputable def torsionTensor (e : TetradField) (ω : SpinConnection) (I : InternalIndex) (μ ν : SpacetimeIndex) (x : SpacetimePoint) : ℂ :=
  partialDeriv μ (e I ν) x - partialDeriv ν (e I μ) x +
  ∑ J : InternalIndex, (ω I J μ x * e J ν x - ω I J ν x * e J μ x)

def isTorsionFree (e : TetradField) (ω : SpinConnection) : Prop :=
  ∀ I μ ν x, torsionTensor e ω I μ ν x = 0

noncomputable def getPauli (a : Fin 3) : SL2C :=
  match a with
  | 0 => sigma1
  | 1 => sigma2
  | 2 => sigma3

noncomputable def project (F : Fin 4 -> Fin 4 -> SL2C) (a : Fin 3) (mu nu : Fin 4) : Complex :=
  let generator := getPauli a
  let F_matrix := F mu nu
  0.5 * (F_matrix.val * generator.val).trace

/-- 3-dimensional Levi-Civita tensor over Int for O(1) kernel evaluation -/
def epsilon3_int : Fin 3 → Fin 3 → Fin 3 → Int
| 0, 1, 2 => 1
| 1, 2, 0 => 1
| 2, 0, 1 => 1
| 0, 2, 1 => -1
| 1, 0, 2 => -1
| 2, 1, 0 => -1
| _, _, _ => 0

/-- 3-dimensional Levi-Civita tensor cast to Complex. -/
def epsilon3 (a b c : Fin 3) : Complex := epsilon3_int a b c

noncomputable def urbantkeMetric (F : Fin 4 -> Fin 4 -> SL2C) : Matrix (Fin 4) (Fin 4) Complex :=
  fun mu nu =>
    ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      let eps_iso := epsilon3 a b c
      let space_term := ∑ alpha : Fin 4, ∑ beta : Fin 4, ∑ gamma : Fin 4, ∑ delta : Fin 4,
          let eps_space := epsilon4 alpha beta gamma delta
          let F1 := project F a mu alpha
          let F2 := project F b nu beta
          let F3 := project F c gamma delta
          eps_space * F1 * F2 * F3
      eps_iso * space_term

noncomputable def matrixInv4x4 (M : Matrix (Fin 4) (Fin 4) Complex) : Matrix (Fin 4) (Fin 4) Complex :=
  (1 / M.det) • M.adjugate

lemma matrixInv4x4_right_inv (M : Matrix (Fin 4) (Fin 4) Complex) (h_det : M.det ≠ 0) :
  M * matrixInv4x4 M = 1 := by
  unfold matrixInv4x4
  rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
  have h_mul : (1 / M.det) * M.det = 1 := div_mul_cancel₀ 1 h_det
  rw [h_mul, one_smul]

lemma matrixInv4x4_left_inv (M : Matrix (Fin 4) (Fin 4) Complex) (h_det : M.det ≠ 0) :
  matrixInv4x4 M * M = 1 := by
  unfold matrixInv4x4
  rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
  have h_mul : (1 / M.det) * M.det = 1 := div_mul_cancel₀ 1 h_det
  rw [h_mul, one_smul]

noncomputable def christoffel (g : SpacetimeIndex → SpacetimeIndex → SpacetimePoint → Complex) (rho mu nu : SpacetimeIndex) (x : SpacetimePoint) : Complex :=
  let g_inv := matrixInv4x4 (fun i j => g i j x)
  (1 / 2 : Complex) * ∑ sigma, g_inv rho sigma * (partialDeriv mu (fun p => g sigma nu p) x + partialDeriv nu (fun p => g mu sigma p) x - partialDeriv sigma (fun p => g mu nu p) x)

noncomputable def ricciTensor (g : SpacetimeIndex → SpacetimeIndex → SpacetimePoint → Complex) (mu nu : SpacetimeIndex) (x : SpacetimePoint) : Complex :=
  ∑ rho, (partialDeriv rho (fun p => christoffel g rho mu nu p) x
        - partialDeriv nu (fun p => christoffel g rho mu rho p) x
        + ∑ lambda, (christoffel g rho lambda rho x * christoffel g lambda mu nu x
                   - christoffel g rho lambda nu x * christoffel g lambda mu rho x))

end CGD.Gravity

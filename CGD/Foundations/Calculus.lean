-- FILENAME: CGD/Foundations/Calculus.lean

import CGD.Math.Calculus
import CGD.Foundations.Spacetime
import CGD.Foundations.GaugeGroup
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Pi

set_option linter.unusedSimpArgs false

namespace CGD.Foundations

open CGD.Math Complex Matrix

noncomputable def partialDerivMat (μ : Fin 4) (f : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => partialDeriv μ (fun p => f p i j) x

noncomputable def partialDerivSl2c (μ : Fin 4) (A : SpacetimePoint → SL2C) (x : SpacetimePoint) : SL2C :=
  let dA_val := partialDerivMat μ (fun p => (A p).val) x
  toSl2c dA_val

lemma partialDerivMat_const (c : Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) (x : SpacetimePoint) :
  partialDerivMat μ (fun _ => c) x = 0 := by
  ext i j
  unfold partialDerivMat
  exact partialDeriv_const (c i j) μ x

lemma partialDerivSl2c_const (c : SL2C) (μ : Fin 4) (x : SpacetimePoint) :
  partialDerivSl2c μ (fun _ => c) x = 0 := by
  unfold partialDerivSl2c
  have h_val : partialDerivMat μ (fun _ => c.val) x = 0 := partialDerivMat_const c.val μ x
  rw [h_val]
  apply Subtype.ext
  unfold toSl2c
  dsimp
  have ht : Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by simp[Matrix.trace]
  rw [ht]
  have hz : (0:ℂ) / 2 = 0 := by ring
  rw [hz, zero_smul, sub_zero]

noncomputable def partialDerivChiral (μ : Fin 4) (f : SpacetimePoint → ChiralM) (x : SpacetimePoint) : ChiralM :=
  let L_A := fun p => toSl2c (fun i j => f p (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)))
  let R_A := fun p => toSl2c (fun i j => f p (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)))
  embedSelfDual (partialDerivSl2c μ L_A x) + embedAntiSelfDual (partialDerivSl2c μ R_A x)

@[simp]
lemma partialDerivChiral_proj_self_dual (μ : Fin 4) (f : SpacetimePoint → ChiralM) (x : SpacetimePoint) :
  (chiralProject (partialDerivChiral μ f x)).self_dual = partialDerivSl2c μ (fun p => (chiralProject (f p)).self_dual) x := by
  unfold partialDerivChiral
  rw [chiralProject_embed_sd]
  rfl

@[simp]
lemma partialDerivChiral_proj_anti_self_dual (μ : Fin 4) (f : SpacetimePoint → ChiralM) (x : SpacetimePoint) :
  (chiralProject (partialDerivChiral μ f x)).anti_self_dual = partialDerivSl2c μ (fun p => (chiralProject (f p)).anti_self_dual) x := by
  unfold partialDerivChiral
  rw [chiralProject_embed_asd]
  rfl

noncomputable def bracket (A B : ChiralM) : ChiralM := A * B - B * A

noncomputable def curvature (A : Fin 4 → SpacetimePoint → ChiralM) (mu nu : Fin 4) (x : SpacetimePoint) : ChiralM :=
  let dA_nu := partialDerivChiral mu (fun p => A nu p) x
  let dA_mu := partialDerivChiral nu (fun p => A mu p) x
  let raw_comm := bracket (A mu x) (A nu x)
  let proj_comm := embedSelfDual (chiralProject raw_comm).self_dual + embedAntiSelfDual (chiralProject raw_comm).anti_self_dual
  dA_nu - dA_mu + proj_comm

attribute [irreducible] curvature

noncomputable def curvatureSl2c (A : Fin 4 → SpacetimePoint → SL2C) (mu nu : Fin 4) (x : SpacetimePoint) : SL2C :=
  let dA_nu := partialDerivSl2c mu (A nu) x
  let dA_mu := partialDerivSl2c nu (A mu) x
  let comm  := ⁅A mu x, A nu x⁆
  dA_nu - dA_mu + comm

lemma curvatureSl2c_def (A : Fin 4 → SpacetimePoint → SL2C) (mu nu : Fin 4) (x : SpacetimePoint) :
  curvatureSl2c A mu nu x = partialDerivSl2c mu (A nu) x - partialDerivSl2c nu (A mu) x + ⁅A mu x, A nu x⁆ := rfl

/--
The curvature tensor strictly satisfies exact antisymmetry, emerging natively from the
commutativity of partial derivatives and the anti-commutativity of the Lie algebra bracket.
-/
lemma curvatureSl2c_antisymm (A : Fin 4 → SpacetimePoint → SL2C) (mu nu : Fin 4) (x : SpacetimePoint) :
  curvatureSl2c A mu nu x = - curvatureSl2c A nu mu x := by
  rw [curvatureSl2c_def, curvatureSl2c_def]
  have h_comm : ⁅A mu x, A nu x⁆ = - ⁅A nu x, A mu x⁆ := (lie_skew (A mu x) (A nu x)).symm
  rw [h_comm]
  abel

lemma partialDerivSl2c_eq_mat (A : SpacetimePoint → SL2C) (μ : Fin 4) (x : SpacetimePoint)
  (hA : ∀ i j, DifferentiableAt ℝ (fun p => (A p).val i j) x) :
  (partialDerivSl2c μ A x).val = partialDerivMat μ (fun p => (A p).val) x := by
  unfold partialDerivSl2c toSl2c
  dsimp
  have h_tr_zero : (fun p => Matrix.trace ((A p).val)) = fun p => 0 := by
    ext p
    exact (A p).property
  have h_pd_zero : partialDeriv μ (fun (p : SpacetimePoint) => (0 : ℂ)) x = 0 := partialDeriv_const 0 μ x
  have h_tr_eval : partialDeriv μ (fun p => Matrix.trace ((A p).val)) x = 0 := by
    rw [h_tr_zero, h_pd_zero]
  have h_tr_mat : Matrix.trace (partialDerivMat μ (fun p => (A p).val) x) = 0 := by
    have h_sum : Matrix.trace (partialDerivMat μ (fun p => (A p).val) x) = partialDeriv μ (fun p => ∑ i : Fin 2, (A p).val i i) x := by
      unfold Matrix.trace partialDerivMat
      exact (partialDeriv_sum (fun i p => (A p).val i i) μ x (fun i => hA i i)).symm
    rw [h_sum]
    exact h_tr_eval
  rw [h_tr_mat]
  have hz : (0 : ℂ) / 2 = 0 := by ring
  rw [hz, zero_smul, sub_zero]

lemma curvatureSl2c_val_eq (A : Fin 4 → SpacetimePoint → SL2C) (μ ν : Fin 4) (x : SpacetimePoint)
  (hAμ : ∀ i j, DifferentiableAt ℝ (fun p => (A μ p).val i j) x)
  (hAν : ∀ i j, DifferentiableAt ℝ (fun p => (A ν p).val i j) x) :
  ∀ i j, (curvatureSl2c A μ ν x).val i j =
    partialDeriv μ (fun p => (A ν p).val i j) x -
    partialDeriv ν (fun p => (A μ p).val i j) x +
    ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) i j := by
  intro i j
  have h_curv : (curvatureSl2c A μ ν x).val = (partialDerivSl2c μ (A ν) x).val - (partialDerivSl2c ν (A μ) x).val + ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) := rfl
  have h1 : (partialDerivSl2c μ (A ν) x).val = partialDerivMat μ (fun p => (A ν p).val) x := partialDerivSl2c_eq_mat (A ν) μ x hAν
  have h2 : (partialDerivSl2c ν (A μ) x).val = partialDerivMat ν (fun p => (A μ p).val) x := partialDerivSl2c_eq_mat (A μ) ν x hAμ
  have h_eval1 : (partialDerivMat μ (fun p => (A ν p).val) x) i j = partialDeriv μ (fun p => (A ν p).val i j) x := rfl
  have h_eval2 : (partialDerivMat ν (fun p => (A μ p).val) x) i j = partialDeriv ν (fun p => (A μ p).val i j) x := rfl
  change (partialDerivSl2c μ (A ν) x).val i j - (partialDerivSl2c ν (A μ) x).val i j + ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) i j = _
  rw [h1, h2, h_eval1, h_eval2]

attribute [irreducible] curvatureSl2c

end CGD.Foundations

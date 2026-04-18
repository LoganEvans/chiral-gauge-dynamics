-- FILENAME: CGD/Foundations/Calculus.lean

import CGD.Axioms.Spacetime
import CGD.Foundations.GaugeGroup
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic

namespace CGD.Foundations

open CGD.Axioms

structure PhysicalField (E : Type*)[NormedAddCommGroup E][NormedSpace ℝ E] where
  val : SpacetimePoint → E
  smooth : ContDiff ℝ ⊤ val

instance {E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E] : CoeFun (PhysicalField E) (fun _ => SpacetimePoint → E) where
  coe := PhysicalField.val

noncomputable def partialDeriv {E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E] (μ : Fin 4) (f : SpacetimePoint → E) : SpacetimePoint → E :=
  fun x => fderiv ℝ f x ((Pi.single μ (1 : ℝ)) : Fin 4 → ℝ)

noncomputable def partialDerivMat (μ : Fin 4) (f : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => partialDeriv μ (fun p => f p i j) x

noncomputable def partialDerivSl2c (μ : Fin 4) (A : SpacetimePoint → SL2C) (x : SpacetimePoint) : SL2C :=
  let dA_val := partialDerivMat μ (fun p => (A p).val) x
  toSl2c dA_val

lemma partialDeriv_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) (μ : Fin 4) (x : SpacetimePoint) :
  partialDeriv μ (fun _ => c) x = 0 := by
  unfold partialDeriv
  have h_const : (fun (_ : SpacetimePoint) => c) = Function.const SpacetimePoint c := rfl
  rw [h_const]
  rw [fderiv_const]
  rfl

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

-- Differentiability explicitly required. 
-- Fully verified using the exact mathematical Fréchet Derivative chain rule.
lemma partialDeriv_comp_coord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : ℝ → E) (c_idx μ : Fin 4) (h_neq : μ ≠ c_idx) (x : SpacetimePoint) 
  (hf : Differentiable ℝ f) :
  partialDeriv μ (fun p => f (p c_idx)) x = 0 := by
  unfold partialDeriv
  let proj : (Fin 4 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj c_idx
  have h_eq : (fun (p : SpacetimePoint) => f (p c_idx)) = f ∘ proj := rfl
  rw [h_eq]
  have hd_f : DifferentiableAt ℝ f (proj x) := hf (proj x)
  have hd_proj : DifferentiableAt ℝ proj x := (ContinuousLinearMap.hasFDerivAt proj).differentiableAt
  rw [fderiv_comp x hd_f hd_proj]
  have h_fderiv_proj : fderiv ℝ proj x = proj := HasFDerivAt.fderiv (ContinuousLinearMap.hasFDerivAt proj)
  rw [h_fderiv_proj]
  rw [ContinuousLinearMap.comp_apply]
  have h_apply : proj ((Pi.single μ (1 : ℝ)) : Fin 4 → ℝ) = 0 := by
    have hc : proj ((Pi.single μ (1 : ℝ)) : Fin 4 → ℝ) = ((Pi.single μ (1 : ℝ)) : Fin 4 → ℝ) c_idx := rfl
    rw [hc]
    simp [h_neq.symm]
  rw [h_apply]
  exact ContinuousLinearMap.map_zero _

lemma math_partialDerivMat_comp_coord (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (c_idx μ : Fin 4) (h_neq : μ ≠ c_idx) (x : SpacetimePoint) 
  (hf : ∀ i j, Differentiable ℝ (fun z => f z i j)) :
  partialDerivMat μ (fun p => f (p c_idx)) x = 0 := by
  ext i j
  unfold partialDerivMat
  exact partialDeriv_comp_coord (fun z => f z i j) c_idx μ h_neq x (hf i j)

noncomputable def partialDerivChiral (μ : Fin 4) (f : SpacetimePoint → ChiralM) (x : SpacetimePoint) : ChiralM :=
  let L_A := fun p => toSl2c (fun i j => f p (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)))
  let R_A := fun p => toSl2c (fun i j => f p (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)))
  embedLight (partialDerivSl2c μ L_A x) + embedDark (partialDerivSl2c μ R_A x)

noncomputable def bracket (A B : ChiralM) : ChiralM := A * B - B * A

noncomputable def curvature (A : Fin 4 → SpacetimePoint → ChiralM) (mu nu : Fin 4) (x : SpacetimePoint) : ChiralM :=
  let dA_nu := partialDerivChiral mu (fun p => A nu p) x
  let dA_mu := partialDerivChiral nu (fun p => A mu p) x
  let raw_comm := bracket (A mu x) (A nu x)
  let proj_comm := embedLight (chiralProject raw_comm).light + embedDark (chiralProject raw_comm).dark
  dA_nu - dA_mu + proj_comm

lemma curvature_def (A : Fin 4 → SpacetimePoint → ChiralM) (mu nu : Fin 4) (x : SpacetimePoint) :
  curvature A mu nu x = partialDerivChiral mu (fun p => A nu p) x - partialDerivChiral nu (fun p => A mu p) x + 
  (embedLight (chiralProject (bracket (A mu x) (A nu x))).light + embedDark (chiralProject (bracket (A mu x) (A nu x))).dark) := rfl

attribute [irreducible] curvature

noncomputable def curvatureSl2c (A : Fin 4 → SpacetimePoint → SL2C) (mu nu : Fin 4) (x : SpacetimePoint) : SL2C :=
  let dA_nu := partialDerivSl2c mu (A nu) x
  let dA_mu := partialDerivSl2c nu (A mu) x
  let comm  := ⁅A mu x, A nu x⁆
  dA_nu - dA_mu + comm

lemma curvatureSl2c_def (A : Fin 4 → SpacetimePoint → SL2C) (mu nu : Fin 4) (x : SpacetimePoint) :
  curvatureSl2c A mu nu x = partialDerivSl2c mu (A nu) x - partialDerivSl2c nu (A mu) x + ⁅A mu x, A nu x⁆ := rfl

/-- 
🟢 PROVEN: The curvature tensor mathematically satisfies exact antisymmetry.
We do not lazily assume antisymmetry; it strictly emerges from the commutative subtraction 
of partial derivatives and the native anti-commutativity of the Lie Algebra bracket.
-/
lemma curvatureSl2c_antisymm (A : Fin 4 → SpacetimePoint → SL2C) (mu nu : Fin 4) (x : SpacetimePoint) :
  curvatureSl2c A mu nu x = - curvatureSl2c A nu mu x := by
  rw [curvatureSl2c_def, curvatureSl2c_def]
  have h_comm : ⁅A mu x, A nu x⁆ = - ⁅A nu x, A mu x⁆ := (lie_skew (A mu x) (A nu x)).symm
  rw [h_comm]
  abel

attribute [irreducible] curvatureSl2c

end CGD.Foundations

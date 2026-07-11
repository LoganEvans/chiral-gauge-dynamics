-- FILENAME: CGD/Math/Calculus.lean

import Litlib.Core
import CGD.Foundations.Spacetime
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Pi
import Litlib.Y1976.rudin1976principles.Chapter09.Sec08_DerivativesOfHigherOrder

set_option linter.unusedSimpArgs false

open Complex CGD.Foundations

namespace CGD.Math

noncomputable def partialDeriv {E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E] (μ : Fin 4) (f : SpacetimePoint → E) : SpacetimePoint → E :=
  fun x => fderiv ℝ f x ((Pi.single μ (1 : ℝ)) : Fin 4 → ℝ)

lemma partialDeriv_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) (μ : Fin 4) (x : SpacetimePoint) :
  partialDeriv μ (fun _ => c) x = 0 := by
  unfold partialDeriv
  have h_const : (fun (_ : SpacetimePoint) => c) = Function.const SpacetimePoint c := rfl
  rw [h_const]
  rw [fderiv_const]
  rfl

lemma partialDeriv_mul_c
  (f g : SpacetimePoint → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
  partialDeriv μ (fun p => f p * g p) x = f x * partialDeriv μ g x + partialDeriv μ f x * g x := by
  unfold partialDeriv
  have h_eq : (fun p => f p * g p) = f * g := rfl
  rw [h_eq]
  rw [fderiv_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma partialDeriv_const_smul
  (c : ℂ) (f : SpacetimePoint → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) :
  partialDeriv μ (fun p => c * f p) x = c * partialDeriv μ f x := by
  have hc : DifferentiableAt ℝ (fun _ : SpacetimePoint => c) x := differentiableAt_const c
  rw [partialDeriv_mul_c (fun _ => c) f μ x hc hf]
  rw [partialDeriv_const]
  ring

lemma diff_sum {ι : Type*} [Fintype ι] (f : ι → SpacetimePoint → ℂ) (x : SpacetimePoint) (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
  DifferentiableAt ℝ (fun p => ∑ i, f i p) x := by
  have h_eq : (fun p => ∑ i, f i p) = ∑ i, f i := by
    ext p
    rw [Finset.sum_apply]
  rw [h_eq]
  have hf' : ∀ i ∈ Finset.univ, DifferentiableAt ℝ (f i) x := fun i _ => hf i
  exact DifferentiableAt.sum hf'

lemma diff_const_mul (c : ℂ) (f : SpacetimePoint → ℂ) (x : SpacetimePoint) (hf : DifferentiableAt ℝ f x) :
  DifferentiableAt ℝ (fun p => c * f p) x := by
  have hc : DifferentiableAt ℝ (fun _ : SpacetimePoint => c) x := differentiableAt_const c
  have h_eq : (fun p => c * f p) = (fun _ => c) * f := by
    ext p
    rfl
  rw [h_eq]
  exact DifferentiableAt.mul hc hf

lemma partialDeriv_sum {ι : Type*} [Fintype ι]
  (f : ι → SpacetimePoint → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
  partialDeriv μ (fun p => ∑ i, f i p) x = ∑ i, partialDeriv μ (f i) x := by
  unfold partialDeriv
  have h_eq : (fun p => ∑ i, f i p) = ∑ i, f i := by
    ext p
    rw [Finset.sum_apply]
  rw [h_eq]
  have hf' : ∀ i ∈ Finset.univ, DifferentiableAt ℝ (f i) x := fun i _ => hf i
  rw [fderiv_sum hf']
  simp

lemma sum_neg_extract (n : Type*) [Fintype n] (f : n → ℂ) :
  ∑ i : n, - f i = - ∑ i : n, f i := by
  calc
    ∑ i : n, - f i = ∑ i : n, (-1 : ℂ) * f i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (-1 : ℂ) * ∑ i : n, f i := by rw [← Finset.mul_sum]
    _ = - ∑ i : n, f i := by ring

lemma sum_antisymm_zero (S : Fin 4 → Fin 4 → ℂ) (h : ∀ i j, S i j = - S j i) :
  ∑ i : Fin 4, ∑ j : Fin 4, S i j = 0 := by
  have h1 : ∑ i : Fin 4, ∑ j : Fin 4, S i j = - ∑ i : Fin 4, ∑ j : Fin 4, S i j := by
    calc
      ∑ i : Fin 4, ∑ j : Fin 4, S i j = ∑ j : Fin 4, ∑ i : Fin 4, S i j := Finset.sum_comm
      _ = ∑ i : Fin 4, ∑ j : Fin 4, S j i := rfl
      _ = ∑ i : Fin 4, ∑ j : Fin 4, - S i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact h j i
      _ = ∑ i : Fin 4, - ∑ j : Fin 4, S i j := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_neg_extract _ (fun j => S i j)
      _ = - ∑ i : Fin 4, ∑ j : Fin 4, S i j := sum_neg_extract _ (fun i => ∑ j : Fin 4, S i j)

  have h2 : (2 : ℂ) * (∑ i : Fin 4, ∑ j : Fin 4, S i j) = 0 := by
    let A := ∑ i : Fin 4, ∑ j : Fin 4, S i j
    have h_add : A + A = -A + A := congrArg (fun x => x + A) h1
    calc
      (2 : ℂ) * A = A + A := by ring
      _ = -A + A := h_add
      _ = 0 := by ring

  calc
    ∑ i : Fin 4, ∑ j : Fin 4, S i j = (1 / 2 : ℂ) * ((2 : ℂ) * ∑ i : Fin 4, ∑ j : Fin 4, S i j) := by ring
    _ = (1 / 2 : ℂ) * 0 := by rw [h2]
    _ = 0 := by ring

lemma partialDeriv_re (f : SpacetimePoint → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) :
  (partialDeriv μ f x).re = partialDeriv μ (fun p => (f p).re) x := by
  unfold partialDeriv
  let L : ℂ →L[ℝ] ℝ := {
    toFun := Complex.re
    map_add' := Complex.add_re
    map_smul' := fun r c => by simp
    cont := continuous_re
  }
  have hg : HasFDerivAt L L (f x) := L.hasFDerivAt
  have hf_has : HasFDerivAt f (fderiv ℝ f x) x := hf.hasFDerivAt
  have hc : HasFDerivAt (L ∘ f) (L.comp (fderiv ℝ f x)) x := hg.comp x hf_has
  have h_fderiv : fderiv ℝ (fun p => (f p).re) x = L.comp (fderiv ℝ f x) := hc.fderiv
  rw [h_fderiv]
  rfl

lemma partialDeriv_im (f : SpacetimePoint → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) :
  (partialDeriv μ f x).im = partialDeriv μ (fun p => (f p).im) x := by
  unfold partialDeriv
  let L : ℂ →L[ℝ] ℝ := {
    toFun := Complex.im
    map_add' := Complex.add_im
    map_smul' := fun r c => by simp
    cont := continuous_im
  }
  have hg : HasFDerivAt L L (f x) := L.hasFDerivAt
  have hf_has : HasFDerivAt f (fderiv ℝ f x) x := hf.hasFDerivAt
  have hc : HasFDerivAt (L ∘ f) (L.comp (fderiv ℝ f x)) x := hg.comp x hf_has
  have h_fderiv : fderiv ℝ (fun p => (f p).im) x = L.comp (fderiv ℝ f x) := hc.fderiv
  rw [h_fderiv]
  rfl

lemma partialDeriv_star (f : SpacetimePoint → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) :
  partialDeriv μ (fun p => star (f p)) x = star (partialDeriv μ f x) := by
  let L : ℂ →L[ℝ] ℂ :=
    { toFun := star
      map_add' := star_add
      map_smul' := fun r c => by
        simp only [RingHom.id_apply]
        have h_conj : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
        change star ((r : ℂ) * c) = (r : ℂ) * star c
        rw [star_mul, mul_comm, h_conj]
      cont := continuous_star }
  have h_eq : (fun p => star (f p)) = L ∘ f := rfl
  rw [h_eq]
  have h_has := hf.hasFDerivAt
  have h_L_has : HasFDerivAt L L (f x) := L.hasFDerivAt
  have h_comp := h_L_has.comp x h_has
  unfold partialDeriv
  rw [h_comp.fderiv]
  rfl

lemma partialDeriv_comm_real
  [clairaut : Litlib.Y1976.rudin1976principles.ClairautTheoremNDimensional]
  (f : SpacetimePoint → ℝ)
  (h_smooth : ContDiffOn ℝ 2 f Set.univ)
  (μ ν : Fin 4) (x : SpacetimePoint)
  (h_diff_fderiv : DifferentiableAt ℝ (fderiv ℝ f) x) :
  partialDeriv μ (partialDeriv ν f) x = partialDeriv ν (partialDeriv μ f) x := by
  let u : Fin 4 → ℝ := (Pi.single ν (1:ℝ) : Fin 4 → ℝ)
  let w : Fin 4 → ℝ := (Pi.single μ (1:ℝ) : Fin 4 → ℝ)

  let L_u : ((Fin 4 → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ u
  have hg1 : HasFDerivAt L_u L_u (fderiv ℝ f x) := L_u.hasFDerivAt
  have hf1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x := h_diff_fderiv.hasFDerivAt
  have hc1 : HasFDerivAt (L_u ∘ (fderiv ℝ f)) (L_u.comp (fderiv ℝ (fderiv ℝ f) x)) x := hg1.comp x hf1
  have hc1_fderiv : fderiv ℝ (L_u ∘ (fderiv ℝ f)) x = L_u.comp (fderiv ℝ (fderiv ℝ f) x) := hc1.fderiv

  have h_eval1 : partialDeriv μ (partialDeriv ν f) x = fderiv ℝ (fderiv ℝ f) x w u := by
    unfold partialDeriv
    have heq : (fun p => fderiv ℝ f p u) = L_u ∘ (fderiv ℝ f) := rfl
    rw [heq, hc1_fderiv]
    rfl

  let L_w : ((Fin 4 → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ w
  have hg2 : HasFDerivAt L_w L_w (fderiv ℝ f x) := L_w.hasFDerivAt
  have hc2 : HasFDerivAt (L_w ∘ (fderiv ℝ f)) (L_w.comp (fderiv ℝ (fderiv ℝ f) x)) x := hg2.comp x hf1
  have hc2_fderiv : fderiv ℝ (L_w ∘ (fderiv ℝ f)) x = L_w.comp (fderiv ℝ (fderiv ℝ f) x) := hc2.fderiv

  have h_eval2 : partialDeriv ν (partialDeriv μ f) x = fderiv ℝ (fderiv ℝ f) x u w := by
    unfold partialDeriv
    have heq : (fun p => fderiv ℝ f p w) = L_w ∘ (fderiv ℝ f) := rfl
    rw [heq, hc2_fderiv]
    rfl

  rw [h_eval1, h_eval2]

  let v : Fin 2 → (Fin 4 → ℝ) := fun i => if i = 0 then u else w
  let sig : Equiv.Perm (Fin 2) := Equiv.swap 0 1

  have hc_clairaut := clairaut.symmetry_of_higher_partials 4 2 Set.univ isOpen_univ f h_smooth x (Set.mem_univ x) v sig

  have hr1 : iteratedFDeriv ℝ 2 f x v = fderiv ℝ (fderiv ℝ f) x u w := by
    have h : iteratedFDeriv ℝ 2 f x v = fderiv ℝ (fderiv ℝ f) x (v 0) (v 1) := iteratedFDeriv_two_apply f x v
    rw [h]
    rfl

  have hr2 : iteratedFDeriv ℝ 2 f x (fun i => v (sig i)) = fderiv ℝ (fderiv ℝ f) x w u := by
    have h : iteratedFDeriv ℝ 2 f x (fun i => v (sig i)) = fderiv ℝ (fderiv ℝ f) x (v (sig 0)) (v (sig 1)) := iteratedFDeriv_two_apply f x (fun i => v (sig i))
    rw [h]
    rfl

  rw [hr2, hr1] at hc_clairaut
  exact hc_clairaut

lemma contDiff_fderiv_of_contDiff_real {f : SpacetimePoint → ℝ} (hf : ContDiff ℝ ⊤ f) :
  ContDiff ℝ ⊤ (fderiv ℝ f) := by
  let snd_clm : (SpacetimePoint × SpacetimePoint) →L[ℝ] SpacetimePoint := ContinuousLinearMap.snd ℝ SpacetimePoint SpacetimePoint
  have hf_snd : ContDiff ℝ ⊤ (fun p : SpacetimePoint × SpacetimePoint => f p.2) :=
    ContDiff.comp (g := f) (f := Prod.snd) hf snd_clm.contDiff
  let id_clm : SpacetimePoint →L[ℝ] SpacetimePoint := ContinuousLinearMap.id ℝ SpacetimePoint
  exact ContDiff.fderiv (f := fun _ y => f y) (g := fun x => x) hf_snd id_clm.contDiff le_top

lemma contDiff_partialDeriv_complex (μ : Fin 4) (f : SpacetimePoint → ℂ) (hf : ContDiff ℝ ⊤ f) :
  ContDiff ℝ ⊤ (partialDeriv μ f) := by
  unfold partialDeriv
  let w : Fin 4 → ℝ := Pi.single μ 1
  have h_w : ContDiff ℝ ⊤ (fun (x : SpacetimePoint) => w) := contDiff_const
  let snd_clm : (SpacetimePoint × SpacetimePoint) →L[ℝ] SpacetimePoint := ContinuousLinearMap.snd ℝ SpacetimePoint SpacetimePoint
  have hf_snd : ContDiff ℝ ⊤ (fun (p : SpacetimePoint × SpacetimePoint) => f p.2) := ContDiff.comp (g := f) (f := Prod.snd) hf snd_clm.contDiff
  let id_clm : SpacetimePoint →L[ℝ] SpacetimePoint := ContinuousLinearMap.id ℝ SpacetimePoint
  have h_fderiv : ContDiff ℝ ⊤ (fderiv ℝ f) := ContDiff.fderiv (f := fun _ y => f y) (g := fun x => x) hf_snd id_clm.contDiff le_top
  exact ContDiff.clm_apply h_fderiv h_w

end CGD.Math

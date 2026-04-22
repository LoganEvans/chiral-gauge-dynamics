-- FILENAME: CGD/Foundations/TensorCalculus/DifferentialRules.lean

import Litlib.Y2003.nakahara2003geometry.Signature
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option linter.unusedVariables false

open Matrix Complex BigOperators CGD.Axioms Litlib.Y2003.nakahara2003geometry

namespace CGD.Foundations

/-- True geometric definition of the gauge covariant derivative of the field strength tensor: 
    D_α F_βγ = ∂_α F_βγ + [A_α, F_βγ] -/
noncomputable def covariantDeriv (A : Fin 4 → SpacetimePoint → SL2C) (alpha beta gamma : Fin 4) (x : SpacetimePoint) : SL2C :=
  let dF := partialDerivSl2c alpha (fun p => curvatureSl2c A beta gamma p) x
  let comm := ⁅A alpha x, curvatureSl2c A beta gamma x⁆
  dF + comm

lemma partialDeriv_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} (s : Finset ι) (A : ι → SpacetimePoint → E) (μ : Fin 4) (x : SpacetimePoint)
  (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) x) :
  partialDeriv μ (fun p => ∑ i ∈ s, A i p) x = ∑ i ∈ s, partialDeriv μ (A i) x := by
  unfold partialDeriv
  have h_eq : (fun p => ∑ i ∈ s, A i p) = ∑ i ∈ s, A i := by
    ext p
    rw [Finset.sum_apply]
  rw [h_eq, fderiv_sum h]
  exact ContinuousLinearMap.sum_apply _ _ _

lemma partialDerivMat_commutes (f : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (μ ν : Fin 4) (x : SpacetimePoint)
  (h_smooth : ∀ i j, ContDiff ℝ ⊤ (fun p => f p i j)) :
  partialDerivMat μ (fun p => partialDerivMat ν f p) x = 
  partialDerivMat ν (fun p => partialDerivMat μ f p) x := by
  ext i j
  unfold partialDerivMat partialDeriv
  have hf_smooth : ContDiff ℝ ⊤ (fun p => f p i j) := h_smooth i j
  have h_diff : Differentiable ℝ (fun p => f p i j) := hf_smooth.differentiable (by decide)
  have h_hasFDeriv : ∀ y, HasFDerivAt (fun p => f p i j) (fderiv ℝ (fun p => f p i j) y) y := fun y => (h_diff y).hasFDerivAt
  
  have h_diff_deriv : DifferentiableAt ℝ (fderiv ℝ (fun p => f p i j)) x := by
    have h_deriv_smooth : ContDiff ℝ 1 (fderiv ℝ (fun p => f p i j)) := hf_smooth.fderiv_right (by decide)
    exact (h_deriv_smooth.differentiable (by decide)) x
    
  have h_symm := second_derivative_symmetric (f := fun p => f p i j) (f' := fderiv ℝ (fun p => f p i j)) (x := x) h_hasFDeriv h_diff_deriv.hasFDerivAt
  
  let v_μ : Fin 4 → ℝ := Pi.single μ 1
  let v_ν : Fin 4 → ℝ := Pi.single ν 1

  have h_apply := h_symm v_μ v_ν

  have h_eq_ν : (fun p => fderiv ℝ (fun p => f p i j) p v_ν) = (ContinuousLinearMap.apply ℝ ℂ v_ν) ∘ (fderiv ℝ (fun p => f p i j)) := rfl
  have h_eq_μ : (fun p => fderiv ℝ (fun p => f p i j) p v_μ) = (ContinuousLinearMap.apply ℝ ℂ v_μ) ∘ (fderiv ℝ (fun p => f p i j)) := rfl

  rw [h_eq_ν, h_eq_μ]
  rw [fderiv_comp x (ContinuousLinearMap.apply ℝ ℂ v_ν).differentiableAt h_diff_deriv]
  rw [fderiv_comp x (ContinuousLinearMap.apply ℝ ℂ v_μ).differentiableAt h_diff_deriv]

  rw [ContinuousLinearMap.fderiv]
  rw [ContinuousLinearMap.fderiv]
  
  change (fderiv ℝ (fderiv ℝ (fun p => f p i j)) x v_μ) v_ν = (fderiv ℝ (fderiv ℝ (fun p => f p i j)) x v_ν) v_μ
  exact h_apply

lemma partialDeriv_add_local (f g : SpacetimePoint → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
  partialDeriv μ (fun p => f p + g p) x = partialDeriv μ f x + partialDeriv μ g x := by
  unfold partialDeriv
  have h_has := HasFDerivAt.add hf.hasFDerivAt hg.hasFDerivAt
  have h_eq : (fun p => f p + g p) = f + g := rfl
  rw [h_eq, h_has.fderiv]
  rfl

lemma partialDeriv_sub_local (f g : SpacetimePoint → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
  partialDeriv μ (fun p => f p - g p) x = partialDeriv μ f x - partialDeriv μ g x := by
  unfold partialDeriv
  have h_has := HasFDerivAt.sub hf.hasFDerivAt hg.hasFDerivAt
  have h_eq : (fun p => f p - g p) = f - g := rfl
  rw [h_eq, h_has.fderiv]
  rfl

lemma partialDerivMat_trace (f : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => f p i j) x) :
  Matrix.trace (partialDerivMat μ f x) = partialDeriv μ (fun p => Matrix.trace (f p)) x := by
  unfold partialDerivMat Matrix.trace
  exact (partialDeriv_sum _ _ μ x (fun i _ => hf i i)).symm

lemma partialDerivSl2c_eq_mat (A : SpacetimePoint → SL2C) (μ : Fin 4) (x : SpacetimePoint)
  (hA : ∀ i j, DifferentiableAt ℝ (fun p => (A p).val i j) x) :
  (partialDerivSl2c μ A x).val = partialDerivMat μ (fun p => (A p).val) x := by
  unfold partialDerivSl2c toSl2c
  dsimp
  have h_tr_zero : (fun p => Matrix.trace ((A p).val)) = fun p => 0 := by
    ext p
    exact (A p).property
  have h_tr : Matrix.trace (partialDerivMat μ (fun p => (A p).val) x) = partialDeriv μ (fun p => Matrix.trace ((A p).val)) x := partialDerivMat_trace _ μ x hA
  rw [h_tr_zero] at h_tr
  have h_pd_zero : partialDeriv μ (fun (p : SpacetimePoint) => (0 : ℂ)) x = 0 := partialDeriv_const 0 μ x
  rw [h_pd_zero] at h_tr
  rw [h_tr]
  have hz : (0 : ℂ) / 2 = 0 := by ring
  rw [hz, zero_smul, sub_zero]

lemma partialDerivSl2c_commutes (A : Fin 4 → SpacetimePoint → SL2C) (α μ ν : Fin 4) (x : SpacetimePoint)
  (h_smooth : ∀ i j, ContDiff ℝ ⊤ (fun p => (A α p).val i j)) :
  partialDerivSl2c μ (fun p => partialDerivSl2c ν (A α) p) x = 
  partialDerivSl2c ν (fun p => partialDerivSl2c μ (A α) p) x := by
  
  have h_diff : ∀ i j, Differentiable ℝ (fun p => (A α p).val i j) := fun i j => (h_smooth i j).differentiable (by decide)
  have hd_A : ∀ y i j, DifferentiableAt ℝ (fun p => (A α p).val i j) y := fun y i j => (h_diff i j) y
  
  have hd_nu : ∀ y, (partialDerivSl2c ν (A α) y).val = partialDerivMat ν (fun p => (A α p).val) y := fun y => partialDerivSl2c_eq_mat (A α) ν y (hd_A y)
  have hd_mu : ∀ y, (partialDerivSl2c μ (A α) y).val = partialDerivMat μ (fun p => (A α p).val) y := fun y => partialDerivSl2c_eq_mat (A α) μ y (hd_A y)

  apply Subtype.ext
  
  have hd_mu_nu_smooth : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c ν (A α) p).val i j) x := by
    intro i j
    have h_eq : (fun p => (partialDerivSl2c ν (A α) p).val i j) = fun p => partialDeriv ν (fun p2 => (A α p2).val i j) p := by
      ext p
      exact congr_fun (congr_fun (hd_nu p) i) j
    rw [h_eq]
    have h_deriv_smooth : ContDiff ℝ 1 (fderiv ℝ (fun p => (A α p).val i j)) := (h_smooth i j).fderiv_right (by decide)
    have hd_deriv : DifferentiableAt ℝ (fderiv ℝ (fun p => (A α p).val i j)) x := (h_deriv_smooth.differentiable (by decide)) x
    have h_apply : (fun p => partialDeriv ν (fun p2 => (A α p2).val i j) p) = (ContinuousLinearMap.apply ℝ ℂ ((Pi.single ν (1 : ℝ)) : Fin 4 → ℝ)) ∘ (fderiv ℝ (fun p => (A α p).val i j)) := rfl
    rw [h_apply]
    exact DifferentiableAt.comp x (ContinuousLinearMap.apply ℝ ℂ ((Pi.single ν (1 : ℝ)) : Fin 4 → ℝ)).differentiableAt hd_deriv

  have hd_nu_mu_smooth : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c μ (A α) p).val i j) x := by
    intro i j
    have h_eq : (fun p => (partialDerivSl2c μ (A α) p).val i j) = fun p => partialDeriv μ (fun p2 => (A α p2).val i j) p := by
      ext p
      exact congr_fun (congr_fun (hd_mu p) i) j
    rw [h_eq]
    have h_deriv_smooth : ContDiff ℝ 1 (fderiv ℝ (fun p => (A α p).val i j)) := (h_smooth i j).fderiv_right (by decide)
    have hd_deriv : DifferentiableAt ℝ (fderiv ℝ (fun p => (A α p).val i j)) x := (h_deriv_smooth.differentiable (by decide)) x
    have h_apply : (fun p => partialDeriv μ (fun p2 => (A α p2).val i j) p) = (ContinuousLinearMap.apply ℝ ℂ ((Pi.single μ (1 : ℝ)) : Fin 4 → ℝ)) ∘ (fderiv ℝ (fun p => (A α p).val i j)) := rfl
    rw [h_apply]
    exact DifferentiableAt.comp x (ContinuousLinearMap.apply ℝ ℂ ((Pi.single μ (1 : ℝ)) : Fin 4 → ℝ)).differentiableAt hd_deriv

  rw [partialDerivSl2c_eq_mat (fun p => partialDerivSl2c ν (A α) p) μ x hd_mu_nu_smooth]
  rw [partialDerivSl2c_eq_mat (fun p => partialDerivSl2c μ (A α) p) ν x hd_nu_mu_smooth]

  have h_eq_lhs : partialDerivMat μ (fun p => (partialDerivSl2c ν (A α) p).val) x = partialDerivMat μ (fun p => partialDerivMat ν (fun p2 => (A α p2).val) p) x := by
    unfold partialDerivMat partialDeriv
    have h_fun_eq : (fun p => (partialDerivSl2c ν (A α) p).val) = fun p => partialDerivMat ν (fun p2 => (A α p2).val) p := by
      ext p i j
      exact congr_fun (congr_fun (hd_nu p) i) j
    rw [h_fun_eq]
    rfl
    
  have h_eq_rhs : partialDerivMat ν (fun p => (partialDerivSl2c μ (A α) p).val) x = partialDerivMat ν (fun p => partialDerivMat μ (fun p2 => (A α p2).val) p) x := by
    unfold partialDerivMat partialDeriv
    have h_fun_eq : (fun p => (partialDerivSl2c μ (A α) p).val) = fun p => partialDerivMat μ (fun p2 => (A α p2).val) p := by
      ext p i j
      exact congr_fun (congr_fun (hd_mu p) i) j
    rw [h_fun_eq]
    rfl

  rw [h_eq_lhs, h_eq_rhs]
  exact partialDerivMat_commutes (fun p => (A α p).val) μ ν x h_smooth

lemma partialDerivMat_mul (f g : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => f p i j) x)
  (hg : ∀ i j, DifferentiableAt ℝ (fun p => g p i j) x) :
  partialDerivMat μ (fun p => f p * g p) x = partialDerivMat μ f x * g x + f x * partialDerivMat μ g x := by
  ext i j
  unfold partialDerivMat
  have h_eq : (fun p => (f p * g p) i j) = fun p => ∑ k : Fin 2, f p i k * g p k j := rfl
  rw [h_eq]
  rw [partialDeriv_sum]
  · simp only [Matrix.add_apply, Matrix.mul_apply]
    have h_eval_sum : (∑ k : Fin 2, partialDeriv μ (fun p => f p i k * g p k j) x) =
                      ∑ k : Fin 2, (f x i k * partialDeriv μ (fun p => g p k j) x + partialDeriv μ (fun p => f p i k) x * g x k j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [partialDeriv_mul_c _ _ _ _ (hf i k) (hg k j)]
    rw [h_eval_sum]
    rw [Finset.sum_add_distrib]
    have h_swap : (∑ k : Fin 2, f x i k * partialDeriv μ (fun p => g p k j) x) + (∑ k : Fin 2, partialDeriv μ (fun p => f p i k) x * g x k j) =
                  (∑ k : Fin 2, partialDeriv μ (fun p => f p i k) x * g x k j) + (∑ k : Fin 2, f x i k * partialDeriv μ (fun p => g p k j) x) := add_comm _ _
    rw [h_swap]
  · intro k _
    exact DifferentiableAt.mul (hf i k) (hg k j)

lemma partialDerivMat_sub (f g : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => f p i j) x)
  (hg : ∀ i j, DifferentiableAt ℝ (fun p => g p i j) x) :
  partialDerivMat μ (fun p => f p - g p) x = partialDerivMat μ f x - partialDerivMat μ g x := by
  ext i j
  unfold partialDerivMat partialDeriv
  have h_eq : (fun p => (f p - g p) i j) = (fun p => f p i j) - (fun p => g p i j) := rfl
  rw [h_eq]
  have h_has := HasFDerivAt.sub (hf i j).hasFDerivAt (hg i j).hasFDerivAt
  rw [h_has.fderiv]
  rfl

lemma diff_matrix_mul (f g : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (x : SpacetimePoint)
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => f p i j) x)
  (hg : ∀ i j, DifferentiableAt ℝ (fun p => g p i j) x) :
  ∀ i j, DifferentiableAt ℝ (fun p => (f p * g p) i j) x := by
  intro i j
  have h_eq : (fun p => (f p * g p) i j) = ∑ k : Fin 2, (fun p => f p i k * g p k j) := by
    ext p
    rw [Finset.sum_apply]
    rfl
  rw [h_eq]
  apply DifferentiableAt.sum
  intro k _
  exact DifferentiableAt.mul (hf i k) (hg k j)

lemma diff_matrix_sub (f g : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (x : SpacetimePoint)
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => f p i j) x)
  (hg : ∀ i j, DifferentiableAt ℝ (fun p => g p i j) x) :
  ∀ i j, DifferentiableAt ℝ (fun p => (f p - g p) i j) x := by
  intro i j
  have h_eq : (fun p => (f p - g p) i j) = fun p => f p i j - g p i j := rfl
  rw [h_eq]
  exact DifferentiableAt.sub (hf i j) (hg i j)

lemma partialDerivSl2c_bracket (A B : SpacetimePoint → SL2C) (μ : Fin 4) (x : SpacetimePoint) 
  (hA : ∀ i j, DifferentiableAt ℝ (fun p => (A p).val i j) x)
  (hB : ∀ i j, DifferentiableAt ℝ (fun p => (B p).val i j) x) :
  partialDerivSl2c μ (fun p => ⁅A p, B p⁆) x = ⁅partialDerivSl2c μ A x, B x⁆ + ⁅A x, partialDerivSl2c μ B x⁆ := by
  have hd_AB := diff_matrix_mul _ _ x hA hB
  have hd_BA := diff_matrix_mul _ _ x hB hA
  have hd_br := diff_matrix_sub _ _ x hd_AB hd_BA
  
  apply Subtype.ext
  have h_val_lhs : (partialDerivSl2c μ (fun p => ⁅A p, B p⁆) x).val = partialDerivMat μ (fun p => (A p).val * (B p).val - (B p).val * (A p).val) x := by
    have h1 : (partialDerivSl2c μ (fun p => ⁅A p, B p⁆) x).val = partialDerivMat μ (fun p => ⁅A p, B p⁆.val) x := partialDerivSl2c_eq_mat (fun p => ⁅A p, B p⁆) μ x hd_br
    rw [h1]
    rfl
    
  rw [h_val_lhs]
  rw [partialDerivMat_sub _ _ μ x hd_AB hd_BA]
  rw [partialDerivMat_mul _ _ μ x hA hB]
  rw [partialDerivMat_mul _ _ μ x hB hA]
  
  have h_dA := partialDerivSl2c_eq_mat A μ x hA
  have h_dB := partialDerivSl2c_eq_mat B μ x hB
  
  have h_rhs1 : ⁅partialDerivSl2c μ A x, B x⁆.val = (partialDerivSl2c μ A x).val * (B x).val - (B x).val * (partialDerivSl2c μ A x).val := rfl
  have h_rhs2 : ⁅A x, partialDerivSl2c μ B x⁆.val = (A x).val * (partialDerivSl2c μ B x).val - (partialDerivSl2c μ B x).val * (A x).val := rfl
  
  change _ = ⁅partialDerivSl2c μ A x, B x⁆.val + ⁅A x, partialDerivSl2c μ B x⁆.val
  rw [h_rhs1, h_rhs2, h_dA, h_dB]
  
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply]
  ring

lemma partialDerivMat_add (f g : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => f p i j) x)
  (hg : ∀ i j, DifferentiableAt ℝ (fun p => g p i j) x) :
  partialDerivMat μ (fun p => f p + g p) x = partialDerivMat μ f x + partialDerivMat μ g x := by
  ext i j
  unfold partialDerivMat partialDeriv
  have h_eq : (fun p => (f p + g p) i j) = (fun p => f p i j) + (fun p => g p i j) := rfl
  rw [h_eq]
  have h_has := HasFDerivAt.add (hf i j).hasFDerivAt (hg i j).hasFDerivAt
  rw [h_has.fderiv]
  rfl

lemma partialDerivSl2c_add (f g : SpacetimePoint → SL2C) (μ : Fin 4) (x : SpacetimePoint) 
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => (f p).val i j) x)
  (hg : ∀ i j, DifferentiableAt ℝ (fun p => (g p).val i j) x) :
  partialDerivSl2c μ (fun p => f p + g p) x = partialDerivSl2c μ f x + partialDerivSl2c μ g x := by
  unfold partialDerivSl2c
  have h_val : (fun p => (f p + g p).val) = fun p => (f p).val + (g p).val := rfl
  rw [h_val]
  have h_mat := partialDerivMat_add (fun p => (f p).val) (fun p => (g p).val) μ x hf hg
  rw [h_mat]
  apply Subtype.ext
  unfold toSl2c
  dsimp
  ext i j
  simp only [Matrix.add_apply, Matrix.trace]
  by_cases h : i = j
  · simp [h]; try ring_nf
  · simp [h]; try ring_nf

lemma partialDerivMat_sub_c (f g : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => f p i j) x)
  (hg : ∀ i j, DifferentiableAt ℝ (fun p => g p i j) x) :
  partialDerivMat μ (fun p => f p - g p) x = partialDerivMat μ f x - partialDerivMat μ g x := by
  ext i j
  unfold partialDerivMat partialDeriv
  have h_eq : (fun p => (f p - g p) i j) = (fun p => f p i j) - (fun p => g p i j) := rfl
  rw [h_eq]
  have h_has := HasFDerivAt.sub (hf i j).hasFDerivAt (hg i j).hasFDerivAt
  rw [h_has.fderiv]
  rfl

lemma partialDerivSl2c_sub (f g : SpacetimePoint → SL2C) (μ : Fin 4) (x : SpacetimePoint) 
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => (f p).val i j) x)
  (hg : ∀ i j, DifferentiableAt ℝ (fun p => (g p).val i j) x) :
  partialDerivSl2c μ (fun p => f p - g p) x = partialDerivSl2c μ f x - partialDerivSl2c μ g x := by
  unfold partialDerivSl2c
  have h_val : (fun p => (f p - g p).val) = fun p => (f p).val - (g p).val := rfl
  rw [h_val]
  have h_mat := partialDerivMat_sub_c (fun p => (f p).val) (fun p => (g p).val) μ x hf hg
  rw [h_mat]
  apply Subtype.ext
  unfold toSl2c
  dsimp
  ext i j
  simp only [Matrix.sub_apply, Matrix.trace]
  by_cases h : i = j
  · simp [h]; try ring_nf
  · simp [h]; try ring_nf

lemma diff_A (A : Fin 4 → SpacetimePoint → SL2C) (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j)) 
  (α : Fin 4) (i j : Fin 2) (x : SpacetimePoint) :
  DifferentiableAt ℝ (fun p => (A α p).val i j) x := 
  ((h_smooth α i j).differentiable (by decide)) x

lemma diff_dA (A : Fin 4 → SpacetimePoint → SL2C) (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j)) 
  (α β : Fin 4) (i j : Fin 2) (x : SpacetimePoint) :
  DifferentiableAt ℝ (fun p => (partialDerivSl2c α (A β) p).val i j) x := by
  have h_eq : (fun p => (partialDerivSl2c α (A β) p).val i j) = fun p => partialDeriv α (fun p2 => (A β p2).val i j) p := by
    ext p
    have h1 := partialDerivSl2c_eq_mat (A β) α p (fun i j => diff_A A h_smooth β i j p)
    exact congr_fun (congr_fun h1 i) j
  rw [h_eq]
  have h_deriv_smooth : ContDiff ℝ 1 (fderiv ℝ (fun p => (A β p).val i j)) := (h_smooth β i j).fderiv_right (by decide)
  have hd_deriv : DifferentiableAt ℝ (fderiv ℝ (fun p => (A β p).val i j)) x := (h_deriv_smooth.differentiable (by decide)) x
  have h_apply : (fun p => partialDeriv α (fun p2 => (A β p2).val i j) p) = (ContinuousLinearMap.apply ℝ ℂ ((Pi.single α (1 : ℝ)) : Fin 4 → ℝ)) ∘ (fderiv ℝ (fun p => (A β p).val i j)) := rfl
  rw [h_apply]
  exact DifferentiableAt.comp x (ContinuousLinearMap.apply ℝ ℂ ((Pi.single α (1 : ℝ)) : Fin 4 → ℝ)).differentiableAt hd_deriv

lemma diff_comm (A : Fin 4 → SpacetimePoint → SL2C) (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j)) 
  (α β : Fin 4) (i j : Fin 2) (x : SpacetimePoint) :
  DifferentiableAt ℝ (fun p => (⁅A α p, A β p⁆).val i j) x := by
  have h_eq : (fun p => (⁅A α p, A β p⁆).val i j) = fun p => ((A α p).val * (A β p).val - (A β p).val * (A α p).val) i j := rfl
  rw [h_eq]
  have hdA_alpha : ∀ i j, DifferentiableAt ℝ (fun p => (A α p).val i j) x := fun i j => diff_A A h_smooth α i j x
  have hdA_beta : ∀ i j, DifferentiableAt ℝ (fun p => (A β p).val i j) x := fun i j => diff_A A h_smooth β i j x
  have h_mul1 := diff_matrix_mul (fun p => (A α p).val) (fun p => (A β p).val) x hdA_alpha hdA_beta
  have h_mul2 := diff_matrix_mul (fun p => (A β p).val) (fun p => (A α p).val) x hdA_beta hdA_alpha
  exact diff_matrix_sub (fun p => (A α p).val * (A β p).val) (fun p => (A β p).val * (A α p).val) x h_mul1 h_mul2 i j

lemma diff_curvature (A : Fin 4 → SpacetimePoint → SL2C) (h_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (A mu x).val i j)) 
  (α β : Fin 4) (i j : Fin 2) (x : SpacetimePoint) :
  DifferentiableAt ℝ (fun p => (curvatureSl2c A α β p).val i j) x := by
  have h_eq : (fun p => (curvatureSl2c A α β p).val i j) = fun p => (partialDerivSl2c α (A β) p - partialDerivSl2c β (A α) p + ⁅A α p, A β p⁆).val i j := by
    ext p
    rw [curvatureSl2c_def]
  rw [h_eq]
  
  have hd_dA_ab : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c α (A β) p).val i j) x := fun i j => diff_dA A h_smooth α β i j x
  have hd_dA_ba : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c β (A α) p).val i j) x := fun i j => diff_dA A h_smooth β α i j x
  
  have hdSub : DifferentiableAt ℝ (fun p => (partialDerivSl2c α (A β) p).val i j - (partialDerivSl2c β (A α) p).val i j) x := 
    DifferentiableAt.sub (hd_dA_ab i j) (hd_dA_ba i j)
    
  have hdComm := diff_comm A h_smooth α β i j x
  
  have h_final_eq : (fun p => (partialDerivSl2c α (A β) p - partialDerivSl2c β (A α) p + ⁅A α p, A β p⁆).val i j) = 
                    fun p => ((partialDerivSl2c α (A β) p).val i j - (partialDerivSl2c β (A α) p).val i j) + ⁅A α p, A β p⁆.val i j := rfl
  rw [h_final_eq]
  
  exact DifferentiableAt.add hdSub hdComm

-- Abelian Exact Solutions and Collapse
lemma commutator_smul_smul (c1 c2 : ℂ) (M : SL2C) : ⁅c1 • M, c2 • M⁆ = 0 := by
  apply Subtype.ext
  change (c1 • M.val) * (c2 • M.val) - (c2 • M.val) * (c1 • M.val) = 0
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h_comm : c1 * c2 = c2 * c1 := mul_comm _ _
  rw [h_comm, sub_self]

lemma diff_ContDiff_1 (f : SpacetimePoint → ℂ) (h : ContDiff ℝ ⊤ f) (x : SpacetimePoint) : DifferentiableAt ℝ f x := 
  (h.differentiable (by decide)) x

lemma diff_ContDiff_2 (f : SpacetimePoint → ℂ) (h : ContDiff ℝ ⊤ f) (μ : Fin 4) (x : SpacetimePoint) : DifferentiableAt ℝ (fun p => partialDeriv μ f p) x := by
  have h_deriv_smooth : ContDiff ℝ 1 (fderiv ℝ f) := h.fderiv_right (by decide)
  have hd_deriv : DifferentiableAt ℝ (fderiv ℝ f) x := (h_deriv_smooth.differentiable (by decide)) x
  have h_apply : (fun p => partialDeriv μ f p) = (ContinuousLinearMap.apply ℝ ℂ ((Pi.single μ (1 : ℝ)) : Fin 4 → ℝ)) ∘ (fderiv ℝ f) := rfl
  rw [h_apply]
  exact DifferentiableAt.comp x (ContinuousLinearMap.apply ℝ ℂ ((Pi.single μ (1 : ℝ)) : Fin 4 → ℝ)).differentiableAt hd_deriv

lemma abelian_curvature_collapse 
  (f : Fin 4 → SpacetimePoint → ℂ) (M : SL2C) 
  (μ ν : Fin 4) (x : SpacetimePoint)
  (hf_smooth : ∀ α, DifferentiableAt ℝ (f α) x) :
  curvatureSl2c (fun α p => f α p • M) μ ν x = (partialDeriv μ (f ν) x - partialDeriv ν (f μ) x) • M := by
  rw [curvatureSl2c_def]
  rw [partialDerivSl2c_smul_c_fun _ _ _ _ (hf_smooth ν)]
  rw [partialDerivSl2c_smul_c_fun _ _ _ _ (hf_smooth μ)]
  have h_comm : ⁅f μ x • M, f ν x • M⁆ = 0 := commutator_smul_smul (f μ x) (f ν x) M
  rw [h_comm, add_zero, ←sub_smul]

lemma abelian_covariant_collapse 
  (f : Fin 4 → SpacetimePoint → ℂ) (M : SL2C) 
  (α β γ : Fin 4) (x : SpacetimePoint)
  (hf_smooth : ∀ μ p, DifferentiableAt ℝ (f μ) p)
  (hf_diff2 : DifferentiableAt ℝ (fun p => partialDeriv β (f γ) p - partialDeriv γ (f β) p) x) :
  covariantDeriv (fun μ p => f μ p • M) α β γ x = partialDeriv α (fun p => partialDeriv β (f γ) p - partialDeriv γ (f β) p) x • M := by
  unfold covariantDeriv
  dsimp
  have hF_eq : (fun p => curvatureSl2c (fun μ p' => f μ p' • M) β γ p) = fun p => (partialDeriv β (f γ) p - partialDeriv γ (f β) p) • M := by
    apply funext
    intro p
    exact abelian_curvature_collapse f M β γ p (fun μ => hf_smooth μ p)
  rw [hF_eq]
  rw [partialDerivSl2c_smul_c_fun _ _ _ _ hf_diff2]
  have hF_x : ((partialDeriv β (f γ) x - partialDeriv γ (f β) x) • M) = curvatureSl2c (fun μ p' => f μ p' • M) β γ x := by
    rw [abelian_curvature_collapse f M β γ x (fun μ => hf_smooth μ x)]
  have h_comm : ⁅f α x • M, (partialDeriv β (f γ) x - partialDeriv γ (f β) x) • M⁆ = 0 := commutator_smul_smul (f α x) _ M
  rw [←hF_x, h_comm, add_zero]

lemma abelian_covariant_eval
  (f : Fin 4 → SpacetimePoint → ℂ) (M : SL2C) 
  (α β γ : Fin 4) (x : SpacetimePoint)
  (hf : ∀ μ, ContDiff ℝ ⊤ (f μ)) :
  covariantDeriv (fun μ p => f μ p • M) α β γ x = 
    (partialDeriv α (fun p => partialDeriv β (f γ) p) x - partialDeriv α (fun p => partialDeriv γ (f β) p) x) • M := by
  have h_diff_f : ∀ μ p, DifferentiableAt ℝ (f μ) p := fun μ p => diff_ContDiff_1 (f μ) (hf μ) p
  have h_diff_df1 : ∀ p, DifferentiableAt ℝ (fun p => partialDeriv β (f γ) p) p := fun p => diff_ContDiff_2 (f γ) (hf γ) β p
  have h_diff_df2 : ∀ p, DifferentiableAt ℝ (fun p => partialDeriv γ (f β) p) p := fun p => diff_ContDiff_2 (f β) (hf β) γ p
  
  have h_diff_sub : DifferentiableAt ℝ (fun p => partialDeriv β (f γ) p - partialDeriv γ (f β) p) x := 
    DifferentiableAt.sub (h_diff_df1 x) (h_diff_df2 x)

  rw [abelian_covariant_collapse f M α β γ x h_diff_f h_diff_sub]
  rw [partialDeriv_sub_local (fun p => partialDeriv β (f γ) p) (fun p => partialDeriv γ (f β) p) α x (h_diff_df1 x) (h_diff_df2 x)]

lemma abelian_curvature_add
  (f g : Fin 4 → SpacetimePoint → ℂ) (M : SL2C) 
  (μ ν : Fin 4) (x : SpacetimePoint)
  (hf : ∀ α, ContDiff ℝ ⊤ (f α))
  (hg : ∀ α, ContDiff ℝ ⊤ (g α)) :
  curvatureSl2c (fun α p => (f α p + g α p) • M) μ ν x = 
    curvatureSl2c (fun α p => f α p • M) μ ν x + 
    curvatureSl2c (fun α p => g α p • M) μ ν x := by
  
  have h_diff_f : ∀ α, DifferentiableAt ℝ (f α) x := fun α => diff_ContDiff_1 (f α) (hf α) x
  have h_diff_g : ∀ α, DifferentiableAt ℝ (g α) x := fun α => diff_ContDiff_1 (g α) (hg α) x
  have h_diff_add : ∀ α, DifferentiableAt ℝ (fun p => f α p + g α p) x := fun α => DifferentiableAt.add (h_diff_f α) (h_diff_g α)
  
  rw [abelian_curvature_collapse (fun α p => f α p + g α p) M μ ν x h_diff_add]
  rw [abelian_curvature_collapse f M μ ν x h_diff_f]
  rw [abelian_curvature_collapse g M μ ν x h_diff_g]
  
  rw [partialDeriv_add_local _ _ μ x (h_diff_f ν) (h_diff_g ν)]
  rw [partialDeriv_add_local _ _ ν x (h_diff_f μ) (h_diff_g μ)]
  
  have h_alg : (partialDeriv μ (f ν) x + partialDeriv μ (g ν) x - (partialDeriv ν (f μ) x + partialDeriv ν (g μ) x)) = 
               (partialDeriv μ (f ν) x - partialDeriv ν (f μ) x) + (partialDeriv μ (g ν) x - partialDeriv ν (g μ) x) := by ring
  rw [h_alg, add_smul]

lemma abelian_covariant_add
  (f g : Fin 4 → SpacetimePoint → ℂ) (M : SL2C) 
  (α β γ : Fin 4) (x : SpacetimePoint)
  (hf : ∀ μ, ContDiff ℝ ⊤ (f μ))
  (hg : ∀ μ, ContDiff ℝ ⊤ (g μ)) :
  covariantDeriv (fun μ p => (f μ p + g μ p) • M) α β γ x = 
    covariantDeriv (fun μ p => f μ p • M) α β γ x + 
    covariantDeriv (fun μ p => g μ p • M) α β γ x := by

  have h_add_cd : ∀ μ, ContDiff ℝ ⊤ (fun p => f μ p + g μ p) := fun μ => ContDiff.add (hf μ) (hg μ)
  
  rw [abelian_covariant_eval (fun μ p => f μ p + g μ p) M α β γ x h_add_cd]
  rw [abelian_covariant_eval f M α β γ x hf]
  rw [abelian_covariant_eval g M α β γ x hg]

  have h_diff_df1 : ∀ p, DifferentiableAt ℝ (fun p => partialDeriv β (f γ) p) p := fun p => diff_ContDiff_2 (f γ) (hf γ) β p
  have h_diff_df2 : ∀ p, DifferentiableAt ℝ (fun p => partialDeriv γ (f β) p) p := fun p => diff_ContDiff_2 (f β) (hf β) γ p
  have h_diff_dg1 : ∀ p, DifferentiableAt ℝ (fun p => partialDeriv β (g γ) p) p := fun p => diff_ContDiff_2 (g γ) (hg γ) β p
  have h_diff_dg2 : ∀ p, DifferentiableAt ℝ (fun p => partialDeriv γ (g β) p) p := fun p => diff_ContDiff_2 (g β) (hg β) γ p
  
  have h_sum1_eq : (fun p => partialDeriv β (fun p' => f γ p' + g γ p') p) = fun p => partialDeriv β (f γ) p + partialDeriv β (g γ) p := by
    ext p; exact partialDeriv_add_local _ _ β p (diff_ContDiff_1 (f γ) (hf γ) p) (diff_ContDiff_1 (g γ) (hg γ) p)
  have h_sum2_eq : (fun p => partialDeriv γ (fun p' => f β p' + g β p') p) = fun p => partialDeriv γ (f β) p + partialDeriv γ (g β) p := by
    ext p; exact partialDeriv_add_local _ _ γ p (diff_ContDiff_1 (f β) (hf β) p) (diff_ContDiff_1 (g β) (hg β) p)
    
  rw [h_sum1_eq, h_sum2_eq]
  
  rw [partialDeriv_add_local _ _ α x (h_diff_df1 x) (h_diff_dg1 x)]
  rw [partialDeriv_add_local _ _ α x (h_diff_df2 x) (h_diff_dg2 x)]

  have h_alg : (partialDeriv α (fun p => partialDeriv β (f γ) p) x + partialDeriv α (fun p => partialDeriv β (g γ) p) x -
                (partialDeriv α (fun p => partialDeriv γ (f β) p) x + partialDeriv α (fun p => partialDeriv γ (g β) p) x)) =
               (partialDeriv α (fun p => partialDeriv β (f γ) p) x - partialDeriv α (fun p => partialDeriv γ (f β) p) x) +
               (partialDeriv α (fun p => partialDeriv β (g γ) p) x - partialDeriv α (fun p => partialDeriv γ (g β) p) x) := by ring
               
  rw [h_alg, add_smul]

end CGD.Foundations

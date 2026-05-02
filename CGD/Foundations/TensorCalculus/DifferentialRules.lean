-- FILENAME: CGD/Foundations/TensorCalculus/DifferentialRules.lean

import Litlib.Y2003.nakahara2003geometry.Signature
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option linter.unusedVariables false

open Matrix Complex BigOperators Litlib.Y2003.nakahara2003geometry

namespace CGD.Foundations

/-- True geometric definition of the gauge covariant derivative of the field strength tensor: 
    D_α F_βγ = ∂_α F_βγ + [A_α, F_βγ] -/
noncomputable def covariantDeriv (A : Fin 4 → SpacetimePoint → SL2C) (alpha beta gamma : Fin 4) (x : SpacetimePoint) : SL2C :=
  let dF := partialDerivSl2c alpha (fun p => curvatureSl2c A beta gamma p) x
  let comm := ⁅A alpha x, curvatureSl2c A beta gamma x⁆
  dF + comm

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

lemma partialDerivMat_trace (f : SpacetimePoint → Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => f p i j) x) :
  Matrix.trace (partialDerivMat μ f x) = partialDeriv μ (fun p => Matrix.trace (f p)) x := by
  unfold partialDerivMat Matrix.trace
  exact (partialDeriv_sum (fun i p => f p i i) μ x (fun i => hf i i)).symm

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
  · intro k
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
  have h_eq : (fun p => (f p * g p) i j) = fun p => ∑ k : Fin 2, f p i k * g p k j := by
    ext p
    rfl
  rw [h_eq]
  apply diff_sum
  intro k
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

end CGD.Foundations

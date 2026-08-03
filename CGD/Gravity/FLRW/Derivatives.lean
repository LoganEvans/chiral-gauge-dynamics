-- FILENAME: CGD/Gravity/FLRW/Derivatives.lean

import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Gravity.Geometry
import CGD.Gravity.ExactSolutions.AlgebraicForms
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic

open CGD.Foundations CGD.Math Complex Matrix BigOperators

namespace CGD.Gravity.FLRW

/-- The exact FLRW matrix evaluator. -/
noncomputable def flrw_L (a : ℝ → ℂ) (μ : Fin 4) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  if μ = 0 then 0
  else if μ = 1 then a (x 0) • sigma1.val
  else if μ = 2 then a (x 0) • sigma2.val
  else if μ = 3 then a (x 0) • sigma3.val
  else 0

/-- The exact FLRW gauge field evaluator in SL2C. -/
noncomputable def flrw_A (a : ℝ → ℂ) (μ : Fin 4) (x : SpacetimePoint) : SL2C :=
  toSl2c (flrw_L a μ x)

lemma fin2_sum (f : Fin 2 → ℂ) : ∑ i : Fin 2, f i = f 0 + f 1 := by
  have eq : (Finset.univ : Finset (Fin 2)) = {0, 1} := rfl
  rw [eq]
  simp [Finset.sum_insert, Finset.sum_singleton]

lemma flrw_L_trace_zero (a : ℝ → ℂ) (μ : Fin 4) (x : SpacetimePoint) :
  Matrix.trace (flrw_L a μ x) = 0 := by
  unfold flrw_L
  split_ifs
  · unfold Matrix.trace Matrix.diag
    rw [fin2_sum]
    change (0 : ℂ) + 0 = 0
    ring
  · unfold Matrix.trace Matrix.diag
    rw [fin2_sum]
    have hs00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
    have hs11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [hs00, hs11]
    ring
  · unfold Matrix.trace Matrix.diag
    rw [fin2_sum]
    have hs00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
    have hs11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [hs00, hs11]
    ring
  · unfold Matrix.trace Matrix.diag
    rw [fin2_sum]
    have hs00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
    have hs11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [hs00, hs11]
    ring
  · unfold Matrix.trace Matrix.diag
    rw [fin2_sum]
    change (0 : ℂ) + 0 = 0
    ring

lemma flrw_A_val_eq (a : ℝ → ℂ) (μ : Fin 4) (x : SpacetimePoint) :
  (flrw_A a μ x).val = flrw_L a μ x := by
  unfold flrw_A
  have h_tr := flrw_L_trace_zero a μ x
  rw [toSl2c_val_eq _ h_tr]

/--
Spatial derivatives of purely time-dependent isotropic functions strictly evaluate to zero.
This is the foundational analytic step for establishing the F_jk magnetic terms in the FLRW vacuum.
-/
lemma partialDeriv_time_dep_spatial
  (f : ℝ → ℂ) (k : Fin 4) (x : SpacetimePoint) (hk : k ≠ 0)
  (hf : DifferentiableAt ℝ f (x 0)) :
  partialDeriv k (fun p => f (p 0)) x = 0 := by
  unfold partialDeriv
  have h_comp : (fun (p : SpacetimePoint) => f (p 0)) = f ∘ (fun p => p 0) := rfl
  rw [h_comp]

  let proj0 : SpacetimePoint →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have h_proj_eq : (fun p : SpacetimePoint => p 0) = proj0 := rfl
  rw [h_proj_eq]

  have h_proj_diff : DifferentiableAt ℝ proj0 x := proj0.differentiableAt
  rw [fderiv_comp x hf h_proj_diff]

  simp only [ContinuousLinearMap.comp_apply]

  have h_fderiv_proj : fderiv ℝ proj0 x = proj0 := proj0.fderiv
  rw [h_fderiv_proj]

  have h_single : proj0 ((Pi.single k (1 : ℝ) : Fin 4 → ℝ)) = 0 := by
    change (Pi.single k (1 : ℝ) : Fin 4 → ℝ) 0 = 0
    simp [Pi.single, Function.update, hk.symm]
  rw [h_single]

  exact ContinuousLinearMap.map_zero (fderiv ℝ f (x 0))

/--
Temporal derivatives of time-dependent isotropic functions strictly evaluate to the 1D chain rule derivative.
-/
lemma partialDeriv_time_dep_time
  (f : ℝ → ℂ) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f (x 0)) :
  partialDeriv 0 (fun p => f (p 0)) x = fderiv ℝ f (x 0) 1 := by
  unfold partialDeriv
  have h_comp : (fun (p : SpacetimePoint) => f (p 0)) = f ∘ (fun p => p 0) := rfl
  rw [h_comp]

  let proj0 : SpacetimePoint →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have h_proj_eq : (fun p : SpacetimePoint => p 0) = proj0 := rfl
  rw [h_proj_eq]

  have h_proj_diff : DifferentiableAt ℝ proj0 x := proj0.differentiableAt
  rw [fderiv_comp x hf h_proj_diff]

  simp only [ContinuousLinearMap.comp_apply]

  have h_fderiv_proj : fderiv ℝ proj0 x = proj0 := proj0.fderiv
  rw [h_fderiv_proj]

  have h_single : proj0 ((Pi.single 0 (1 : ℝ) : Fin 4 → ℝ)) = 1 := by
    change (Pi.single 0 (1 : ℝ) : Fin 4 → ℝ) 0 = 1
    simp [Pi.single, Function.update]
  rw [h_single]

  have h_eval : proj0 x = x 0 := rfl
  rw [h_eval]

/--
Proves that the coordinate-projected time function remains differentiable on the 4D manifold.
-/
lemma diff_time_dep (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  DifferentiableAt ℝ (fun p => a (p 0)) x := by
  let proj0 : SpacetimePoint →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have h_comp : (fun (p : SpacetimePoint) => a (p 0)) = a ∘ proj0 := by
    ext p
    rfl
  rw [h_comp]
  have h_proj_diff : DifferentiableAt ℝ proj0 x := proj0.differentiableAt
  exact DifferentiableAt.comp x ha h_proj_diff

/-- Evaluates the temporal partial derivative of the mu=1 FLRW connection matrix. -/
lemma partialDerivMat_flrw_L_0_1 (a : ℝ → ℂ) (x : SpacetimePoint)
  (ha : DifferentiableAt ℝ a (x 0)) :
  partialDerivMat 0 (fun p => flrw_L a 1 p) x = (fderiv ℝ a (x 0) 1) • sigma1.val := by
  ext i j
  unfold partialDerivMat
  have h_eq : (fun p => flrw_L a 1 p i j) = fun p => sigma1.val i j * a (p 0) := by
    ext p
    have h_eval : flrw_L a 1 p = a (p 0) • sigma1.val := by
      unfold flrw_L
      simp
    rw [h_eval]
    change a (p 0) * sigma1.val i j = sigma1.val i j * a (p 0)
    ring
  rw [h_eq]
  have hd := diff_time_dep a x ha
  rw [partialDeriv_const_smul (sigma1.val i j) (fun p => a (p 0)) 0 x hd]
  rw [partialDeriv_time_dep_time a x ha]
  change sigma1.val i j * fderiv ℝ a (x 0) 1 = fderiv ℝ a (x 0) 1 * sigma1.val i j
  ring

/-- Evaluates the spatial partial derivative of the mu=1 FLRW connection matrix. -/
lemma partialDerivMat_flrw_L_k_1 (a : ℝ → ℂ) (k : Fin 4) (x : SpacetimePoint)
  (hk : k ≠ 0) (ha : DifferentiableAt ℝ a (x 0)) :
  partialDerivMat k (fun p => flrw_L a 1 p) x = 0 := by
  ext i j
  unfold partialDerivMat
  have h_eq : (fun p => flrw_L a 1 p i j) = fun p => sigma1.val i j * a (p 0) := by
    ext p
    have h_eval : flrw_L a 1 p = a (p 0) • sigma1.val := by
      unfold flrw_L
      simp
    rw [h_eval]
    change a (p 0) * sigma1.val i j = sigma1.val i j * a (p 0)
    ring
  rw [h_eq]
  have hd := diff_time_dep a x ha
  rw [partialDeriv_const_smul (sigma1.val i j) (fun p => a (p 0)) k x hd]
  rw [partialDeriv_time_dep_spatial a k x hk ha]
  change sigma1.val i j * 0 = 0
  ring

/-- Evaluates the temporal partial derivative of the mu=2 FLRW connection matrix. -/
lemma partialDerivMat_flrw_L_0_2 (a : ℝ → ℂ) (x : SpacetimePoint)
  (ha : DifferentiableAt ℝ a (x 0)) :
  partialDerivMat 0 (fun p => flrw_L a 2 p) x = (fderiv ℝ a (x 0) 1) • sigma2.val := by
  ext i j
  unfold partialDerivMat
  have h_eq : (fun p => flrw_L a 2 p i j) = fun p => sigma2.val i j * a (p 0) := by
    ext p
    have h_eval : flrw_L a 2 p = a (p 0) • sigma2.val := by
      unfold flrw_L
      simp
    rw [h_eval]
    change a (p 0) * sigma2.val i j = sigma2.val i j * a (p 0)
    ring
  rw [h_eq]
  have hd := diff_time_dep a x ha
  rw [partialDeriv_const_smul (sigma2.val i j) (fun p => a (p 0)) 0 x hd]
  rw [partialDeriv_time_dep_time a x ha]
  change sigma2.val i j * fderiv ℝ a (x 0) 1 = fderiv ℝ a (x 0) 1 * sigma2.val i j
  ring

/-- Evaluates the spatial partial derivative of the mu=2 FLRW connection matrix. -/
lemma partialDerivMat_flrw_L_k_2 (a : ℝ → ℂ) (k : Fin 4) (x : SpacetimePoint)
  (hk : k ≠ 0) (ha : DifferentiableAt ℝ a (x 0)) :
  partialDerivMat k (fun p => flrw_L a 2 p) x = 0 := by
  ext i j
  unfold partialDerivMat
  have h_eq : (fun p => flrw_L a 2 p i j) = fun p => sigma2.val i j * a (p 0) := by
    ext p
    have h_eval : flrw_L a 2 p = a (p 0) • sigma2.val := by
      unfold flrw_L
      simp
    rw [h_eval]
    change a (p 0) * sigma2.val i j = sigma2.val i j * a (p 0)
    ring
  rw [h_eq]
  have hd := diff_time_dep a x ha
  rw [partialDeriv_const_smul (sigma2.val i j) (fun p => a (p 0)) k x hd]
  rw [partialDeriv_time_dep_spatial a k x hk ha]
  change sigma2.val i j * 0 = 0
  ring

/-- Evaluates the temporal partial derivative of the mu=3 FLRW connection matrix. -/
lemma partialDerivMat_flrw_L_0_3 (a : ℝ → ℂ) (x : SpacetimePoint)
  (ha : DifferentiableAt ℝ a (x 0)) :
  partialDerivMat 0 (fun p => flrw_L a 3 p) x = (fderiv ℝ a (x 0) 1) • sigma3.val := by
  ext i j
  unfold partialDerivMat
  have h_eq : (fun p => flrw_L a 3 p i j) = fun p => sigma3.val i j * a (p 0) := by
    ext p
    have h_eval : flrw_L a 3 p = a (p 0) • sigma3.val := by
      unfold flrw_L
      simp
    rw [h_eval]
    change a (p 0) * sigma3.val i j = sigma3.val i j * a (p 0)
    ring
  rw [h_eq]
  have hd := diff_time_dep a x ha
  rw [partialDeriv_const_smul (sigma3.val i j) (fun p => a (p 0)) 0 x hd]
  rw [partialDeriv_time_dep_time a x ha]
  change sigma3.val i j * fderiv ℝ a (x 0) 1 = fderiv ℝ a (x 0) 1 * sigma3.val i j
  ring

/-- Evaluates the spatial partial derivative of the mu=3 FLRW connection matrix. -/
lemma partialDerivMat_flrw_L_k_3 (a : ℝ → ℂ) (k : Fin 4) (x : SpacetimePoint)
  (hk : k ≠ 0) (ha : DifferentiableAt ℝ a (x 0)) :
  partialDerivMat k (fun p => flrw_L a 3 p) x = 0 := by
  ext i j
  unfold partialDerivMat
  have h_eq : (fun p => flrw_L a 3 p i j) = fun p => sigma3.val i j * a (p 0) := by
    ext p
    have h_eval : flrw_L a 3 p = a (p 0) • sigma3.val := by
      unfold flrw_L
      simp
    rw [h_eval]
    change a (p 0) * sigma3.val i j = sigma3.val i j * a (p 0)
    ring
  rw [h_eq]
  have hd := diff_time_dep a x ha
  rw [partialDeriv_const_smul (sigma3.val i j) (fun p => a (p 0)) k x hd]
  rw [partialDeriv_time_dep_spatial a k x hk ha]
  change sigma3.val i j * 0 = 0
  ring

/-- The temporal component of the FLRW connection is identically zero in the Weyl gauge. -/
lemma flrw_L_0_eq (a : ℝ → ℂ) (x : SpacetimePoint) :
  flrw_L a 0 x = 0 := by
  unfold flrw_L
  simp

/-- The partial derivatives of the temporal component of the FLRW connection are identically zero. -/
lemma partialDerivMat_flrw_L_k_0 (a : ℝ → ℂ) (k : Fin 4) (x : SpacetimePoint) :
  partialDerivMat k (fun p => flrw_L a 0 p) x = 0 := by
  have h_direct : (fun p => flrw_L a 0 p) = fun _ => 0 := funext (fun p => flrw_L_0_eq a p)
  rw [h_direct]
  exact partialDerivMat_const 0 k x

/--
Proves that the internal elements of the FLRW matrix field are everywhere differentiable,
satisfying the prerequisite for invoking the rigorous curvature matrix evaluation theorem.
-/
lemma flrw_A_differentiable (a : ℝ → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (ha : DifferentiableAt ℝ a (x 0)) :
  ∀ i j, DifferentiableAt ℝ (fun p => (flrw_A a μ p).val i j) x := by
  intros i j
  have h_eq : (fun p => (flrw_A a μ p).val i j) = fun p => flrw_L a μ p i j := by
    ext p
    rw [flrw_A_val_eq]
  rw [h_eq]
  unfold flrw_L
  split_ifs
  · exact differentiableAt_const 0
  · have h_smul : (fun (p : SpacetimePoint) => (a (p 0) • sigma1.val) i j) = fun (p : SpacetimePoint) => sigma1.val i j * a (p 0) := by
      ext p
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    rw [h_smul]
    exact DifferentiableAt.const_mul (diff_time_dep a x ha) (sigma1.val i j)
  · have h_smul : (fun (p : SpacetimePoint) => (a (p 0) • sigma2.val) i j) = fun (p : SpacetimePoint) => sigma2.val i j * a (p 0) := by
      ext p
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    rw [h_smul]
    exact DifferentiableAt.const_mul (diff_time_dep a x ha) (sigma2.val i j)
  · have h_smul : (fun (p : SpacetimePoint) => (a (p 0) • sigma3.val) i j) = fun (p : SpacetimePoint) => sigma3.val i j * a (p 0) := by
      ext p
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    rw [h_smul]
    exact DifferentiableAt.const_mul (diff_time_dep a x ha) (sigma3.val i j)
  · exact differentiableAt_const 0

end CGD.Gravity.FLRW

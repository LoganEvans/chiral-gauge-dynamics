-- FILENAME: CGD/Gravity/ExactSolutions/FLRW.lean

import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Gravity.Geometry
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import CGD.Gravity.ExactSolutions.Definitions
import CGD.Gravity.ExactSolutions.AlgebraicForms

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

open CGD.Axioms CGD.Foundations CGD.Math Complex Matrix CGD.Gravity BigOperators

set_option linter.unreachableTactic false

namespace CGD.Gravity.ExactSolutions

/-!
# FLRW (Isotropic) Reality Filter

This file acts as the stable aggregator for the FLRW (formerly "Type O" isotropic) proofs.
The complete kinematic reality filter theorem is located at the bottom of the file:
`flrwSatisfiesReality`
-/

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

/-- Evaluates the [A_1, A_2] commutator, establishing the F_12 magnetic field component. -/
lemma flrw_L_comm_1_2 (a : ℝ → ℂ) (x : SpacetimePoint) :
  flrw_L a 1 x * flrw_L a 2 x - flrw_L a 2 x * flrw_L a 1 x = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val := by
  have h1 : flrw_L a 1 x = a (x 0) • sigma1.val := by unfold flrw_L; simp
  have h2 : flrw_L a 2 x = a (x 0) • sigma2.val := by unfold flrw_L; simp
  rw [h1, h2]
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
  fin_cases i <;> fin_cases j
  · change a (x 0) * sigma1.val 0 0 * (a (x 0) * sigma2.val 0 0) + a (x 0) * sigma1.val 0 1 * (a (x 0) * sigma2.val 1 0) - (a (x 0) * sigma2.val 0 0 * (a (x 0) * sigma1.val 0 0) + a (x 0) * sigma2.val 0 1 * (a (x 0) * sigma1.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma3.val 0 0
    simp only [hs1_00, hs1_01, hs1_10, hs2_00, hs2_01, hs2_10, hs3_00]
    ring
  · change a (x 0) * sigma1.val 0 0 * (a (x 0) * sigma2.val 0 1) + a (x 0) * sigma1.val 0 1 * (a (x 0) * sigma2.val 1 1) - (a (x 0) * sigma2.val 0 0 * (a (x 0) * sigma1.val 0 1) + a (x 0) * sigma2.val 0 1 * (a (x 0) * sigma1.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma3.val 0 1
    simp only [hs1_00, hs1_01, hs1_11, hs2_00, hs2_01, hs2_11, hs3_01]
    ring
  · change a (x 0) * sigma1.val 1 0 * (a (x 0) * sigma2.val 0 0) + a (x 0) * sigma1.val 1 1 * (a (x 0) * sigma2.val 1 0) - (a (x 0) * sigma2.val 1 0 * (a (x 0) * sigma1.val 0 0) + a (x 0) * sigma2.val 1 1 * (a (x 0) * sigma1.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma3.val 1 0
    simp only [hs1_00, hs1_10, hs1_11, hs2_00, hs2_10, hs2_11, hs3_10]
    ring
  · change a (x 0) * sigma1.val 1 0 * (a (x 0) * sigma2.val 0 1) + a (x 0) * sigma1.val 1 1 * (a (x 0) * sigma2.val 1 1) - (a (x 0) * sigma2.val 1 0 * (a (x 0) * sigma1.val 0 1) + a (x 0) * sigma2.val 1 1 * (a (x 0) * sigma1.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma3.val 1 1
    simp only [hs1_01, hs1_10, hs1_11, hs2_01, hs2_10, hs2_11, hs3_11]
    ring

/-- Evaluates the [A_2, A_3] commutator, establishing the F_23 magnetic field component. -/
lemma flrw_L_comm_2_3 (a : ℝ → ℂ) (x : SpacetimePoint) :
  flrw_L a 2 x * flrw_L a 3 x - flrw_L a 3 x * flrw_L a 2 x = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val := by
  have h2 : flrw_L a 2 x = a (x 0) • sigma2.val := by unfold flrw_L; simp
  have h3 : flrw_L a 3 x = a (x 0) • sigma3.val := by unfold flrw_L; simp
  rw [h2, h3]
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
  fin_cases i <;> fin_cases j
  · change a (x 0) * sigma2.val 0 0 * (a (x 0) * sigma3.val 0 0) + a (x 0) * sigma2.val 0 1 * (a (x 0) * sigma3.val 1 0) - (a (x 0) * sigma3.val 0 0 * (a (x 0) * sigma2.val 0 0) + a (x 0) * sigma3.val 0 1 * (a (x 0) * sigma2.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma1.val 0 0
    simp only [hs1_00, hs2_00, hs2_01, hs2_10, hs3_00, hs3_01, hs3_10]
    ring
  · change a (x 0) * sigma2.val 0 0 * (a (x 0) * sigma3.val 0 1) + a (x 0) * sigma2.val 0 1 * (a (x 0) * sigma3.val 1 1) - (a (x 0) * sigma3.val 0 0 * (a (x 0) * sigma2.val 0 1) + a (x 0) * sigma3.val 0 1 * (a (x 0) * sigma2.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma1.val 0 1
    simp only [hs1_01, hs2_00, hs2_01, hs2_11, hs3_00, hs3_01, hs3_11]
    ring
  · change a (x 0) * sigma2.val 1 0 * (a (x 0) * sigma3.val 0 0) + a (x 0) * sigma2.val 1 1 * (a (x 0) * sigma3.val 1 0) - (a (x 0) * sigma3.val 1 0 * (a (x 0) * sigma2.val 0 0) + a (x 0) * sigma3.val 1 1 * (a (x 0) * sigma2.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma1.val 1 0
    simp only [hs1_10, hs2_00, hs2_10, hs2_11, hs3_00, hs3_10, hs3_11]
    ring
  · change a (x 0) * sigma2.val 1 0 * (a (x 0) * sigma3.val 0 1) + a (x 0) * sigma2.val 1 1 * (a (x 0) * sigma3.val 1 1) - (a (x 0) * sigma3.val 1 0 * (a (x 0) * sigma2.val 0 1) + a (x 0) * sigma3.val 1 1 * (a (x 0) * sigma2.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma1.val 1 1
    simp only [hs1_11, hs2_01, hs2_10, hs2_11, hs3_01, hs3_10, hs3_11]
    ring

/-- Evaluates the [A_3, A_1] commutator, establishing the F_31 magnetic field component. -/
lemma flrw_L_comm_3_1 (a : ℝ → ℂ) (x : SpacetimePoint) :
  flrw_L a 3 x * flrw_L a 1 x - flrw_L a 1 x * flrw_L a 3 x = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val := by
  have h3 : flrw_L a 3 x = a (x 0) • sigma3.val := by unfold flrw_L; simp
  have h1 : flrw_L a 1 x = a (x 0) • sigma1.val := by unfold flrw_L; simp
  rw [h3, h1]
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases i <;> fin_cases j
  · change a (x 0) * sigma3.val 0 0 * (a (x 0) * sigma1.val 0 0) + a (x 0) * sigma3.val 0 1 * (a (x 0) * sigma1.val 1 0) - (a (x 0) * sigma1.val 0 0 * (a (x 0) * sigma3.val 0 0) + a (x 0) * sigma1.val 0 1 * (a (x 0) * sigma3.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma2.val 0 0
    simp only [hs1_00, hs1_01, hs1_10, hs2_00, hs3_00, hs3_01, hs3_10]
    ring
  · change a (x 0) * sigma3.val 0 0 * (a (x 0) * sigma1.val 0 1) + a (x 0) * sigma3.val 0 1 * (a (x 0) * sigma1.val 1 1) - (a (x 0) * sigma1.val 0 0 * (a (x 0) * sigma3.val 0 1) + a (x 0) * sigma1.val 0 1 * (a (x 0) * sigma3.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma2.val 0 1
    simp only [hs1_00, hs1_01, hs1_11, hs2_01, hs3_00, hs3_01, hs3_11]
    -- Apply the scalar Pauli reduction, then explicitly substitute I^2 via rw, then close with ring
    have h_eq : a (x 0) * 1 * (a (x 0) * 1) + a (x 0) * 0 * (a (x 0) * 0) - (a (x 0) * 0 * (a (x 0) * 0) + a (x 0) * 1 * (a (x 0) * -1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * -Complex.I := by
      calc
        a (x 0) * 1 * (a (x 0) * 1) + a (x 0) * 0 * (a (x 0) * 0) - (a (x 0) * 0 * (a (x 0) * 0) + a (x 0) * 1 * (a (x 0) * -1))
        _ = 2 * (a (x 0) * a (x 0)) := by ring
        _ = 2 * (a (x 0) * a (x 0)) * -(-1) := by ring
        _ = 2 * (a (x 0) * a (x 0)) * -(Complex.I ^ 2) := by rw [hI]
        _ = 2 * Complex.I * (a (x 0) * a (x 0)) * -Complex.I := by ring
    exact h_eq
  · change a (x 0) * sigma3.val 1 0 * (a (x 0) * sigma1.val 0 0) + a (x 0) * sigma3.val 1 1 * (a (x 0) * sigma1.val 1 0) - (a (x 0) * sigma1.val 1 0 * (a (x 0) * sigma3.val 0 0) + a (x 0) * sigma1.val 1 1 * (a (x 0) * sigma3.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma2.val 1 0
    simp only [hs1_00, hs1_10, hs1_11, hs2_10, hs3_00, hs3_10, hs3_11]
    have h_eq : a (x 0) * 0 * (a (x 0) * 0) + a (x 0) * -1 * (a (x 0) * 1) - (a (x 0) * 1 * (a (x 0) * 1) + a (x 0) * 0 * (a (x 0) * 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * Complex.I := by
      calc
        a (x 0) * 0 * (a (x 0) * 0) + a (x 0) * -1 * (a (x 0) * 1) - (a (x 0) * 1 * (a (x 0) * 1) + a (x 0) * 0 * (a (x 0) * 0))
        _ = -2 * (a (x 0) * a (x 0)) := by ring
        _ = 2 * (a (x 0) * a (x 0)) * (-1) := by ring
        _ = 2 * (a (x 0) * a (x 0)) * (Complex.I ^ 2) := by rw [hI]
        _ = 2 * Complex.I * (a (x 0) * a (x 0)) * Complex.I := by ring
    exact h_eq
  · change a (x 0) * sigma3.val 1 0 * (a (x 0) * sigma1.val 0 1) + a (x 0) * sigma3.val 1 1 * (a (x 0) * sigma1.val 1 1) - (a (x 0) * sigma1.val 1 0 * (a (x 0) * sigma3.val 0 1) + a (x 0) * sigma1.val 1 1 * (a (x 0) * sigma3.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma2.val 1 1
    simp only [hs1_01, hs1_10, hs1_11, hs2_11, hs3_01, hs3_10, hs3_11]
    ring

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

/-- The F_01 component of the FLRW curvature evaluates strictly to \dot{a} sigma_x. -/
lemma flrw_F_0_1 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (flrw_A a) 0 1 x).val = (fderiv ℝ a (x 0) 1) • sigma1.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (flrw_A a) 0 1 x (flrw_A_differentiable a 0 x ha) (flrw_A_differentiable a 1 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 0 (fun p => (flrw_A a 1 p).val i j) x = (fderiv ℝ a (x 0) 1 * sigma1.val i j) := by
    have h_mat := partialDerivMat_flrw_L_0_1 a x ha
    have h_eq : (fun p => (flrw_A a 1 p).val i j) = fun p => flrw_L a 1 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 0 (fun p => flrw_L a 1 p i j) x = partialDerivMat 0 (fun p => flrw_L a 1 p) x i j := rfl
    rw [h_eval, h_mat]
    simp only [Matrix.smul_apply, smul_eq_mul]
  have hd1 : partialDeriv 1 (fun p => (flrw_A a 0 p).val i j) x = 0 := by
    have h_mat := partialDerivMat_flrw_L_k_0 a 1 x
    have h_eq : (fun p => (flrw_A a 0 p).val i j) = fun p => flrw_L a 0 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 1 (fun p => flrw_L a 0 p i j) x = partialDerivMat 1 (fun p => flrw_L a 0 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((flrw_A a 0 x).val * (flrw_A a 1 x).val - (flrw_A a 1 x).val * (flrw_A a 0 x).val) i j = 0 := by
    have h0 : (flrw_A a 0 x).val = 0 := by rw [flrw_A_val_eq, flrw_L_0_eq]
    rw [h0]
    simp
  rw [hd0, hd1, h_comm]
  simp only [Matrix.smul_apply, smul_eq_mul, add_zero, sub_zero]

/-- The F_02 component of the FLRW curvature evaluates strictly to \dot{a} sigma_y. -/
lemma flrw_F_0_2 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (flrw_A a) 0 2 x).val = (fderiv ℝ a (x 0) 1) • sigma2.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (flrw_A a) 0 2 x (flrw_A_differentiable a 0 x ha) (flrw_A_differentiable a 2 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 0 (fun p => (flrw_A a 2 p).val i j) x = (fderiv ℝ a (x 0) 1 * sigma2.val i j) := by
    have h_mat := partialDerivMat_flrw_L_0_2 a x ha
    have h_eq : (fun p => (flrw_A a 2 p).val i j) = fun p => flrw_L a 2 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 0 (fun p => flrw_L a 2 p i j) x = partialDerivMat 0 (fun p => flrw_L a 2 p) x i j := rfl
    rw [h_eval, h_mat]
    simp only [Matrix.smul_apply, smul_eq_mul]
  have hd1 : partialDeriv 2 (fun p => (flrw_A a 0 p).val i j) x = 0 := by
    have h_mat := partialDerivMat_flrw_L_k_0 a 2 x
    have h_eq : (fun p => (flrw_A a 0 p).val i j) = fun p => flrw_L a 0 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 2 (fun p => flrw_L a 0 p i j) x = partialDerivMat 2 (fun p => flrw_L a 0 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((flrw_A a 0 x).val * (flrw_A a 2 x).val - (flrw_A a 2 x).val * (flrw_A a 0 x).val) i j = 0 := by
    have h0 : (flrw_A a 0 x).val = 0 := by rw [flrw_A_val_eq, flrw_L_0_eq]
    rw [h0]
    simp
  rw [hd0, hd1, h_comm]
  simp only [Matrix.smul_apply, smul_eq_mul, add_zero, sub_zero]

/-- The F_03 component of the FLRW curvature evaluates strictly to \dot{a} sigma_z. -/
lemma flrw_F_0_3 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (flrw_A a) 0 3 x).val = (fderiv ℝ a (x 0) 1) • sigma3.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (flrw_A a) 0 3 x (flrw_A_differentiable a 0 x ha) (flrw_A_differentiable a 3 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 0 (fun p => (flrw_A a 3 p).val i j) x = (fderiv ℝ a (x 0) 1 * sigma3.val i j) := by
    have h_mat := partialDerivMat_flrw_L_0_3 a x ha
    have h_eq : (fun p => (flrw_A a 3 p).val i j) = fun p => flrw_L a 3 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 0 (fun p => flrw_L a 3 p i j) x = partialDerivMat 0 (fun p => flrw_L a 3 p) x i j := rfl
    rw [h_eval, h_mat]
    simp only [Matrix.smul_apply, smul_eq_mul]
  have hd1 : partialDeriv 3 (fun p => (flrw_A a 0 p).val i j) x = 0 := by
    have h_mat := partialDerivMat_flrw_L_k_0 a 3 x
    have h_eq : (fun p => (flrw_A a 0 p).val i j) = fun p => flrw_L a 0 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 3 (fun p => flrw_L a 0 p i j) x = partialDerivMat 3 (fun p => flrw_L a 0 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((flrw_A a 0 x).val * (flrw_A a 3 x).val - (flrw_A a 3 x).val * (flrw_A a 0 x).val) i j = 0 := by
    have h0 : (flrw_A a 0 x).val = 0 := by rw [flrw_A_val_eq, flrw_L_0_eq]
    rw [h0]
    simp
  rw [hd0, hd1, h_comm]
  simp only [Matrix.smul_apply, smul_eq_mul, add_zero, sub_zero]

/-- The F_12 component of the FLRW curvature evaluates strictly to the [A_1, A_2] commutator. -/
lemma flrw_F_1_2 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (flrw_A a) 1 2 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (flrw_A a) 1 2 x (flrw_A_differentiable a 1 x ha) (flrw_A_differentiable a 2 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 1 (fun p => (flrw_A a 2 p).val i j) x = 0 := by
    have hk : (1 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_flrw_L_k_2 a 1 x hk ha
    have h_eq : (fun p => (flrw_A a 2 p).val i j) = fun p => flrw_L a 2 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 1 (fun p => flrw_L a 2 p i j) x = partialDerivMat 1 (fun p => flrw_L a 2 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have hd1 : partialDeriv 2 (fun p => (flrw_A a 1 p).val i j) x = 0 := by
    have hk : (2 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_flrw_L_k_1 a 2 x hk ha
    have h_eq : (fun p => (flrw_A a 1 p).val i j) = fun p => flrw_L a 1 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 2 (fun p => flrw_L a 1 p i j) x = partialDerivMat 2 (fun p => flrw_L a 1 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((flrw_A a 1 x).val * (flrw_A a 2 x).val - (flrw_A a 2 x).val * (flrw_A a 1 x).val) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val) i j := by
    have h1 : (flrw_A a 1 x).val = flrw_L a 1 x := flrw_A_val_eq a 1 x
    have h2 : (flrw_A a 2 x).val = flrw_L a 2 x := flrw_A_val_eq a 2 x
    rw [h1, h2]
    have h_comm_mat := flrw_L_comm_1_2 a x
    have h_eval : (flrw_L a 1 x * flrw_L a 2 x - flrw_L a 2 x * flrw_L a 1 x) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val) i j := by rw [h_comm_mat]
    exact h_eval
  rw [hd0, hd1, h_comm]
  simp only [sub_zero, zero_add]

/-- The F_23 component of the FLRW curvature evaluates strictly to the [A_2, A_3] commutator. -/
lemma flrw_F_2_3 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (flrw_A a) 2 3 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (flrw_A a) 2 3 x (flrw_A_differentiable a 2 x ha) (flrw_A_differentiable a 3 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 2 (fun p => (flrw_A a 3 p).val i j) x = 0 := by
    have hk : (2 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_flrw_L_k_3 a 2 x hk ha
    have h_eq : (fun p => (flrw_A a 3 p).val i j) = fun p => flrw_L a 3 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 2 (fun p => flrw_L a 3 p i j) x = partialDerivMat 2 (fun p => flrw_L a 3 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have hd1 : partialDeriv 3 (fun p => (flrw_A a 2 p).val i j) x = 0 := by
    have hk : (3 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_flrw_L_k_2 a 3 x hk ha
    have h_eq : (fun p => (flrw_A a 2 p).val i j) = fun p => flrw_L a 2 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 3 (fun p => flrw_L a 2 p i j) x = partialDerivMat 3 (fun p => flrw_L a 2 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((flrw_A a 2 x).val * (flrw_A a 3 x).val - (flrw_A a 3 x).val * (flrw_A a 2 x).val) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val) i j := by
    have h2 : (flrw_A a 2 x).val = flrw_L a 2 x := flrw_A_val_eq a 2 x
    have h3 : (flrw_A a 3 x).val = flrw_L a 3 x := flrw_A_val_eq a 3 x
    rw [h2, h3]
    have h_comm_mat := flrw_L_comm_2_3 a x
    have h_eval : (flrw_L a 2 x * flrw_L a 3 x - flrw_L a 3 x * flrw_L a 2 x) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val) i j := by rw [h_comm_mat]
    exact h_eval
  rw [hd0, hd1, h_comm]
  simp only [sub_zero, zero_add]

/-- The F_31 component of the FLRW curvature evaluates strictly to the [A_3, A_1] commutator. -/
lemma flrw_F_3_1 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (curvatureSl2c (flrw_A a) 3 1 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val := by
  ext i j
  have hc := curvatureSl2c_val_eq (flrw_A a) 3 1 x (flrw_A_differentiable a 3 x ha) (flrw_A_differentiable a 1 x ha) i j
  rw [hc]
  have hd0 : partialDeriv 3 (fun p => (flrw_A a 1 p).val i j) x = 0 := by
    have hk : (3 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_flrw_L_k_1 a 3 x hk ha
    have h_eq : (fun p => (flrw_A a 1 p).val i j) = fun p => flrw_L a 1 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 3 (fun p => flrw_L a 1 p i j) x = partialDerivMat 3 (fun p => flrw_L a 1 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have hd1 : partialDeriv 1 (fun p => (flrw_A a 3 p).val i j) x = 0 := by
    have hk : (1 : Fin 4) ≠ 0 := by decide
    have h_mat := partialDerivMat_flrw_L_k_3 a 1 x hk ha
    have h_eq : (fun p => (flrw_A a 3 p).val i j) = fun p => flrw_L a 3 p i j := by ext p; rw [flrw_A_val_eq]
    rw [h_eq]
    have h_eval : partialDeriv 1 (fun p => flrw_L a 3 p i j) x = partialDerivMat 1 (fun p => flrw_L a 3 p) x i j := rfl
    rw [h_eval, h_mat]
    rfl
  have h_comm : ((flrw_A a 3 x).val * (flrw_A a 1 x).val - (flrw_A a 1 x).val * (flrw_A a 3 x).val) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val) i j := by
    have h3 : (flrw_A a 3 x).val = flrw_L a 3 x := flrw_A_val_eq a 3 x
    have h1 : (flrw_A a 1 x).val = flrw_L a 1 x := flrw_A_val_eq a 1 x
    rw [h3, h1]
    have h_comm_mat := flrw_L_comm_3_1 a x
    have h_eval : (flrw_L a 3 x * flrw_L a 1 x - flrw_L a 1 x * flrw_L a 3 x) i j = ((2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val) i j := by rw [h_comm_mat]
    exact h_eval
  rw [hd0, hd1, h_comm]
  simp only [sub_zero, zero_add]

/-- Extracts the a=0 adjoint projection from the F_01 curvature matrix. Evaluates to \dot{a}. -/
lemma flrw_project_0_0_1 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 0 0 1 = fderiv ℝ a (x 0) 1 := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (flrw_A a) 0 1 x).val = (fderiv ℝ a (x 0) 1) • sigma1.val := flrw_F_0_1 a x ha
  rw [hF]
  rw [fin2_sum]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  simp only [hs1_00, hs1_01, hs1_10, hs1_11]
  have h_eq : (0.5 : ℂ) * (
    (fderiv ℝ a (x 0) 1 * 0 * 0 + fderiv ℝ a (x 0) 1 * 1 * 1) +
    (fderiv ℝ a (x 0) 1 * 1 * 1 + fderiv ℝ a (x 0) 1 * 0 * 0)
  ) = fderiv ℝ a (x 0) 1 := by ring
  exact h_eq

/-- Extracts the a=1 adjoint projection from the F_02 curvature matrix. Evaluates to \dot{a}. -/
lemma flrw_project_1_0_2 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 1 0 2 = fderiv ℝ a (x 0) 1 := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (flrw_A a) 0 2 x).val = (fderiv ℝ a (x 0) 1) • sigma2.val := flrw_F_0_2 a x ha
  rw [hF]
  rw [fin2_sum]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  simp only [hs2_00, hs2_01, hs2_10, hs2_11]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h_eq : (0.5 : ℂ) * (
    (fderiv ℝ a (x 0) 1 * 0 * 0 + fderiv ℝ a (x 0) 1 * -Complex.I * Complex.I) +
    (fderiv ℝ a (x 0) 1 * Complex.I * -Complex.I + fderiv ℝ a (x 0) 1 * 0 * 0)
  ) = fderiv ℝ a (x 0) 1 := by
    calc (0.5 : ℂ) * ( (fderiv ℝ a (x 0) 1 * 0 * 0 + fderiv ℝ a (x 0) 1 * -Complex.I * Complex.I) + (fderiv ℝ a (x 0) 1 * Complex.I * -Complex.I + fderiv ℝ a (x 0) 1 * 0 * 0) )
      _ = (0.5 : ℂ) * ( - fderiv ℝ a (x 0) 1 * (Complex.I * Complex.I) - fderiv ℝ a (x 0) 1 * (Complex.I * Complex.I) ) := by ring
      _ = (0.5 : ℂ) * ( - fderiv ℝ a (x 0) 1 * (-1) - fderiv ℝ a (x 0) 1 * (-1) ) := by rw [hI]
      _ = fderiv ℝ a (x 0) 1 := by ring
  exact h_eq

/-- Extracts the a=2 adjoint projection from the F_03 curvature matrix. Evaluates to \dot{a}. -/
lemma flrw_project_2_0_3 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 2 0 3 = fderiv ℝ a (x 0) 1 := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (flrw_A a) 0 3 x).val = (fderiv ℝ a (x 0) 1) • sigma3.val := flrw_F_0_3 a x ha
  rw [hF]
  rw [fin2_sum]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
  simp only [hs3_00, hs3_01, hs3_10, hs3_11]
  have h_eq : (0.5 : ℂ) * (
    (fderiv ℝ a (x 0) 1 * 1 * 1 + fderiv ℝ a (x 0) 1 * 0 * 0) +
    (fderiv ℝ a (x 0) 1 * 0 * 0 + fderiv ℝ a (x 0) 1 * -1 * -1)
  ) = fderiv ℝ a (x 0) 1 := by ring
  exact h_eq

/-- Extracts the a=2 adjoint projection from the F_12 curvature matrix. Evaluates to 2i a^2. -/
lemma flrw_project_2_1_2 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 2 1 2 = 2 * Complex.I * (a (x 0) * a (x 0)) := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (flrw_A a) 1 2 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma3.val := flrw_F_1_2 a x ha
  rw [hF]
  rw [fin2_sum]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
  simp only [hs3_00, hs3_01, hs3_10, hs3_11]
  have h_eq : (0.5 : ℂ) * (
    (2 * Complex.I * (a (x 0) * a (x 0)) * 1 * 1 + 2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0) +
    (2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0 + 2 * Complex.I * (a (x 0) * a (x 0)) * -1 * -1)
  ) = 2 * Complex.I * (a (x 0) * a (x 0)) := by ring
  exact h_eq

/-- Extracts the a=0 adjoint projection from the F_23 curvature matrix. Evaluates to 2i a^2. -/
lemma flrw_project_0_2_3 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 0 2 3 = 2 * Complex.I * (a (x 0) * a (x 0)) := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (flrw_A a) 2 3 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val := flrw_F_2_3 a x ha
  rw [hF]
  rw [fin2_sum]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  simp only [hs1_00, hs1_01, hs1_10, hs1_11]
  have h_eq : (0.5 : ℂ) * (
    (2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0 + 2 * Complex.I * (a (x 0) * a (x 0)) * 1 * 1) +
    (2 * Complex.I * (a (x 0) * a (x 0)) * 1 * 1 + 2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0)
  ) = 2 * Complex.I * (a (x 0) * a (x 0)) := by ring
  exact h_eq

/-- Extracts the a=1 adjoint projection from the F_31 curvature matrix. Evaluates to 2i a^2. -/
lemma flrw_project_1_3_1 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  project (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 1 3 1 = 2 * Complex.I * (a (x 0) * a (x 0)) := by
  unfold project getPauli Matrix.trace Matrix.diag
  dsimp only
  have hF : (curvatureSl2c (flrw_A a) 3 1 x).val = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val := flrw_F_3_1 a x ha
  rw [hF]
  rw [fin2_sum]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  simp only [hs2_00, hs2_01, hs2_10, hs2_11]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h_eq : (0.5 : ℂ) * (
    (2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0 + 2 * Complex.I * (a (x 0) * a (x 0)) * -Complex.I * Complex.I) +
    (2 * Complex.I * (a (x 0) * a (x 0)) * Complex.I * -Complex.I + 2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0)
  ) = 2 * Complex.I * (a (x 0) * a (x 0)) := by
    calc (0.5 : ℂ) * ( (2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0 + 2 * Complex.I * (a (x 0) * a (x 0)) * -Complex.I * Complex.I) + (2 * Complex.I * (a (x 0) * a (x 0)) * Complex.I * -Complex.I + 2 * Complex.I * (a (x 0) * a (x 0)) * 0 * 0) )
      _ = (0.5 : ℂ) * ( - (2 * Complex.I * (a (x 0) * a (x 0))) * (Complex.I * Complex.I) - (2 * Complex.I * (a (x 0) * a (x 0))) * (Complex.I * Complex.I) ) := by ring
      _ = (0.5 : ℂ) * ( - (2 * Complex.I * (a (x 0) * a (x 0))) * (-1) - (2 * Complex.I * (a (x 0) * a (x 0))) * (-1) ) := by rw [hI]
      _ = 2 * Complex.I * (a (x 0) * a (x 0)) := by ring
  exact h_eq

/-- Expands the 3-dimensional Levi-Civita summation over the internal isotopic indices. -/
lemma urbantke_sum_iso (F : Fin 3 → Fin 3 → Fin 3 → ℂ) :
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, epsilon3 a b c * F a b c) =
  F 0 1 2 - F 0 2 1 - F 1 0 2 + F 1 2 0 + F 2 0 1 - F 2 1 0 := by
  simp [Fin.sum_univ_three, epsilon3, epsilon3_int]
  ring

/-- Expands the 4-dimensional Levi-Civita summation over the spacetime indices. -/
lemma urbantke_sum_space (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
  (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4, epsilon4 a b c d * F a b c d) =
  F 0 1 2 3 - F 0 1 3 2 - F 0 2 1 3 + F 0 2 3 1 + F 0 3 1 2 - F 0 3 2 1
  - F 1 0 2 3 + F 1 0 3 2 + F 1 2 0 3 - F 1 2 3 0 - F 1 3 0 2 + F 1 3 2 0
  + F 2 0 1 3 - F 2 0 3 1 - F 2 1 0 3 + F 2 1 3 0 + F 2 3 0 1 - F 2 3 1 0
  - F 3 0 1 2 + F 3 0 2 1 + F 3 1 0 2 - F 3 1 2 0 - F 3 2 0 1 + F 3 2 1 0 := by
  simp [Fin.sum_univ_four, epsilon4, epsilon4_int]
  ring

/-- The exact analytically predicted values for the 16 F_{mu, nu} curvature components. -/
noncomputable def flrw_F_expected (adot a2 : ℂ) (mu nu : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if mu = 0 ∧ nu = 1 then adot • sigma1.val
  else if mu = 1 ∧ nu = 0 then -adot • sigma1.val
  else if mu = 0 ∧ nu = 2 then adot • sigma2.val
  else if mu = 2 ∧ nu = 0 then -adot • sigma2.val
  else if mu = 0 ∧ nu = 3 then adot • sigma3.val
  else if mu = 3 ∧ nu = 0 then -adot • sigma3.val
  else if mu = 1 ∧ nu = 2 then (2 * Complex.I * a2) • sigma3.val
  else if mu = 2 ∧ nu = 1 then -(2 * Complex.I * a2) • sigma3.val
  else if mu = 2 ∧ nu = 3 then (2 * Complex.I * a2) • sigma1.val
  else if mu = 3 ∧ nu = 2 then -(2 * Complex.I * a2) • sigma1.val
  else if mu = 3 ∧ nu = 1 then (2 * Complex.I * a2) • sigma2.val
  else if mu = 1 ∧ nu = 3 then -(2 * Complex.I * a2) • sigma2.val
  else 0

lemma curvatureSl2c_same (A : Fin 4 → SpacetimePoint → SL2C) (m : Fin 4) (x : SpacetimePoint) :
  (curvatureSl2c A m m x).val = 0 := by
  rw [curvatureSl2c_def]
  have h_comm : ⁅A m x, A m x⁆ = 0 := lie_self (A m x)
  rw [h_comm]
  simp

/-- Consolidates all 16 F_{mu, nu} tensors into a single rapid-access evaluation theorem. -/
lemma flrw_F_val_master (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) (mu nu : Fin 4) :
  (curvatureSl2c (flrw_A a) mu nu x).val = flrw_F_expected (fderiv ℝ a (x 0) 1) (a (x 0) * a (x 0)) mu nu := by
  have h_rev : ∀ m n, (curvatureSl2c (flrw_A a) n m x).val = - (curvatureSl2c (flrw_A a) m n x).val := by
    intro m n
    have h := curvatureSl2c_antisymm (flrw_A a) n m x
    calc (curvatureSl2c (flrw_A a) n m x).val
      _ = (- curvatureSl2c (flrw_A a) m n x).val := by rw [h]
      _ = - (curvatureSl2c (flrw_A a) m n x).val := rfl

  fin_cases mu <;> fin_cases nu
  · change (curvatureSl2c (flrw_A a) 0 0 x).val = flrw_F_expected _ _ 0 0
    rw [curvatureSl2c_same]; rfl
  · change (curvatureSl2c (flrw_A a) 0 1 x).val = flrw_F_expected _ _ 0 1
    rw [flrw_F_0_1 a x ha]; rfl
  · change (curvatureSl2c (flrw_A a) 0 2 x).val = flrw_F_expected _ _ 0 2
    rw [flrw_F_0_2 a x ha]; rfl
  · change (curvatureSl2c (flrw_A a) 0 3 x).val = flrw_F_expected _ _ 0 3
    rw [flrw_F_0_3 a x ha]; rfl
  · change (curvatureSl2c (flrw_A a) 1 0 x).val = flrw_F_expected _ _ 1 0
    rw [h_rev 0 1, flrw_F_0_1 a x ha]; dsimp [flrw_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (flrw_A a) 1 1 x).val = flrw_F_expected _ _ 1 1
    rw [curvatureSl2c_same]; rfl
  · change (curvatureSl2c (flrw_A a) 1 2 x).val = flrw_F_expected _ _ 1 2
    rw [flrw_F_1_2 a x ha]; rfl
  · change (curvatureSl2c (flrw_A a) 1 3 x).val = flrw_F_expected _ _ 1 3
    rw [h_rev 3 1, flrw_F_3_1 a x ha]; dsimp [flrw_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (flrw_A a) 2 0 x).val = flrw_F_expected _ _ 2 0
    rw [h_rev 0 2, flrw_F_0_2 a x ha]; dsimp [flrw_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (flrw_A a) 2 1 x).val = flrw_F_expected _ _ 2 1
    rw [h_rev 1 2, flrw_F_1_2 a x ha]; dsimp [flrw_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (flrw_A a) 2 2 x).val = flrw_F_expected _ _ 2 2
    rw [curvatureSl2c_same]; rfl
  · change (curvatureSl2c (flrw_A a) 2 3 x).val = flrw_F_expected _ _ 2 3
    rw [flrw_F_2_3 a x ha]; rfl
  · change (curvatureSl2c (flrw_A a) 3 0 x).val = flrw_F_expected _ _ 3 0
    rw [h_rev 0 3, flrw_F_0_3 a x ha]; dsimp [flrw_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (flrw_A a) 3 1 x).val = flrw_F_expected _ _ 3 1
    rw [flrw_F_3_1 a x ha]; rfl
  · change (curvatureSl2c (flrw_A a) 3 2 x).val = flrw_F_expected _ _ 3 2
    rw [h_rev 2 3, flrw_F_2_3 a x ha]; dsimp [flrw_F_expected]; ext i j; simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · change (curvatureSl2c (flrw_A a) 3 3 x).val = flrw_F_expected _ _ 3 3
    rw [curvatureSl2c_same]; rfl

/-- The exact analytically predicted values for the 48 adjoint projection traces P^a_{mu, nu}. -/
noncomputable def flrw_P_expected (adot a2 : ℂ) (c : Fin 3) (mu nu : Fin 4) : ℂ :=
  if c = 0 ∧ mu = 0 ∧ nu = 1 then adot
  else if c = 0 ∧ mu = 1 ∧ nu = 0 then -adot
  else if c = 1 ∧ mu = 0 ∧ nu = 2 then adot
  else if c = 1 ∧ mu = 2 ∧ nu = 0 then -adot
  else if c = 2 ∧ mu = 0 ∧ nu = 3 then adot
  else if c = 2 ∧ mu = 3 ∧ nu = 0 then -adot
  else if c = 2 ∧ mu = 1 ∧ nu = 2 then 2 * Complex.I * a2
  else if c = 2 ∧ mu = 2 ∧ nu = 1 then -2 * Complex.I * a2
  else if c = 0 ∧ mu = 2 ∧ nu = 3 then 2 * Complex.I * a2
  else if c = 0 ∧ mu = 3 ∧ nu = 2 then -2 * Complex.I * a2
  else if c = 1 ∧ mu = 3 ∧ nu = 1 then 2 * Complex.I * a2
  else if c = 1 ∧ mu = 1 ∧ nu = 3 then -2 * Complex.I * a2
  else 0

lemma flrw_project_master_c0 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) (mu nu : Fin 4) :
  project (fun m n => curvatureSl2c (flrw_A a) m n x) 0 mu nu = flrw_P_expected (fderiv ℝ a (x 0) 1) (a (x 0) * a (x 0)) 0 mu nu := by

  -- Explicitly expand project to bypass `let` bindings
  have h_expand : project (fun m n => curvatureSl2c (flrw_A a) m n x) 0 mu nu = 0.5 * ((curvatureSl2c (flrw_A a) mu nu x).val * sigma1.val).trace := rfl
  rw [h_expand]

  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I

  match mu, nu with
  | 0, 0 => rw [flrw_F_val_master a x ha 0 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 0, 1 => rw [flrw_F_val_master a x ha 0 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 0, 2 => rw [flrw_F_val_master a x ha 0 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 0, 3 => rw [flrw_F_val_master a x ha 0 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 1, 0 => rw [flrw_F_val_master a x ha 1 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 1, 1 => rw [flrw_F_val_master a x ha 1 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 1, 2 => rw [flrw_F_val_master a x ha 1 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 1, 3 => rw [flrw_F_val_master a x ha 1 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 2, 0 => rw [flrw_F_val_master a x ha 2 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 2, 1 => rw [flrw_F_val_master a x ha 2 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 2, 2 => rw [flrw_F_val_master a x ha 2 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 2, 3 => rw [flrw_F_val_master a x ha 2 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 3, 0 => rw [flrw_F_val_master a x ha 3 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 3, 1 => rw [flrw_F_val_master a x ha 3 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 3, 2 => rw [flrw_F_val_master a x ha 3 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring
  | 3, 3 => rw [flrw_F_val_master a x ha 3 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11, hI]; ring

lemma I_cubed : Complex.I ^ 3 = -Complex.I := by
  have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
  calc Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
  _ = -1 * Complex.I := by rw [h2]
  _ = -Complex.I := by ring

lemma flrw_project_master_c1 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) (mu nu : Fin 4) :
  project (fun m n => curvatureSl2c (flrw_A a) m n x) 1 mu nu = flrw_P_expected (fderiv ℝ a (x 0) 1) (a (x 0) * a (x 0)) 1 mu nu := by

  -- Explicitly expand project to bypass `let` bindings
  have h_expand : project (fun m n => curvatureSl2c (flrw_A a) m n x) 1 mu nu = 0.5 * ((curvatureSl2c (flrw_A a) mu nu x).val * sigma2.val).trace := rfl
  rw [h_expand]

  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl

  match mu, nu with
  | 0, 0 => rw [flrw_F_val_master a x ha 0 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 0, 1 => rw [flrw_F_val_master a x ha 0 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 0, 2 => rw [flrw_F_val_master a x ha 0 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 0, 3 => rw [flrw_F_val_master a x ha 0 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 0 => rw [flrw_F_val_master a x ha 1 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 1 => rw [flrw_F_val_master a x ha 1 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 2 => rw [flrw_F_val_master a x ha 1 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 3 => rw [flrw_F_val_master a x ha 1 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 0 => rw [flrw_F_val_master a x ha 2 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 1 => rw [flrw_F_val_master a x ha 2 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 2 => rw [flrw_F_val_master a x ha 2 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 3 => rw [flrw_F_val_master a x ha 2 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 0 => rw [flrw_F_val_master a x ha 3 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 1 => rw [flrw_F_val_master a x ha 3 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 2 => rw [flrw_F_val_master a x ha 3 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 3 => rw [flrw_F_val_master a x ha 3 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring

lemma flrw_project_master_c2 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) (mu nu : Fin 4) :
  project (fun m n => curvatureSl2c (flrw_A a) m n x) 2 mu nu = flrw_P_expected (fderiv ℝ a (x 0) 1) (a (x 0) * a (x 0)) 2 mu nu := by

  -- Explicitly expand project to bypass `let` bindings
  have h_expand : project (fun m n => curvatureSl2c (flrw_A a) m n x) 2 mu nu = 0.5 * ((curvatureSl2c (flrw_A a) mu nu x).val * sigma3.val).trace := rfl
  rw [h_expand]

  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl

  match mu, nu with
  | 0, 0 => rw [flrw_F_val_master a x ha 0 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 0, 1 => rw [flrw_F_val_master a x ha 0 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 0, 2 => rw [flrw_F_val_master a x ha 0 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 0, 3 => rw [flrw_F_val_master a x ha 0 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 0 => rw [flrw_F_val_master a x ha 1 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 1 => rw [flrw_F_val_master a x ha 1 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 2 => rw [flrw_F_val_master a x ha 1 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 1, 3 => rw [flrw_F_val_master a x ha 1 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 0 => rw [flrw_F_val_master a x ha 2 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 1 => rw [flrw_F_val_master a x ha 2 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 2 => rw [flrw_F_val_master a x ha 2 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 2, 3 => rw [flrw_F_val_master a x ha 2 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 0 => rw [flrw_F_val_master a x ha 3 0]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 1 => rw [flrw_F_val_master a x ha 3 1]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 2 => rw [flrw_F_val_master a x ha 3 2]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring
  | 3, 3 => rw [flrw_F_val_master a x ha 3 3]; dsimp [flrw_P_expected, flrw_F_expected]; unfold Matrix.trace Matrix.diag; rw [fin2_sum]; simp only [Matrix.mul_apply, fin2_sum, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, hs1_00, hs1_01, hs1_10, hs1_11, hs2_00, hs2_01, hs2_10, hs2_11, hs3_00, hs3_01, hs3_10, hs3_11]; try ring_nf; try simp only [Complex.I_sq, I_cubed]; try ring

lemma space_term_mul_assoc (E F1 F2 F3 : ℂ) : E * F1 * F2 * F3 = E * (F1 * F2 * F3) := by ring

/--
Evaluates the time-time component of the macroscopic Urbantke metric for the FLRW cosmological vacuum.
Yields precisely 12 * adot^3, driving the temporal signature of the expanding FLRW universe.
-/
lemma flrw_metric_00 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  urbantkeMetric (fun m n => curvatureSl2c (flrw_A a) m n x) 0 0 = 12 * (fderiv ℝ a (x 0) 1) ^ 3 := by
  unfold urbantkeMetric
  dsimp only
  simp only [space_term_mul_assoc]
  rw [urbantke_sum_iso]
  simp only [urbantke_sum_space]
  simp only [flrw_project_master_c0 a x ha, flrw_project_master_c1 a x ha, flrw_project_master_c2 a x ha]
  dsimp [flrw_P_expected]
  try ring_nf
  try simp only [Complex.I_sq, I_cubed]
  try ring

/--
Evaluates the x-x spatial component of the macroscopic Urbantke metric for the FLRW cosmological vacuum.
Yields precisely -48 * adot * a^4, capturing the dynamic expansion of the spatial hypersurface.
-/
lemma flrw_metric_11 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  urbantkeMetric (fun m n => curvatureSl2c (flrw_A a) m n x) 1 1 = -48 * (fderiv ℝ a (x 0) 1) * (a (x 0) * a (x 0)) ^ 2 := by
  unfold urbantkeMetric
  dsimp only
  simp only [space_term_mul_assoc]
  rw [urbantke_sum_iso]
  simp only [urbantke_sum_space]
  simp only [flrw_project_master_c0 a x ha, flrw_project_master_c1 a x ha, flrw_project_master_c2 a x ha]
  dsimp [flrw_P_expected]
  try ring_nf
  try simp only [Complex.I_sq, I_cubed]
  try ring

/--
Evaluates the y-y spatial component of the macroscopic Urbantke metric for the FLRW cosmological vacuum.
Yields precisely -48 * adot * a^4, capturing the dynamic expansion of the spatial hypersurface.
-/
lemma flrw_metric_22 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  urbantkeMetric (fun m n => curvatureSl2c (flrw_A a) m n x) 2 2 = -48 * (fderiv ℝ a (x 0) 1) * (a (x 0) * a (x 0)) ^ 2 := by
  unfold urbantkeMetric
  dsimp only
  simp only [space_term_mul_assoc]
  rw [urbantke_sum_iso]
  simp only [urbantke_sum_space]
  simp only [flrw_project_master_c0 a x ha, flrw_project_master_c1 a x ha, flrw_project_master_c2 a x ha]
  dsimp [flrw_P_expected]
  try ring_nf
  try simp only [Complex.I_sq, I_cubed]
  try ring

/--
Evaluates the z-z spatial component of the macroscopic Urbantke metric for the FLRW cosmological vacuum.
Yields precisely -48 * adot * a^4, capturing the dynamic expansion of the spatial hypersurface.
-/
lemma flrw_metric_33 (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  urbantkeMetric (fun m n => curvatureSl2c (flrw_A a) m n x) 3 3 = -48 * (fderiv ℝ a (x 0) 1) * (a (x 0) * a (x 0)) ^ 2 := by
  unfold urbantkeMetric
  dsimp only
  simp only [space_term_mul_assoc]
  rw [urbantke_sum_iso]
  simp only [urbantke_sum_space]
  simp only [flrw_project_master_c0 a x ha, flrw_project_master_c1 a x ha, flrw_project_master_c2 a x ha]
  dsimp [flrw_P_expected]
  try ring_nf
  try simp only [Complex.I_sq, I_cubed]
  try ring

/--
Evaluates the off-diagonal spatial components of the macroscopic Urbantke metric for the FLRW cosmological vacuum.
Because the FLRW spatial slices are strictly isotropic and orthogonal to the time flow, all off-diagonals evaluate to exactly 0.
-/
lemma flrw_metric_off_diagonal (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) (μ ν : Fin 4) (h_diff : μ ≠ ν) :
  urbantkeMetric (fun m n => curvatureSl2c (flrw_A a) m n x) μ ν = 0 := by
  revert h_diff
  fin_cases μ <;> fin_cases ν <;> intro h_diff <;> try { contradiction }
  all_goals {
    unfold urbantkeMetric
    dsimp only
    simp only [space_term_mul_assoc]
    rw [urbantke_sum_iso]
    simp only [urbantke_sum_space]
    simp only [flrw_project_master_c0 a x ha, flrw_project_master_c1 a x ha, flrw_project_master_c2 a x ha]
    dsimp [flrw_P_expected]
    try ring_nf
    try simp only [Complex.I_sq, I_cubed]
    try ring
  }

-- ==============================================================================
-- COMPLEX REALITY HELPERS
-- ==============================================================================

lemma complex_re_im_eq (z : ℂ) (h : z.im = 0) : z = (z.re : ℂ) := by
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im]
    exact h

lemma complex_ne_zero_re (z : ℂ) (h_im : z.im = 0) (h_nz : z ≠ 0) : z.re ≠ 0 := by
  intro h_re
  have h_zero : z = 0 := by
    apply Complex.ext
    · exact h_re
    · exact h_im
  contradiction

lemma im_zero_00 (adot : ℂ) (h_adot_im : adot.im = 0) : (12 * adot ^ 3).im = 0 := by
  rw [complex_re_im_eq adot h_adot_im]
  have : 12 * (adot.re : ℂ) ^ 3 = (((12 : ℝ) * adot.re ^ 3 : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  exact Complex.ofReal_im _

lemma im_zero_ii (adot a_val : ℂ) (h_adot_im : adot.im = 0) (h_a_im : a_val.im = 0) :
  (-48 * adot * (a_val * a_val) ^ 2).im = 0 := by
  rw [complex_re_im_eq adot h_adot_im, complex_re_im_eq a_val h_a_im]
  have : -48 * (adot.re : ℂ) * ((a_val.re : ℂ) * (a_val.re : ℂ)) ^ 2 = (((-48 : ℝ) * adot.re * (a_val.re * a_val.re) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  exact Complex.ofReal_im _

-- ==============================================================================
-- METRIC DETERMINANT KINEMATICS
-- ==============================================================================

lemma pow_six_pos (r : ℝ) (hr : r ≠ 0) : 0 < r ^ 6 := by
  have h2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have h6 : r ^ 6 = (r ^ 2) ^ 3 := by ring
  rw [h6]
  exact pow_pos h2 3

lemma pow_twelve_pos (r : ℝ) (hr : r ≠ 0) : 0 < r ^ 12 := by
  have h2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have h12 : r ^ 12 = (r ^ 2) ^ 6 := by ring
  rw [h12]
  exact pow_pos h2 6

lemma fin_prod_four (f : Fin 4 → ℂ) : (∏ i : Fin 4, f i) = f 0 * f 1 * f 2 * f 3 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp
  ring

lemma det_diag_4x4 (M : Matrix (Fin 4) (Fin 4) ℂ) (h_off : ∀ i j, i ≠ j → M i j = 0) :
  M.det = M 0 0 * M 1 1 * M 2 2 * M 3 3 := by
  have h_diag : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq]
    · rw [h_off i j h]
      exact (Matrix.diagonal_apply_ne _ h).symm
  rw [h_diag]
  rw [Matrix.det_diagonal]
  exact fin_prod_four (fun i => M i i)

lemma flrw_det_eval (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (urbantkeMetric (fun m n => curvatureSl2c (flrw_A a) m n x)).det =
  -1327104 * (fderiv ℝ a (x 0) 1) ^ 6 * (a (x 0)) ^ 12 := by
  have h00 := flrw_metric_00 a x ha
  have h11 := flrw_metric_11 a x ha
  have h22 := flrw_metric_22 a x ha
  have h33 := flrw_metric_33 a x ha
  have h_off : ∀ μ ν, μ ≠ ν → urbantkeMetric (fun m n => curvatureSl2c (flrw_A a) m n x) μ ν = 0 :=
    fun μ ν h_diff => flrw_metric_off_diagonal a x ha μ ν h_diff
  have h_det := det_diag_4x4 (urbantkeMetric (fun m n => curvatureSl2c (flrw_A a) m n x)) h_off
  rw [h_det, h00, h11, h22, h33]
  ring

lemma flrw_det_signs (adot a_val : ℂ)
  (h_adot_im : adot.im = 0) (h_a_im : a_val.im = 0)
  (h_adot_nz : adot ≠ 0) (h_a_nz : a_val ≠ 0) :
  (-1327104 * adot ^ 6 * a_val ^ 12).im = 0 ∧
  (-1327104 * adot ^ 6 * a_val ^ 12).re < 0 := by
  have h_adot_re := complex_re_im_eq adot h_adot_im
  have h_a_re := complex_re_im_eq a_val h_a_im
  have h_sub : -1327104 * adot ^ 6 * a_val ^ 12 = (-1327104 * (adot.re : ℂ) ^ 6 * (a_val.re : ℂ) ^ 12) := by
    rw [← h_adot_re, ← h_a_re]
  rw [h_sub]
  have h_real_cast : (-1327104 * (adot.re : ℂ) ^ 6 * (a_val.re : ℂ) ^ 12) = (((-1327104 : ℝ) * adot.re ^ 6 * a_val.re ^ 12 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [h_real_cast]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  have h_adot_nz_re : adot.re ≠ 0 := complex_ne_zero_re adot h_adot_im h_adot_nz
  have h_a_nz_re : a_val.re ≠ 0 := complex_ne_zero_re a_val h_a_im h_a_nz
  have h_adot_pos := pow_six_pos adot.re h_adot_nz_re
  have h_a_pos := pow_twelve_pos a_val.re h_a_nz_re
  have h_mul_pos : 0 < adot.re ^ 6 * a_val.re ^ 12 := mul_pos h_adot_pos h_a_pos
  linarith

lemma diff_of_fderiv_apply_ne_zero (f : ℝ → ℂ) (t : ℝ) (h : fderiv ℝ f t 1 ≠ 0) : DifferentiableAt ℝ f t := by
  by_contra hc
  have h0 : fderiv ℝ f t = 0 := fderiv_zero_of_not_differentiableAt hc
  have h1 : fderiv ℝ f t 1 = 0 := by rw [h0]; rfl
  exact h h1

lemma flrw_A_eval_0 (a : ℝ → ℂ) (p : SpacetimePoint) : flrw_A a 0 p = 0 := by
  apply Subtype.ext
  change (flrw_A a 0 p).val = 0
  rw [flrw_A_val_eq, flrw_L_0_eq]

lemma flrw_A_eval_1 (a : ℝ → ℂ) (p : SpacetimePoint) : flrw_A a 1 p = toSl2c (a (p 0) • sigma1.val) := by
  unfold flrw_A flrw_L
  simp

lemma flrw_A_eval_2 (a : ℝ → ℂ) (p : SpacetimePoint) : flrw_A a 2 p = toSl2c (a (p 0) • sigma2.val) := by
  unfold flrw_A flrw_L
  simp

lemma flrw_A_eval_3 (a : ℝ → ℂ) (p : SpacetimePoint) : flrw_A a 3 p = toSl2c (a (p 0) • sigma3.val) := by
  unfold flrw_A flrw_L
  simp

lemma flrw_A_eq (pu : PhysicalUniverse) (a : ℝ → ℂ)
  (h0 : ∀ p : SpacetimePoint, pu.toUniverse.sd_sector.val 0 p = 0)
  (h1 : ∀ p : SpacetimePoint, pu.toUniverse.sd_sector.val 1 p = toSl2c (a (p 0) • sigma1.val))
  (h2 : ∀ p : SpacetimePoint, pu.toUniverse.sd_sector.val 2 p = toSl2c (a (p 0) • sigma2.val))
  (h3 : ∀ p : SpacetimePoint, pu.toUniverse.sd_sector.val 3 p = toSl2c (a (p 0) • sigma3.val)) :
  pu.toUniverse.sd_sector.val = flrw_A a := by
  apply funext
  intro μ
  apply funext
  intro p
  fin_cases μ
  · change pu.toUniverse.sd_sector.val 0 p = flrw_A a 0 p
    rw [h0 p, flrw_A_eval_0]
  · change pu.toUniverse.sd_sector.val 1 p = flrw_A a 1 p
    rw [h1 p, flrw_A_eval_1]
  · change pu.toUniverse.sd_sector.val 2 p = flrw_A a 2 p
    rw [h2 p, flrw_A_eval_2]
  · change pu.toUniverse.sd_sector.val 3 p = flrw_A a 3 p
    rw [h3 p, flrw_A_eval_3]

/--
LRW (Isotropic) spacetimes intrinsically satisfy the non-degenerate Lorentzian Reality Conditions natively from the SU(2) topology, requiring no exact scalar field assumptions.
-/
@[litlib_track "FLRW connections produce real Lorentzian metrics"]
theorem flrwSatisfiesReality (pu : PhysicalUniverse) (h_typeO : IsTypeOForm pu) :
  SatisfiesRealityConditions pu := by

  unfold SatisfiesRealityConditions
  intro x _ -- Bulk constraint satisfied strictly globally

  rcases h_typeO with ⟨a, h_a_global⟩

  -- Extract scalar properties at evaluation point x
  have hx := h_a_global x
  have h_a_im : (a (x 0)).im = 0 := hx.1
  have h_adot_im : (fderiv ℝ a (x 0) 1).im = 0 := hx.2.1
  have h_a_nz : a (x 0) ≠ 0 := hx.2.2.1
  have h_adot_nz : fderiv ℝ a (x 0) 1 ≠ 0 := hx.2.2.2.1

  -- Extract and elevate field equalities globally
  have h0 : ∀ p, pu.toUniverse.sd_sector.val 0 p = 0 := fun p => (h_a_global p).2.2.2.2.1
  have h1 : ∀ p, pu.toUniverse.sd_sector.val 1 p = toSl2c (a (p 0) • sigma1.val) := fun p => (h_a_global p).2.2.2.2.2.1
  have h2 : ∀ p, pu.toUniverse.sd_sector.val 2 p = toSl2c (a (p 0) • sigma2.val) := fun p => (h_a_global p).2.2.2.2.2.2.1
  have h3 : ∀ p, pu.toUniverse.sd_sector.val 3 p = toSl2c (a (p 0) • sigma3.val) := fun p => (h_a_global p).2.2.2.2.2.2.2

  have ha_diff : DifferentiableAt ℝ a (x 0) := diff_of_fderiv_apply_ne_zero a (x 0) h_adot_nz

  have h_A_eq : pu.toUniverse.sd_sector.val = flrw_A a := flrw_A_eq pu a h0 h1 h2 h3

  have h_metric_eq : (urbantkeMetric (fun μ ν => curvatureSl2c pu.toUniverse.sd_sector.val μ ν x)) =
                     (urbantkeMetric (fun μ ν => curvatureSl2c (flrw_A a) μ ν x)) := by rw [h_A_eq]

  unfold isLorentzian
  rw [h_metric_eq]

  -- 1. Verify imaginary metric components dynamically collapse to zero
  have h_im_zero : ∀ i j, (urbantkeMetric (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) i j).im = 0 := by
    intro i j
    by_cases h_diff : i = j
    · subst h_diff
      fin_cases i
      · change (urbantkeMetric (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 0 0).im = 0
        rw [flrw_metric_00 a x ha_diff]
        exact im_zero_00 _ h_adot_im
      · change (urbantkeMetric (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 1 1).im = 0
        rw [flrw_metric_11 a x ha_diff]
        exact im_zero_ii _ _ h_adot_im h_a_im
      · change (urbantkeMetric (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 2 2).im = 0
        rw [flrw_metric_22 a x ha_diff]
        exact im_zero_ii _ _ h_adot_im h_a_im
      · change (urbantkeMetric (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) 3 3).im = 0
        rw [flrw_metric_33 a x ha_diff]
        exact im_zero_ii _ _ h_adot_im h_a_im
    · have h_off := flrw_metric_off_diagonal a x ha_diff i j h_diff
      change (urbantkeMetric (fun μ ν => curvatureSl2c (flrw_A a) μ ν x) i j).im = 0
      rw [h_off]
      rfl

  -- 2. Verify determinant reality conditions (strict Non-Degenerate Lorentzian Signature)
  have h_det_eval_eq := flrw_det_eval a x ha_diff
  have h_signs := flrw_det_signs (fderiv ℝ a (x 0) 1) (a (x 0)) h_adot_im h_a_im h_adot_nz h_a_nz

  rw [h_det_eval_eq]

  exact ⟨h_im_zero, h_signs.2, h_signs.1⟩

end CGD.Gravity.ExactSolutions

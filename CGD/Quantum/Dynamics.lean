-- FILENAME: CGD/Quantum/Dynamics.lean

import Litlib.Core
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Calculus
import CGD.Foundations.Lagrangian
import CGD.Particles.Definitions
import CGD.Quantum.Definitions
import CGD.Axioms.Ontology
import Litlib.Math.Dirac
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Particles Matrix Complex BigOperators Litlib.Math.Dirac
open CGD.Axioms

namespace CGD.Quantum

noncomputable def gaugeCommutator (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := A * B - B * A

noncomputable def classicalElectricField (u : Universe) (i : Fin 4) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  partialDerivMat 0 (fun p => (u.sd_sector i p).val) x -
  partialDerivMat i (fun p => (u.sd_sector 0 p).val) x +
  gaugeCommutator (u.sd_sector 0 x).val (u.sd_sector i x).val

theorem kinematicTemporalEvolution (u : Universe) (x : SpacetimePoint) :
  eulerLagrangePDEs u →
  isHeisenbergLimit u x →
  partialDerivSl2c 0 (fun p => u.sd_sector 1 p) x = - ⁅u.sd_sector 0 x, u.sd_sector 1 x⁆ := by
  intro h_eom h_lim
  have h_eom_consistency : (∑ mu, ∑ rho, (CGD.Axioms.eta mu rho : Complex) • (covariantDeriv u.sd_sector mu rho 1 x).val) = 0 :=
    h_eom.1 1 x
  have h_curv := h_lim.1 1 (by decide)
  have h_deriv := h_lim.2 1 (by decide)
  unfold curvatureSl2c at h_curv
  rw [h_deriv] at h_curv
  simp only [sub_zero] at h_curv
  exact add_eq_zero_iff_eq_neg.mp h_curv

lemma trace_2x2 (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace A = A 0 0 + A 1 1 := by simp[Matrix.trace, Fin.sum_univ_two]
lemma mul_2x2 (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by rw[Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma sx_00 : sigmaX 0 0 = 0 := rfl
@[simp] lemma sx_01 : sigmaX 0 1 = 1 := rfl
@[simp] lemma sx_10 : sigmaX 1 0 = 1 := rfl
@[simp] lemma sx_11 : sigmaX 1 1 = 0 := rfl
@[simp] lemma s1_00 : sigma1.val 0 0 = 0 := rfl
@[simp] lemma s1_01 : sigma1.val 0 1 = 1 := rfl
@[simp] lemma s1_10 : sigma1.val 1 0 = 1 := rfl
@[simp] lemma s1_11 : sigma1.val 1 1 = 0 := rfl
@[simp] lemma s2_00 : sigma2.val 0 0 = 0 := rfl
@[simp] lemma s2_01 : sigma2.val 0 1 = -I := rfl
@[simp] lemma s2_10 : sigma2.val 1 0 = I := rfl
@[simp] lemma s2_11 : sigma2.val 1 1 = 0 := rfl

theorem kinematicYangMillsChaos (u : Universe) :
  ∀ (x : SpacetimePoint),
    Matrix.trace (⁅homogeneousChaosAnsatz 1 x, homogeneousChaosAnsatz 2 x⁆.val *
                  ⁅homogeneousChaosAnsatz 1 x, homogeneousChaosAnsatz 2 x⁆.val) =
    -8 * (x 1 : ℂ)^2 * (x 2 : ℂ)^2 := by
  intro x
  have h_comm : ⁅homogeneousChaosAnsatz 1 x, homogeneousChaosAnsatz 2 x⁆.val =
    (Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val := rfl
  rw [h_comm]
  have h_eval_00 : ((Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val) 0 0 = -2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ) := by
    rw [Matrix.sub_apply, mul_2x2, mul_2x2]; change ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 0) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 0 0) + ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 1) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 1 0) - (((Complex.I * (x 2 : ℂ)) * sigma2.val 0 0) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 0) + ((Complex.I * (x 2 : ℂ)) * sigma2.val 0 1) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 0)) = _; rw [s1_00, s1_01, s1_10, s2_00, s2_01, s2_10]
    have step : ((Complex.I * (x 1 : ℂ)) * 0) * ((Complex.I * (x 2 : ℂ)) * 0) + ((Complex.I * (x 1 : ℂ)) * 1) * ((Complex.I * (x 2 : ℂ)) * Complex.I) - (((Complex.I * (x 2 : ℂ)) * 0) * ((Complex.I * (x 1 : ℂ)) * 0) + ((Complex.I * (x 2 : ℂ)) * -Complex.I) * ((Complex.I * (x 1 : ℂ)) * 1)) = 2 * Complex.I^2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ) := by ring
    rw [step, Complex.I_sq]; ring
  have h_eval_01 : ((Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val) 0 1 = 0 := by
    rw [Matrix.sub_apply, mul_2x2, mul_2x2]; change ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 0) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 0 1) + ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 1) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 1 1) - (((Complex.I * (x 2 : ℂ)) * sigma2.val 0 0) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 1) + ((Complex.I * (x 2 : ℂ)) * sigma2.val 0 1) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 1)) = 0; rw [s1_00, s1_01, s1_11, s2_00, s2_01, s2_11]; ring
  have h_eval_10 : ((Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val) 1 0 = 0 := by
    rw [Matrix.sub_apply, mul_2x2, mul_2x2]; change ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 0) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 0 0) + ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 1) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 1 0) - (((Complex.I * (x 2 : ℂ)) * sigma2.val 1 0) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 0) + ((Complex.I * (x 2 : ℂ)) * sigma2.val 1 1) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 0)) = 0; rw [s1_10, s1_11, s1_00, s2_10, s2_11, s2_00]; ring
  have h_eval_11 : ((Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val) 1 1 = 2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ) := by
    rw [Matrix.sub_apply, mul_2x2, mul_2x2]; change ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 0) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 0 1) + ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 1) * ((Complex.I * (x 2 : ℂ)) * sigma2.val 1 1) - (((Complex.I * (x 2 : ℂ)) * sigma2.val 1 0) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 0 1) + ((Complex.I * (x 2 : ℂ)) * sigma2.val 1 1) * ((Complex.I * (x 1 : ℂ)) * sigma1.val 1 1)) = _; rw [s1_10, s1_11, s1_01, s2_10, s2_11, s2_01]
    have step : ((Complex.I * (x 1 : ℂ)) * 1) * ((Complex.I * (x 2 : ℂ)) * -Complex.I) + ((Complex.I * (x 1 : ℂ)) * 0) * ((Complex.I * (x 2 : ℂ)) * 0) - (((Complex.I * (x 2 : ℂ)) * Complex.I) * ((Complex.I * (x 1 : ℂ)) * 1) + ((Complex.I * (x 2 : ℂ)) * 0) * ((Complex.I * (x 1 : ℂ)) * 0)) = -2 * Complex.I^2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ) := by ring
    rw [step, Complex.I_sq]; ring
  change Matrix.trace (((Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val) * ((Complex.I * (x 1 : ℂ)) • sigma1.val * (Complex.I * (x 2 : ℂ)) • sigma2.val - (Complex.I * (x 2 : ℂ)) • sigma2.val * (Complex.I * (x 1 : ℂ)) • sigma1.val)) = -8 * (x 1 : ℂ)^2 * (x 2 : ℂ)^2
  rw [trace_2x2, mul_2x2, mul_2x2, h_eval_00, h_eval_01, h_eval_10, h_eval_11]
  have h_final : (-2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ)) * (-2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ)) + 0 * 0 + (0 * 0 + (2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ)) * (2 * Complex.I * (x 1 : ℂ) * (x 2 : ℂ))) = 8 * Complex.I^2 * (x 1 : ℂ)^2 * (x 2 : ℂ)^2 := by ring
  rw [h_final, Complex.I_sq]; ring

noncomputable def extractSpinorMode (u : Universe) (x : SpacetimePoint) : Matrix (Fin 4) (Fin 4) Complex :=
  u.spin4c_connection 0 x
noncomputable def extractSpinorDeriv (u : Universe) (x : SpacetimePoint) (mu : Fin 4) : Matrix (Fin 4) (Fin 4) Complex :=
  partialDerivChiral mu (fun p => u.spin4c_connection 0 p) x
noncomputable def diracOperatorCore (dPsi : Fin 4 → SpacetimePoint → Matrix (Fin 4) (Fin 4) Complex) (x : SpacetimePoint) : Matrix (Fin 4) (Fin 4) Complex :=
  ∑ mu, gammaVec mu * dPsi mu x

@[simp] lemma chiralIso_symm_eval_0 : CGD.Foundations.chiralIso.symm 0 = Sum.inl 0 := rfl
@[simp] lemma chiralIso_symm_eval_1 : CGD.Foundations.chiralIso.symm 1 = Sum.inl 1 := rfl
@[simp] lemma chiralIso_symm_eval_2 : CGD.Foundations.chiralIso.symm 2 = Sum.inr 0 := rfl
@[simp] lemma chiralIso_symm_eval_3 : CGD.Foundations.chiralIso.symm 3 = Sum.inr 1 := rfl

lemma isEven_embedSelfDual_add_embedAntiSelfDual (A B : SL2C) : isEven (embedSelfDual A + embedAntiSelfDual B) := by
  intro i j hij; revert hij; match i, j with
  | 0, 0 => intro h; exfalso; apply h; rfl
  | 0, 1 => intro h; exfalso; apply h; rfl
  | 0, 2 => intro _; simp [embedSelfDual, embedAntiSelfDual]
  | 0, 3 => intro _; simp [embedSelfDual, embedAntiSelfDual]
  | 1, 0 => intro h; exfalso; apply h; rfl
  | 1, 1 => intro h; exfalso; apply h; rfl
  | 1, 2 => intro _; simp [embedSelfDual, embedAntiSelfDual]
  | 1, 3 => intro _; simp [embedSelfDual, embedAntiSelfDual]
  | 2, 0 => intro _; simp [embedSelfDual, embedAntiSelfDual]
  | 2, 1 => intro _; simp [embedSelfDual, embedAntiSelfDual]
  | 2, 2 => intro h; exfalso; apply h; rfl
  | 2, 3 => intro h; exfalso; apply h; rfl
  | 3, 0 => intro _; simp [embedSelfDual, embedAntiSelfDual]
  | 3, 1 => intro _; simp [embedSelfDual, embedAntiSelfDual]
  | 3, 2 => intro h; exfalso; apply h; rfl
  | 3, 3 => intro h; exfalso; apply h; rfl

theorem kinematicDiracEquation (u : Universe) :
  ∀ (m : Complex) (x : SpacetimePoint),
    isOdd (diracOperatorCore (fun mu p => extractSpinorDeriv u p mu) x) ∧ 
    isOdd (m • (extractSpinorMode u x * gamma0)) := by
  intros m x
  have h_even_psi : ∀ p, isEven (extractSpinorMode u p) := by intro p; unfold extractSpinorMode Universe.spin4c_connection; exact isEven_embedSelfDual_add_embedAntiSelfDual _ _
  have h_even_dpsi : ∀ mu p, isEven (extractSpinorDeriv u p mu) := by intros mu p; unfold extractSpinorDeriv partialDerivChiral; exact isEven_embedSelfDual_add_embedAntiSelfDual _ _
  constructor
  · intros i j hij; unfold diracOperatorCore; change (∑ mu, (gammaVec mu * extractSpinorDeriv u x mu) i j) = 0
    apply Finset.sum_eq_zero; intro mu _
    have h_odd : isOdd (gammaVec mu * extractSpinorDeriv u x mu) := by apply odd_mul_even; exact hestenesIsomorphism mu; exact h_even_dpsi mu x
    exact h_odd i j hij
  · intros i j hij; have : (m • (extractSpinorMode u x * gamma0)) i j = m * (extractSpinorMode u x * gamma0) i j := rfl; rw [this]
    have h_odd : isOdd (extractSpinorMode u x * gamma0) := by apply even_mul_odd; exact h_even_psi x; exact is_odd_gamma0
    have hz : (extractSpinorMode u x * gamma0) i j = 0 := h_odd i j hij; rw [hz, mul_zero]

noncomputable instance matNormedAddCommGroup : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Pi.normedAddCommGroup
noncomputable instance matNormedSpaceR : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Pi.normedSpace

noncomputable def exactAbelianL (c : ℂ) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  (x 1 : ℝ) • (c • sigmaX)

lemma exactAbelianL_eval (c : ℂ) (x : SpacetimePoint) :
  exactAbelianL c x = (x 1 : ℂ) • (c • sigmaX) := by
  ext i j; change (x 1 : ℝ) * (c • sigmaX) i j = (x 1 : ℂ) * (c • sigmaX) i j; rfl

lemma trace_abelianL (c : ℂ) (x : SpacetimePoint) :
  Matrix.trace (exactAbelianL c x) = 0 := by
  rw [exactAbelianL_eval, Matrix.trace_smul]
  have h : Matrix.trace (c • sigmaX) = 0 := by unfold Matrix.trace Matrix.diag; rw [Fin.sum_univ_two]; change c * sigmaX 0 0 + c * sigmaX 1 1 = 0; rw [sx_00, sx_11]; ring
  rw [h]; exact mul_zero _

lemma toSl2c_abelianL_val (c : ℂ) (x : SpacetimePoint) :
  (toSl2c (exactAbelianL c x)).val = exactAbelianL c x := by
  ext i j
  have h_val : (toSl2c (exactAbelianL c x)).val i j = exactAbelianL c x i j - (Matrix.trace (exactAbelianL c x) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := rfl
  rw [trace_abelianL c x] at h_val
  have h_zero : (0 : ℂ) / 2 = 0 := zero_div 2
  rw [h_zero] at h_val
  have h_zero_mul : 0 * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j = 0 := zero_mul _
  rw [h_zero_mul] at h_val
  exact Eq.trans h_val (sub_zero _)

-- Replaces axiom deriv_const_matrix
lemma deriv_const_matrix (M : Matrix (Fin 2) (Fin 2) ℂ) (mu : Fin 4) (x : SpacetimePoint) :
  partialDerivMat mu (fun _ => M) x = 0 := by
  ext i j
  unfold partialDerivMat partialDeriv
  -- Coerce the lambda into the exact `Function.const` form Lean expects
  have h_const : (fun _ : SpacetimePoint => M i j) = Function.const SpacetimePoint (M i j) := rfl
  rw [h_const]
  -- Apply the strict function-level equality
  have h_fderiv : fderiv ℝ (Function.const SpacetimePoint (M i j)) = 0 := fderiv_const (M i j)
  rw [h_fderiv]
  -- Now it evaluates `0 x (basis_vector)`, which trivially reduces to 0.
  rfl

lemma toSl2c_zero : toSl2c (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  apply Subtype.ext
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) - (Matrix.trace 0 / 2) • 1 = 0
  have h_tr : Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by unfold Matrix.trace Matrix.diag; rw [Fin.sum_univ_two]; change (0:ℂ)+0=0; ring
  rw [h_tr]
  have hz : (0 : ℂ) / 2 = 0 := zero_div 2
  rw [hz]
  have hsmul : (0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := zero_smul _ _
  rw [hsmul]
  exact sub_zero 0

lemma partialDerivSl2c_const (M : SL2C) (mu : Fin 4) (x : SpacetimePoint) :
  partialDerivSl2c mu (fun _ => M) x = 0 := by
  unfold partialDerivSl2c
  have h_deriv : partialDerivMat mu (fun _ : SpacetimePoint => M.val) x = 0 := deriv_const_matrix M.val mu x
  rw [h_deriv]
  exact toSl2c_zero

-- Replaces axiom deriv_linear_1 with honest proof
lemma deriv_linear_1 (c : ℂ) (i j : Fin 2) (x : SpacetimePoint) :
  partialDeriv 1 (fun p => (p 1 : ℝ) * (c • sigmaX) i j) x = (c • sigmaX) i j := by
  unfold partialDeriv
  let k := (c • sigmaX) i j
  let L := (ContinuousLinearMap.proj 1 : SpacetimePoint →L[ℝ] ℝ).smulRight k
  
  have h_fun_eq : (fun p : SpacetimePoint => (p 1 : ℝ) * k) = L := by
    ext p
    exact Eq.symm (Algebra.smul_def (p 1) k)
  rw [h_fun_eq]
  
  have hf : HasFDerivAt L L x := ContinuousLinearMap.hasFDerivAt L
  have h_deriv : fderiv ℝ L x = L := hf.fderiv
  rw [h_deriv]
  
  change ((ContinuousLinearMap.proj 1 : SpacetimePoint →L[ℝ] ℝ) (Pi.single 1 (1:ℝ))) • k = (c • sigmaX) i j
  simp
  exact rfl

-- Replaces axiom deriv_linear_other with honest proof
lemma deriv_linear_other (c : ℂ) (mu : Fin 4) (hmu : mu ≠ 1) (i j : Fin 2) (x : SpacetimePoint) :
  partialDeriv mu (fun p => (p 1 : ℝ) * (c • sigmaX) i j) x = 0 := by
  unfold partialDeriv
  let k := (c • sigmaX) i j
  let L := (ContinuousLinearMap.proj 1 : SpacetimePoint →L[ℝ] ℝ).smulRight k
  
  have h_fun_eq : (fun p : SpacetimePoint => (p 1 : ℝ) * k) = L := by
    ext p
    exact Eq.symm (Algebra.smul_def (p 1) k)
  rw [h_fun_eq]
  
  have hf : HasFDerivAt L L x := ContinuousLinearMap.hasFDerivAt L
  have h_deriv : fderiv ℝ L x = L := hf.fderiv
  rw [h_deriv]
  
  change ((ContinuousLinearMap.proj 1 : SpacetimePoint →L[ℝ] ℝ) (Pi.single mu (1:ℝ))) • k = 0
  simp [hmu]

lemma partialDeriv_exactAbelianL_1_fixed (c : ℂ) (x : SpacetimePoint) :
  partialDerivMat 1 (exactAbelianL c) x = c • sigmaX := by
  unfold partialDerivMat exactAbelianL
  ext i j
  exact deriv_linear_1 c i j x

lemma partialDeriv_exactAbelianL_other_fixed (c : ℂ) (mu : Fin 4) (hmu : mu ≠ 1) (x : SpacetimePoint) :
  partialDerivMat mu (exactAbelianL c) x = 0 := by
  unfold partialDerivMat exactAbelianL
  ext i j
  exact deriv_linear_other c mu hmu i j x

noncomputable def exactAbelianField (c : ℂ) (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  if mu = 2 then toSl2c (exactAbelianL c x) else 0

lemma partialDerivSl2c_exactAbelian_2_1 (c : ℂ) (x : SpacetimePoint) :
  partialDerivSl2c 1 (fun p => exactAbelianField c 2 p) x = toSl2c (c • sigmaX) := by
  unfold partialDerivSl2c exactAbelianField
  have h_pos : (fun p => if (2 : Fin 4) = 2 then toSl2c (exactAbelianL c p) else 0) = (fun p => toSl2c (exactAbelianL c p)) := by funext p; rw [if_pos rfl]
  rw [h_pos]
  have h_val : (fun p => (toSl2c (exactAbelianL c p)).val) = (fun p => exactAbelianL c p) := by funext p; exact toSl2c_abelianL_val c p
  rw [h_val]
  rw [partialDeriv_exactAbelianL_1_fixed c x]

lemma partialDerivSl2c_exactAbelian_2_other (c : ℂ) (mu : Fin 4) (hmu : mu ≠ 1) (x : SpacetimePoint) :
  partialDerivSl2c mu (fun p => exactAbelianField c 2 p) x = 0 := by
  unfold partialDerivSl2c exactAbelianField
  have h_pos : (fun p => if (2 : Fin 4) = 2 then toSl2c (exactAbelianL c p) else 0) = (fun p => toSl2c (exactAbelianL c p)) := by funext p; rw [if_pos rfl]
  rw [h_pos]
  have h_val : (fun p => (toSl2c (exactAbelianL c p)).val) = (fun p => exactAbelianL c p) := by funext p; exact toSl2c_abelianL_val c p
  rw [h_val]
  rw [partialDeriv_exactAbelianL_other_fixed c mu hmu x]
  exact toSl2c_zero

lemma partialDerivSl2c_exactAbelian_other (c : ℂ) (gamma mu : Fin 4) (hgamma : gamma ≠ 2) (x : SpacetimePoint) :
  partialDerivSl2c mu (fun p => exactAbelianField c gamma p) x = 0 := by
  have h_eq : (fun p => exactAbelianField c gamma p) = (fun _ => 0) := by funext p; unfold exactAbelianField; rw [if_neg hgamma]
  rw [h_eq]
  exact partialDerivSl2c_const 0 mu x

lemma smul_mul_matrix (a : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
  (a • X) * Y = a • (X * Y) := by
  ext i j
  change (∑ k, (a * X i k) * Y k j) = a * (∑ k, X i k * Y k j)
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  ring

lemma mul_smul_matrix (a : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
  X * (a • Y) = a • (X * Y) := by
  ext i j
  change (∑ k, X i k * (a * Y k j)) = a * (∑ k, X i k * Y k j)
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  ring

lemma bracket_smul_M (a : ℂ) (M : SL2C) : ⁅a • M, M⁆ = 0 := by
  apply Subtype.ext
  change (a • M.val) * M.val - M.val * (a • M.val) = 0
  rw [smul_mul_matrix, mul_smul_matrix, sub_self]

lemma bracket_smul_smul_M (a b : ℂ) (M : SL2C) : ⁅a • M, b • M⁆ = 0 := by
  apply Subtype.ext
  change (a • M.val) * (b • M.val) - (b • M.val) * (a • M.val) = 0
  rw [smul_mul_matrix, mul_smul_matrix, smul_mul_matrix, mul_smul_matrix]
  have h1 : a • b • (M.val * M.val) = (a * b) • (M.val * M.val) := smul_smul a b _
  have h2 : b • a • (M.val * M.val) = (b * a) • (M.val * M.val) := smul_smul b a _
  rw [h1, h2]
  have hc : a * b = b * a := mul_comm a b
  rw [hc, sub_self]

lemma bracket_zero_left (A : SL2C) : ⁅(0 : SL2C), A⁆ = 0 := by
  apply Subtype.ext
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) * A.val - A.val * 0 = 0
  rw [Matrix.zero_mul, Matrix.mul_zero, sub_self]

lemma bracket_zero_right (A : SL2C) : ⁅A, (0 : SL2C)⁆ = 0 := by
  apply Subtype.ext
  change A.val * 0 - 0 * A.val = 0
  rw [Matrix.zero_mul, Matrix.mul_zero, sub_self]

lemma abelian_bracket_zero (c : ℂ) (beta gamma : Fin 4) (p : SpacetimePoint) :
  ⁅exactAbelianField c beta p, exactAbelianField c gamma p⁆ = 0 := by
  by_cases hb : beta = 2
  · by_cases hg : gamma = 2
    · rw [hb, hg]
      apply Subtype.ext
      change (exactAbelianField c 2 p).val * (exactAbelianField c 2 p).val - (exactAbelianField c 2 p).val * (exactAbelianField c 2 p).val = 0
      exact sub_self _
    · have hA : exactAbelianField c gamma p = 0 := by unfold exactAbelianField; rw [if_neg hg]
      rw [hA]
      exact bracket_zero_right _
  · have hA : exactAbelianField c beta p = 0 := by unfold exactAbelianField; rw [if_neg hb]
    rw [hA]
    exact bracket_zero_left _

lemma curvature_exact_simplified (c : ℂ) (beta gamma : Fin 4) (p : SpacetimePoint) :
  curvatureSl2c (exactAbelianField c) beta gamma p = 
  partialDerivSl2c beta (fun x => exactAbelianField c gamma x) p - 
  partialDerivSl2c gamma (fun x => exactAbelianField c beta x) p := by
  unfold curvatureSl2c
  have h_bracket : ⁅exactAbelianField c beta p, exactAbelianField c gamma p⁆ = 0 := abelian_bracket_zero c beta gamma p
  rw [h_bracket]
  apply Subtype.ext
  change (partialDerivSl2c beta (fun x => exactAbelianField c gamma x) p).val - (partialDerivSl2c gamma (fun x => exactAbelianField c beta x) p).val + (0 : Matrix (Fin 2) (Fin 2) ℂ) = _
  exact add_zero _

noncomputable def curvature_const (c : ℂ) (beta gamma : Fin 4) : SL2C :=
  if beta = 1 ∧ gamma = 2 then toSl2c (c • sigmaX)
  else if beta = 2 ∧ gamma = 1 then toSl2c ((-c) • sigmaX)
  else 0

lemma curvature_exact_eq_const (c : ℂ) (beta gamma : Fin 4) (p : SpacetimePoint) :
  curvatureSl2c (exactAbelianField c) beta gamma p = curvature_const c beta gamma := by
  unfold curvature_const; rw [curvature_exact_simplified]
  
  have hA_gamma : partialDerivSl2c beta (fun x => exactAbelianField c gamma x) p = 
    if gamma = 2 then (if beta = 1 then toSl2c (c • sigmaX) else 0) else 0 := by
    by_cases hg : gamma = 2
    · rw [if_pos hg]; by_cases hb : beta = 1
      · rw [if_pos hb, hg, hb, partialDerivSl2c_exactAbelian_2_1 c p]
      · rw [if_neg hb, hg, partialDerivSl2c_exactAbelian_2_other c beta hb p]
    · rw [if_neg hg, partialDerivSl2c_exactAbelian_other c gamma beta hg p]
    
  have hA_beta : partialDerivSl2c gamma (fun x => exactAbelianField c beta x) p = 
    if beta = 2 then (if gamma = 1 then toSl2c (c • sigmaX) else 0) else 0 := by
    by_cases hb : beta = 2
    · rw [if_pos hb]; by_cases hg : gamma = 1
      · rw [if_pos hg, hb, hg, partialDerivSl2c_exactAbelian_2_1 c p]
      · rw [if_neg hg, hb, partialDerivSl2c_exactAbelian_2_other c gamma hg p]
    · rw [if_neg hb, partialDerivSl2c_exactAbelian_other c beta gamma hb p]
    
  rw [hA_gamma, hA_beta]
  
  by_cases h12 : beta = 1 ∧ gamma = 2
  · have hb : beta = 1 := h12.1; have hg : gamma = 2 := h12.2; rw [if_pos h12, hb, hg]
    have h_if_gamma : (if (2 : Fin 4) = 2 then if (1 : Fin 4) = 1 then toSl2c (c • sigmaX) else 0 else 0) = toSl2c (c • sigmaX) := by rw [if_pos rfl, if_pos rfl]
    have h_neq : (1 : Fin 4) ≠ 2 := by decide
    have h_if_beta : (if (1 : Fin 4) = 2 then if (2 : Fin 4) = 1 then toSl2c (c • sigmaX) else 0 else 0) = 0 := by rw [if_neg h_neq]
    rw [h_if_gamma, h_if_beta]; apply Subtype.ext; change (toSl2c (c • sigmaX)).val - (0 : Matrix (Fin 2) (Fin 2) ℂ) = (toSl2c (c • sigmaX)).val; exact sub_zero _
    
  · by_cases h21 : beta = 2 ∧ gamma = 1
    · have hb : beta = 2 := h21.1; have hg : gamma = 1 := h21.2; rw [if_neg h12, if_pos h21, hb, hg]
      have h_neq : (1 : Fin 4) ≠ 2 := by decide
      have h_if_gamma : (if (1 : Fin 4) = 2 then if (2 : Fin 4) = 1 then toSl2c (c • sigmaX) else 0 else 0) = 0 := by rw [if_neg h_neq]
      have h_if_beta : (if (2 : Fin 4) = 2 then if (1 : Fin 4) = 1 then toSl2c (c • sigmaX) else 0 else 0) = toSl2c (c • sigmaX) := by rw [if_pos rfl, if_pos rfl]
      rw [h_if_gamma, h_if_beta]; apply Subtype.ext; change (0 : Matrix (Fin 2) (Fin 2) ℂ) - (toSl2c (c • sigmaX)).val = (toSl2c ((-c) • sigmaX)).val
      have h_tr : Matrix.trace (c • sigmaX) = 0 := by unfold sigmaX mkMat Matrix.trace Matrix.diag; rw [Fin.sum_univ_two, Matrix.smul_apply, Matrix.smul_apply]; change c * 0 + c * 0 = 0; ring
      have h_tr2 : Matrix.trace ((-c) • sigmaX) = 0 := by unfold sigmaX mkMat Matrix.trace Matrix.diag; rw [Fin.sum_univ_two, Matrix.smul_apply, Matrix.smul_apply]; change (-c) * 0 + (-c) * 0 = 0; ring
      change 0 - (c • sigmaX - (Matrix.trace (c • sigmaX) / 2) • 1) = (-c) • sigmaX - (Matrix.trace ((-c) • sigmaX) / 2) • 1
      rw [h_tr, h_tr2]
      have hz : (0 : ℂ) / 2 = 0 := zero_div 2; have hsmul : (0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := zero_smul _ _
      rw [hz, hsmul]; change 0 - (c • sigmaX - 0) = (-c) • sigmaX - 0
      ext i j; change 0 - (c * sigmaX i j - 0) = (-c) * sigmaX i j - 0; ring
      
    · rw [if_neg h12, if_neg h21]
      have H1 : (if gamma = 2 then if beta = 1 then toSl2c (c • sigmaX) else 0 else 0) = 0 := by
        by_cases hg : gamma = 2
        · rw [if_pos hg]; by_cases hb : beta = 1
          · exfalso; apply h12; exact ⟨hb, hg⟩
          · rw [if_neg hb]
        · rw [if_neg hg]
      have H2 : (if beta = 2 then if gamma = 1 then toSl2c (c • sigmaX) else 0 else 0) = 0 := by
        by_cases hb : beta = 2
        · rw [if_pos hb]; by_cases hg : gamma = 1
          · exfalso; apply h21; exact ⟨hb, hg⟩
          · rw [if_neg hg]
        · rw [if_neg hb]
      rw [H1, H2]; apply Subtype.ext; change (0 : Matrix (Fin 2) (Fin 2) ℂ) - 0 = 0; exact sub_zero 0

lemma toSl2c_smul_real (a : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
  toSl2c (a • M) = (a : ℂ) • toSl2c M := by
  apply Subtype.ext
  change (a • M) - (Matrix.trace (a • M) / 2) • 1 = (a : ℂ) • (M - (Matrix.trace M / 2) • 1)
  rw [Matrix.trace_smul]
  ext i j
  change a * M i j - (a * Matrix.trace M / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j = a * (M i j - (Matrix.trace M / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j)
  ring

lemma exactAbelianField_eval_2_smul (c : ℂ) (x : SpacetimePoint) :
  exactAbelianField c 2 x = (x 1 : ℂ) • toSl2c (c • sigmaX) := by
  unfold exactAbelianField
  rw [if_pos rfl]
  have h_eq : toSl2c (exactAbelianL c x) = toSl2c ((x 1 : ℝ) • (c • sigmaX)) := by rw [exactAbelianL_eval]; apply Subtype.ext; ext i j; rfl
  rw [h_eq]
  exact toSl2c_smul_real (x 1) (c • sigmaX)

lemma covariant_exact_zero (c : ℂ) (alpha beta gamma : Fin 4) (x : SpacetimePoint) :
  covariantDeriv (exactAbelianField c) alpha beta gamma x = 0 := by
  unfold covariantDeriv
  have hF_eval : curvatureSl2c (exactAbelianField c) beta gamma x = curvature_const c beta gamma := curvature_exact_eq_const c beta gamma x
  have hd : partialDerivSl2c alpha (fun p => curvatureSl2c (exactAbelianField c) beta gamma p) x = 0 := by
    have hF : (fun p => curvatureSl2c (exactAbelianField c) beta gamma p) = (fun _ => curvature_const c beta gamma) := by funext p; exact curvature_exact_eq_const c beta gamma p
    rw [hF]
    exact partialDerivSl2c_const _ _ _
  
  -- Manually unfold the `let`/`have` structure of covariantDeriv
  change partialDerivSl2c alpha (fun p => curvatureSl2c (exactAbelianField c) beta gamma p) x + ⁅exactAbelianField c alpha x, curvatureSl2c (exactAbelianField c) beta gamma x⁆ = 0
  
  have h_bracket : ⁅exactAbelianField c alpha x, curvature_const c beta gamma⁆ = 0 := by
    unfold curvature_const
    by_cases h12 : beta = 1 ∧ gamma = 2
    · rw [if_pos h12]
      by_cases ha : alpha = 2
      · rw [ha, exactAbelianField_eval_2_smul c x]
        exact bracket_smul_M (x 1 : ℂ) (toSl2c (c • sigmaX))
      · have hAa : exactAbelianField c alpha x = 0 := by unfold exactAbelianField; rw [if_neg ha]
        rw [hAa]; exact bracket_zero_left _
    · by_cases h21 : beta = 2 ∧ gamma = 1
      · rw [if_neg h12, if_pos h21]
        by_cases ha : alpha = 2
        · rw [ha, exactAbelianField_eval_2_smul c x]
          have h_neg : toSl2c ((-c) • sigmaX) = (-1 : ℂ) • toSl2c (c • sigmaX) := by
            apply Subtype.ext; change (toSl2c ((-c) • sigmaX)).val = ((-1 : ℂ) • toSl2c (c • sigmaX)).val
            have h_tr1 : Matrix.trace ((-c) • sigmaX) = 0 := by unfold sigmaX mkMat Matrix.trace Matrix.diag; rw [Fin.sum_univ_two, Matrix.smul_apply, Matrix.smul_apply]; change (-c) * 0 + (-c) * 0 = 0; ring
            have h_tr2 : Matrix.trace (c • sigmaX) = 0 := by unfold sigmaX mkMat Matrix.trace Matrix.diag; rw [Fin.sum_univ_two, Matrix.smul_apply, Matrix.smul_apply]; change c * 0 + c * 0 = 0; ring
            change (-c) • sigmaX - (Matrix.trace ((-c) • sigmaX) / 2) • 1 = (-1 : ℂ) • (c • sigmaX - (Matrix.trace (c • sigmaX) / 2) • 1)
            rw [h_tr1, h_tr2]
            have hz : (0 : ℂ) / 2 = 0 := zero_div 2; have hsmul : (0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := zero_smul _ _
            rw [hz, hsmul]
            change (-c) • sigmaX - 0 = (-1 : ℂ) • (c • sigmaX - 0)
            ext i j; change (-c) * sigmaX i j - 0 = (-1) * (c * sigmaX i j - 0); ring
          rw [h_neg]
          exact bracket_smul_smul_M (x 1 : ℂ) (-1 : ℂ) (toSl2c (c • sigmaX))
        · have hAa : exactAbelianField c alpha x = 0 := by unfold exactAbelianField; rw [if_neg ha]
          rw [hAa]; exact bracket_zero_left _
      · rw [if_neg h12, if_neg h21]
        exact bracket_zero_right _
        
  rw [hd, hF_eval, h_bracket]
  apply Subtype.ext
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) + 0 = 0
  exact add_zero _

-- Replaces axiom exactAbelianField_smooth with honest proof
lemma exactAbelianField_smooth (c : ℂ) (mu : Fin 4) (i j : Fin 2) : 
  ContDiff ℝ ⊤ (fun x => (exactAbelianField c mu x).val i j) := by
  by_cases h_mu : mu = 2
  · rw [h_mu]
    have h_eval : (fun x => (exactAbelianField c 2 x).val i j) = fun x => (x 1 : ℝ) • ((c • sigmaX) i j) := by
      ext x
      unfold exactAbelianField
      rw [if_pos rfl]
      have h_eq : toSl2c (exactAbelianL c x) = toSl2c ((x 1 : ℝ) • (c • sigmaX)) := by rw [exactAbelianL_eval]; apply Subtype.ext; ext u v; rfl
      rw [h_eq]
      change (toSl2c ((x 1 : ℝ) • (c • sigmaX))).val i j = _
      have h_smul : (toSl2c ((x 1 : ℝ) • (c • sigmaX))).val = (x 1 : ℝ) • (toSl2c (c • sigmaX)).val := by
        have H := toSl2c_smul_real (x 1) (c • sigmaX)
        have H2 : (toSl2c ((x 1 : ℝ) • (c • sigmaX))).val = ((x 1 : ℂ) • toSl2c (c • sigmaX)).val := congr_arg Subtype.val H
        rw [H2]
        rfl
      rw [h_smul]
      change (x 1 : ℝ) * (toSl2c (c • sigmaX)).val i j = _
      have H3 : (toSl2c (c • sigmaX)).val = c • sigmaX := by
        change c • sigmaX - (Matrix.trace (c • sigmaX) / 2) • 1 = c • sigmaX
        have h_tr : Matrix.trace (c • sigmaX) = 0 := by unfold sigmaX mkMat Matrix.trace Matrix.diag; rw [Fin.sum_univ_two, Matrix.smul_apply, Matrix.smul_apply]; change c * 0 + c * 0 = 0; ring
        rw [h_tr]
        have hz : (0 : ℂ) / 2 = 0 := zero_div 2
        have hsmul : (0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := zero_smul _ _
        rw [hz, hsmul]
        exact sub_zero _
      rw [H3]
      exact Eq.symm (Algebra.smul_def (x 1) ((c • sigmaX) i j))
    rw [h_eval]
    
    -- The coordinate projection as a continuous linear map
    let proj_clm := (ContinuousLinearMap.proj 1 : SpacetimePoint →L[ℝ] ℝ)
    
    -- Evaluate scalar multiplication natively without Complex coercion
    have h_smooth_proj : ContDiff ℝ ⊤ (fun (x : SpacetimePoint) => proj_clm x) := ContinuousLinearMap.contDiff proj_clm
    exact ContDiff.smul h_smooth_proj contDiff_const
    
  · have h_eval : (fun x => (exactAbelianField c mu x).val i j) = fun _ => 0 := by
      ext x
      unfold exactAbelianField
      rw [if_neg h_mu]
      rfl
    rw [h_eval]
    exact contDiff_const

lemma covariant_zero_field (mu rho nu : Fin 4) (x : SpacetimePoint) :
  covariantDeriv (fun _ _ => (0 : SL2C)) mu rho nu x = 0 := by
  unfold covariantDeriv
  have hF_eval : curvatureSl2c (fun _ _ => (0 : SL2C)) rho nu x = 0 := by
    unfold curvatureSl2c
    rw [partialDerivSl2c_const (0 : SL2C) rho x, partialDerivSl2c_const (0 : SL2C) nu x]
    have h_comm : ⁅(0 : SL2C), (0 : SL2C)⁆ = 0 := bracket_zero_left (0 : SL2C)
    rw [h_comm]
    apply Subtype.ext
    change (0 : Matrix (Fin 2) (Fin 2) ℂ) - (0 : Matrix (Fin 2) (Fin 2) ℂ) + (0 : Matrix (Fin 2) (Fin 2) ℂ) = (0 : Matrix (Fin 2) (Fin 2) ℂ)
    simp
    
  have hd : partialDerivSl2c mu (fun p => curvatureSl2c (fun _ _ => (0 : SL2C)) rho nu p) x = 0 := by
    have hF : (fun p => curvatureSl2c (fun _ _ => (0 : SL2C)) rho nu p) = (fun _ => (0 : SL2C)) := by
      funext p
      unfold curvatureSl2c
      rw [partialDerivSl2c_const (0 : SL2C) rho p, partialDerivSl2c_const (0 : SL2C) nu p]
      have h_comm : ⁅(0 : SL2C), (0 : SL2C)⁆ = 0 := bracket_zero_left (0 : SL2C)
      rw [h_comm]
      apply Subtype.ext
      change (0 : Matrix (Fin 2) (Fin 2) ℂ) - (0 : Matrix (Fin 2) (Fin 2) ℂ) + (0 : Matrix (Fin 2) (Fin 2) ℂ) = (0 : Matrix (Fin 2) (Fin 2) ℂ)
      simp
    rw [hF]
    exact partialDerivSl2c_const (0 : SL2C) mu x
    
  change partialDerivSl2c mu (fun p => curvatureSl2c (fun _ _ => (0 : SL2C)) rho nu p) x + ⁅(0 : SL2C), curvatureSl2c (fun _ _ => (0 : SL2C)) rho nu x⁆ = 0
  
  have h_comm2 : ⁅(0 : SL2C), (0 : SL2C)⁆ = 0 := bracket_zero_left (0 : SL2C)
  rw [hd, hF_eval, h_comm2]
  apply Subtype.ext
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) + (0 : Matrix (Fin 2) (Fin 2) ℂ) = (0 : Matrix (Fin 2) (Fin 2) ℂ)
  simp

lemma asd_sector_zero_val : (0 : Sl2cGaugeField).val = fun _ _ => 0 := rfl

lemma smul_sigmaX_eq_zero_iff (c : ℂ) : c • toSl2c sigmaX = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h_val_eq : (c • toSl2c sigmaX).val = 0 := congr_arg Subtype.val h
    have h_sx : (toSl2c sigmaX).val = sigmaX := by
      change sigmaX - (Matrix.trace sigmaX / 2) • 1 = sigmaX
      have h_tr : Matrix.trace sigmaX = 0 := by unfold sigmaX mkMat Matrix.trace Matrix.diag; rw [Fin.sum_univ_two]; change (0:ℂ)+0=0; ring
      rw [h_tr]
      have hz : (0:ℂ)/2=0 := zero_div 2
      rw [hz]
      have hsmul : (0:ℂ)•(1:Matrix (Fin 2) (Fin 2) ℂ)=0 := zero_smul _ _
      rw [hsmul]
      exact sub_zero _
    have h_eval : (c • toSl2c sigmaX).val 0 1 = 0 := by rw [h_val_eq]; rfl
    have h_eval2 : c * (toSl2c sigmaX).val 0 1 = 0 := h_eval
    rw [h_sx] at h_eval2
    have h_sx01 : sigmaX 0 1 = 1 := rfl
    rw [h_sx01, mul_one] at h_eval2
    exact h_eval2
  · intro h
    rw [h]
    exact zero_smul ℂ _

lemma toSl2c_smul_complex (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
  toSl2c (c • M) = c • toSl2c M := by
  apply Subtype.ext
  change (c • M) - (Matrix.trace (c • M) / 2) • 1 = c • (M - (Matrix.trace M / 2) • 1)
  rw [Matrix.trace_smul]
  ext i j
  change c * M i j - (c * Matrix.trace M / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j = c * (M i j - (Matrix.trace M / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j)
  ring

theorem dynamicExactAbelianSolution (c : ℂ) (hc : c ≠ 0) :
  ∃ (u : Universe), 
    eulerLagrangePDEs u ∧ 
    (∀ x, curvatureSl2c u.sd_sector 1 2 x = c • toSl2c sigmaX) ∧
    (∃ x, curvatureSl2c u.sd_sector 1 2 x ≠ 0) := by
  let u := Universe.mk 
    (Sl2cGaugeField.mk (exactAbelianField c) (exactAbelianField_smooth c))
    (0 : Sl2cGaugeField)
  use u
  constructor
  · dsimp [eulerLagrangePDEs]
    constructor
    · intro nu x
      have h_cov : ∀ mu rho, covariantDeriv u.sd_sector mu rho nu x = 0 := by
        intros mu rho
        change covariantDeriv (exactAbelianField c) mu rho nu x = 0
        exact covariant_exact_zero c mu rho nu x
      have h_cov_val : ∀ mu rho, (covariantDeriv u.sd_sector mu rho nu x).val = 0 := by intros mu rho; rw [h_cov mu rho]; rfl
      have h_sum : (∑ mu : Fin 4, ∑ rho : Fin 4, (eta mu rho : ℂ) • (covariantDeriv u.sd_sector mu rho nu x).val) = 
                   (∑ mu : Fin 4, ∑ rho : Fin 4, (eta mu rho : ℂ) • (0 : Matrix (Fin 2) (Fin 2) ℂ)) := by
        apply Finset.sum_congr rfl; intro mu _; apply Finset.sum_congr rfl; intro rho _; rw [h_cov_val mu rho]
      rw [h_sum]
      have h_zero : ∀ mu rho, (eta mu rho : ℂ) • (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := fun mu rho => smul_zero _
      have h_sum2 : (∑ mu : Fin 4, ∑ rho : Fin 4, (eta mu rho : ℂ) • (0 : Matrix (Fin 2) (Fin 2) ℂ)) = 
                    (∑ mu : Fin 4, ∑ rho : Fin 4, (0 : Matrix (Fin 2) (Fin 2) ℂ)) := by
        apply Finset.sum_congr rfl; intro mu _; apply Finset.sum_congr rfl; intro rho _; rw [h_zero mu rho]
      rw [h_sum2]
      exact Finset.sum_eq_zero (fun mu _ => Finset.sum_eq_zero (fun rho _ => rfl))
    · intro nu x
      have h_asd : u.asd_sector.val = fun _ _ => 0 := asd_sector_zero_val
      have h_cov : ∀ mu rho, covariantDeriv u.asd_sector mu rho nu x = 0 := by
        intros mu rho
        have h_cov_eval : covariantDeriv u.asd_sector mu rho nu x = covariantDeriv u.asd_sector.val mu rho nu x := rfl
        rw [h_cov_eval, h_asd]
        exact covariant_zero_field mu rho nu x
      have h_cov_val : ∀ mu rho, (covariantDeriv u.asd_sector mu rho nu x).val = 0 := by intros mu rho; rw [h_cov mu rho]; rfl
      have h_sum : (∑ mu : Fin 4, ∑ rho : Fin 4, (eta mu rho : ℂ) • (covariantDeriv u.asd_sector mu rho nu x).val) = 
                   (∑ mu : Fin 4, ∑ rho : Fin 4, (eta mu rho : ℂ) • (0 : Matrix (Fin 2) (Fin 2) ℂ)) := by
        apply Finset.sum_congr rfl; intro mu _; apply Finset.sum_congr rfl; intro rho _; rw [h_cov_val mu rho]
      rw [h_sum]
      have h_zero : ∀ mu rho, (eta mu rho : ℂ) • (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := fun mu rho => smul_zero _
      have h_sum2 : (∑ mu : Fin 4, ∑ rho : Fin 4, (eta mu rho : ℂ) • (0 : Matrix (Fin 2) (Fin 2) ℂ)) = 
                    (∑ mu : Fin 4, ∑ rho : Fin 4, (0 : Matrix (Fin 2) (Fin 2) ℂ)) := by
        apply Finset.sum_congr rfl; intro mu _; apply Finset.sum_congr rfl; intro rho _; rw [h_zero mu rho]
      rw [h_sum2]
      exact Finset.sum_eq_zero (fun mu _ => Finset.sum_eq_zero (fun rho _ => rfl))
  · constructor
    · intro x
      change curvatureSl2c (exactAbelianField c) 1 2 x = c • toSl2c sigmaX
      have h12 : (1 : Fin 4) = 1 ∧ (2 : Fin 4) = 2 := ⟨rfl, rfl⟩
      rw [curvature_exact_eq_const c 1 2 x]
      unfold curvature_const
      rw [if_pos h12, toSl2c_smul_complex]
    · use (fun _ => 0)
      change curvatureSl2c (exactAbelianField c) 1 2 (fun _ => 0) ≠ 0
      have h12 : (1 : Fin 4) = 1 ∧ (2 : Fin 4) = 2 := ⟨rfl, rfl⟩
      rw [curvature_exact_eq_const c 1 2 (fun _ => 0)]
      unfold curvature_const
      rw [if_pos h12]
      intro h_eq
      have h_eq2 : c • toSl2c sigmaX = 0 := by
        rw [toSl2c_smul_complex] at h_eq
        exact h_eq
      have h_c_zero : c = 0 := (smul_sigmaX_eq_zero_iff c).mp h_eq2
      exact hc h_c_zero

end CGD.Quantum

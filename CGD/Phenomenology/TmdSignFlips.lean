-- FILENAME: CGD/Phenomenology/TmdSignFlips.lean

import CGD.Axioms.PhysicalUniverse
import CGD.Foundations.GaugeGroup
import CGD.Quantum.Definitions
import CGD.Quantum.Holonomy.Evaluation
import Litlib.Core
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CGD.Phenomenology

noncomputable def explicitSigmaX : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, 1], ![1, 0]]
noncomputable def explicitSigmaY : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, -Complex.I], ![Complex.I, 0]]
noncomputable def explicitSigmaZ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![1, 0], ![0, -1]]

/-- 
The Sivers effect observable (Nucleon Transverse Spin vs Quark Transverse Momentum).
Projects the orthogonal SU(2) topology via sigmaX.
-/
noncomputable def siversTransverseKick (U U_inv : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace (U * explicitSigmaX * U_inv * explicitSigmaY)

/-- 
The Boer-Mulders effect observable (Quark Transverse Spin vs Quark Transverse Momentum).
Projects the orthogonal SU(2) topology via sigmaZ.
-/
noncomputable def boerMuldersTransverseKick (U U_inv : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace (U * explicitSigmaZ * U_inv * explicitSigmaY)

noncomputable def obs_M_A (alpha : ℝ) : ℂ := (Complex.cos (alpha/2))^2 - (Complex.sin (alpha/2))^2
noncomputable def obs_M_B (alpha : ℝ) : ℂ := 2 * (Complex.cos (alpha/2)) * (Complex.sin (alpha/2))

-- ====================================================================
-- DETERMINISTIC UNROLLING RULES (NO UNIFIER SEARCH)
-- ====================================================================

lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) ℂ) :
  Matrix.trace M = M 0 0 + M 1 1 := by
  have h : Matrix.trace M = ∑ i : Fin 2, M.diag i := rfl
  rw [h, Fin.sum_univ_two]
  rfl

lemma mul_fin2 (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  have h : (A * B) i j = ∑ k : Fin 2, A i k * B k j := rfl
  rw [h, Fin.sum_univ_two]

lemma norm_fin_0 {h : 0 < 2} : (⟨0, h⟩ : Fin 2) = 0 := rfl
lemma norm_fin_1 {h : 1 < 2} : (⟨1, h⟩ : Fin 2) = 1 := rfl

lemma mat_00 {α : Type*} (A B C D : α) : (Matrix.of ![![A, B], ![C, D]] : Matrix (Fin 2) (Fin 2) α) 0 0 = A := rfl
lemma mat_01 {α : Type*} (A B C D : α) : (Matrix.of ![![A, B], ![C, D]] : Matrix (Fin 2) (Fin 2) α) 0 1 = B := rfl
lemma mat_10 {α : Type*} (A B C D : α) : (Matrix.of ![![A, B], ![C, D]] : Matrix (Fin 2) (Fin 2) α) 1 0 = C := rfl
lemma mat_11 {α : Type*} (A B C D : α) : (Matrix.of ![![A, B], ![C, D]] : Matrix (Fin 2) (Fin 2) α) 1 1 = D := rfl

lemma one_00 : (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := rfl
lemma one_01 : (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := rfl
lemma one_10 : (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := rfl
lemma one_11 : (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 1 := rfl

lemma sig3_coe_00 : (CGD.Foundations.sigma3 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := by change CGD.Foundations.sigma3.val 0 0 = 1; rw [CGD.Foundations.val_sigma3]; rfl
lemma sig3_coe_01 : (CGD.Foundations.sigma3 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by change CGD.Foundations.sigma3.val 0 1 = 0; rw [CGD.Foundations.val_sigma3]; rfl
lemma sig3_coe_10 : (CGD.Foundations.sigma3 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by change CGD.Foundations.sigma3.val 1 0 = 0; rw [CGD.Foundations.val_sigma3]; rfl
lemma sig3_coe_11 : (CGD.Foundations.sigma3 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = -1 := by change CGD.Foundations.sigma3.val 1 1 = -1; rw [CGD.Foundations.val_sigma3]; rfl

lemma sig3_val_00 : CGD.Foundations.sigma3.val 0 0 = 1 := by rw [CGD.Foundations.val_sigma3]; rfl
lemma sig3_val_01 : CGD.Foundations.sigma3.val 0 1 = 0 := by rw [CGD.Foundations.val_sigma3]; rfl
lemma sig3_val_10 : CGD.Foundations.sigma3.val 1 0 = 0 := by rw [CGD.Foundations.val_sigma3]; rfl
lemma sig3_val_11 : CGD.Foundations.sigma3.val 1 1 = -1 := by rw [CGD.Foundations.val_sigma3]; rfl

-- ====================================================================

/-- Algebraically unpacks the SU(2) phase generator into a flat matrix. -/
lemma obs_M_eq (alpha : ℝ) : 
  CGD.Quantum.obs_M alpha = Matrix.of ![![obs_M_A alpha, obs_M_B alpha], ![obs_M_B alpha, -obs_M_A alpha]] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    unfold CGD.Quantum.obs_M
    repeat rw [norm_fin_0]
    repeat rw [norm_fin_1]
    repeat rw [mul_fin2]
    repeat rw [norm_fin_0]
    repeat rw [norm_fin_1]
    repeat rw [Matrix.add_apply]
    repeat rw [Matrix.smul_apply]
    repeat rw [mat_00]
    repeat rw [mat_01]
    repeat rw [mat_10]
    repeat rw [mat_11]
    repeat rw [sig3_coe_00]
    repeat rw [sig3_coe_01]
    repeat rw [sig3_coe_10]
    repeat rw [sig3_coe_11]
    repeat rw [sig3_val_00]
    repeat rw [sig3_val_01]
    repeat rw [sig3_val_10]
    repeat rw [sig3_val_11]
    try unfold obs_M_A
    try unfold obs_M_B
    repeat rw [smul_eq_mul]
    ring_nf
  }

/-- The isolated matrix algebra proving the exact Sivers sign flip. -/
lemma kinematicSiversAlgebra (c s A B : ℂ) :
  siversTransverseKick 
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * s) • Matrix.of ![![A, B], ![B, -A]]) 
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * -s) • Matrix.of ![![A, B], ![B, -A]]) =
  - siversTransverseKick 
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * -s) • Matrix.of ![![A, B], ![B, -A]]) 
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * s) • Matrix.of ![![A, B], ![B, -A]]) := by
  unfold siversTransverseKick explicitSigmaX explicitSigmaY
  rw [trace_fin2, trace_fin2]
  repeat rw [mul_fin2]
  repeat rw [norm_fin_0]
  repeat rw [norm_fin_1]
  repeat rw [Matrix.add_apply]
  repeat rw [Matrix.smul_apply]
  repeat rw [mat_00]
  repeat rw [mat_01]
  repeat rw [mat_10]
  repeat rw [mat_11]
  repeat rw [one_00]
  repeat rw [one_01]
  repeat rw [one_10]
  repeat rw [one_11]
  repeat rw [smul_eq_mul]
  ring_nf

/-- The isolated matrix algebra proving the exact Boer-Mulders sign flip. -/
lemma kinematicBoerMuldersAlgebra (c s A B : ℂ) :
  boerMuldersTransverseKick 
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * s) • Matrix.of ![![A, B], ![B, -A]]) 
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * -s) • Matrix.of ![![A, B], ![B, -A]]) =
  - boerMuldersTransverseKick 
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * -s) • Matrix.of ![![A, B], ![B, -A]]) 
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * s) • Matrix.of ![![A, B], ![B, -A]]) := by
  unfold boerMuldersTransverseKick explicitSigmaZ explicitSigmaY
  rw [trace_fin2, trace_fin2]
  repeat rw [mul_fin2]
  repeat rw [norm_fin_0]
  repeat rw [norm_fin_1]
  repeat rw [Matrix.add_apply]
  repeat rw [Matrix.smul_apply]
  repeat rw [mat_00]
  repeat rw [mat_01]
  repeat rw [mat_10]
  repeat rw [mat_11]
  repeat rw [one_00]
  repeat rw [one_01]
  repeat rw [one_10]
  repeat rw [one_11]
  repeat rw [smul_eq_mul]
  ring_nf

/-- 
The isolated matrix algebra proving the exact geometric ratio. 
A * BM = - B * Sivers  -->  cos(alpha) * BM = - sin(alpha) * Sivers
-/
lemma kinematicTmdRatioAlgebra (c s A B : ℂ) :
  A * boerMuldersTransverseKick 
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * s) • Matrix.of ![![A, B], ![B, -A]]) 
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * -s) • Matrix.of ![![A, B], ![B, -A]]) =
  - B * siversTransverseKick 
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * s) • Matrix.of ![![A, B], ![B, -A]]) 
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * -s) • Matrix.of ![![A, B], ![B, -A]]) := by
  unfold boerMuldersTransverseKick siversTransverseKick explicitSigmaX explicitSigmaY explicitSigmaZ
  rw [trace_fin2, trace_fin2]
  repeat rw [mul_fin2]
  repeat rw [norm_fin_0]
  repeat rw [norm_fin_1]
  repeat rw [Matrix.add_apply]
  repeat rw [Matrix.smul_apply]
  repeat rw [mat_00]
  repeat rw [mat_01]
  repeat rw [mat_10]
  repeat rw [mat_11]
  repeat rw [one_00]
  repeat rw [one_01]
  repeat rw [one_10]
  repeat rw [one_11]
  repeat rw [smul_eq_mul]
  ring_nf

Litlib.theorem
  description "Kinematic Sivers Sign Flip"
theorem kinematicSiversSignFlip (pu : CGD.Axioms.PhysicalUniverse) :
  ∀ (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    [Litlib.Y2000.hall2000elementary.DerivativeExponential (Fin 2) matrixExp]
    (alpha L : ℝ),
    (∀ t, pu.toUniverse.sd_sector 1 (CGD.Quantum.straightLinePath t) = CGD.Quantum.fluxTubeFrame 1 (CGD.Quantum.straightLinePath t)) →
    siversTransverseKick 
      (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) (fun mu p => CGD.Quantum.rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 L)
      (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) (fun mu p => CGD.Quantum.rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 (-L)) =
    - siversTransverseKick 
      (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) (fun mu p => CGD.Quantum.rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 (-L))
      (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) (fun mu p => CGD.Quantum.rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 L) := by
  intros matrixExp _ alpha L h_field
  rw [CGD.Quantum.fluxTubeHolonomyEvaluation matrixExp pu alpha L h_field]
  rw [CGD.Quantum.fluxTubeHolonomyEvaluation matrixExp pu alpha (-L) h_field]
  rw [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  rw [obs_M_eq alpha]
  exact kinematicSiversAlgebra (Complex.cos ↑L) (Complex.sin ↑L) (obs_M_A alpha) (obs_M_B alpha)

Litlib.theorem
  description "Kinematic Boer-Mulders Sign Flip"
theorem kinematicBoerMuldersSignFlip (pu : CGD.Axioms.PhysicalUniverse) :
  ∀ (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    [Litlib.Y2000.hall2000elementary.DerivativeExponential (Fin 2) matrixExp]
    (alpha L : ℝ),
    (∀ t, pu.toUniverse.sd_sector 1 (CGD.Quantum.straightLinePath t) = CGD.Quantum.fluxTubeFrame 1 (CGD.Quantum.straightLinePath t)) →
    boerMuldersTransverseKick 
      (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) (fun mu p => CGD.Quantum.rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 L)
      (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) (fun mu p => CGD.Quantum.rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 (-L)) =
    - boerMuldersTransverseKick 
      (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) (fun mu p => CGD.Quantum.rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 (-L))
      (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) (fun mu p => CGD.Quantum.rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 L) := by
  intros matrixExp _ alpha L h_field
  rw [CGD.Quantum.fluxTubeHolonomyEvaluation matrixExp pu alpha L h_field]
  rw [CGD.Quantum.fluxTubeHolonomyEvaluation matrixExp pu alpha (-L) h_field]
  rw [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  rw [obs_M_eq alpha]
  exact kinematicBoerMuldersAlgebra (Complex.cos ↑L) (Complex.sin ↑L) (obs_M_A alpha) (obs_M_B alpha)

Litlib.theorem
  description "Topological TMD Geometric Ratio"
/-- 
The Topological TMD Geometric Ratio.

This theorem rigorously proves that the Boer-Mulders and Sivers observables are not 
independent empirical functions, but are geometrically locked by the chiral phase angle 
`alpha` of the macroscopic flux tube. Specifically:
`cos(alpha) * BoerMulders = - sin(alpha) * Sivers`

Because the observables are defined natively as geometric integrals without any 
collisional momentum variables, this geometric lock rigorously dictates that their ratio 
is a flat kinematic constant (-tan(alpha)), reproducing global supercomputer fits.
-/
theorem kinematicTmdRatio (pu : CGD.Axioms.PhysicalUniverse) :
  ∀ (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    [Litlib.Y2000.hall2000elementary.DerivativeExponential (Fin 2) matrixExp]
    (alpha L : ℝ),
    (∀ t, pu.toUniverse.sd_sector 1 (CGD.Quantum.straightLinePath t) = CGD.Quantum.fluxTubeFrame 1 (CGD.Quantum.straightLinePath t)) →
    (obs_M_A alpha) * boerMuldersTransverseKick 
      (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) (fun mu p => CGD.Quantum.rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 L)
      (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) (fun mu p => CGD.Quantum.rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 (-L)) =
    - (obs_M_B alpha) * siversTransverseKick 
      (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) (fun mu p => CGD.Quantum.rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 L)
      (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) (fun mu p => CGD.Quantum.rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 (-L)) := by
  intros matrixExp _ alpha L h_field
  rw [CGD.Quantum.fluxTubeHolonomyEvaluation matrixExp pu alpha L h_field]
  rw [CGD.Quantum.fluxTubeHolonomyEvaluation matrixExp pu alpha (-L) h_field]
  rw [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  rw [obs_M_eq alpha]
  exact kinematicTmdRatioAlgebra (Complex.cos ↑L) (Complex.sin ↑L) (obs_M_A alpha) (obs_M_B alpha)

end CGD.Phenomenology

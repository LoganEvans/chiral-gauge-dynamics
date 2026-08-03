-- FILENAME: CGD/Phenomenology/TMD/Algebra.lean

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import CGD.Foundations.GaugeGroup
import CGD.Quantum.Holonomy.Evaluation

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CGD.Phenomenology.TMD

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
Projects the orthogonal SU(2) topology via sigmaX.
Geometrically identical to the Sivers projection.
-/
noncomputable def boerMuldersTransverseKick (U U_inv : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace (U * explicitSigmaX * U_inv * explicitSigmaY)

/--
The Worm-Gear effect observable (Quark Longitudinal Spin vs Quark Transverse Momentum).
Projects the orthogonal SU(2) topology via sigmaZ.
-/
noncomputable def wormGearTransverseKick (U U_inv : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace (U * explicitSigmaZ * U_inv * explicitSigmaY)

noncomputable def obsM_A (alpha : ℝ) : ℂ := (Complex.cos (alpha/2))^2 - (Complex.sin (alpha/2))^2
noncomputable def obsM_B (alpha : ℝ) : ℂ := 2 * (Complex.cos (alpha/2)) * (Complex.sin (alpha/2))

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
lemma obsM_eq (alpha : ℝ) :
  CGD.Quantum.obsM alpha = Matrix.of ![![obsM_A alpha, obsM_B alpha], ![obsM_B alpha, -obsM_A alpha]] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    unfold CGD.Quantum.obsM
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
    try unfold obsM_A
    try unfold obsM_B
    repeat rw [smul_eq_mul]
    ring_nf
  }

/-- The isolated matrix algebra proving the exact Sivers sign flip. -/
lemma geometricSiversAlgebra (c s A B : ℂ) :
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

/-- The isolated matrix algebra proving the exact Worm-Gear sign flip. -/
lemma geometricWormGearAlgebra (c s A B : ℂ) :
  wormGearTransverseKick
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * s) • Matrix.of ![![A, B], ![B, -A]])
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * -s) • Matrix.of ![![A, B], ![B, -A]]) =
  - wormGearTransverseKick
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * -s) • Matrix.of ![![A, B], ![B, -A]])
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * s) • Matrix.of ![![A, B], ![B, -A]]) := by
  unfold wormGearTransverseKick explicitSigmaZ explicitSigmaY
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
A * WormGear = - B * Sivers  -->  cos(alpha) * WormGear = - sin(alpha) * Sivers
-/
lemma geometricTmdRatioAlgebra (c s A B : ℂ) :
  A * wormGearTransverseKick
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * s) • Matrix.of ![![A, B], ![B, -A]])
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * -s) • Matrix.of ![![A, B], ![B, -A]]) =
  - B * siversTransverseKick
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * s) • Matrix.of ![![A, B], ![B, -A]])
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * -s) • Matrix.of ![![A, B], ![B, -A]]) := by
  unfold wormGearTransverseKick siversTransverseKick explicitSigmaX explicitSigmaY explicitSigmaZ
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

end CGD.Phenomenology.TMD

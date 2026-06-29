-- FILENAME: CGD/Phenomenology/SiversEffect.lean

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

/-- 
The physical transverse momentum kick observable.
We evaluate the momentum projection orthogonally to both the beam and the spin.
-/
noncomputable def siversTransverseKick (U U_inv : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace (U * explicitSigmaX * U_inv * explicitSigmaY)

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
    ring_nf
  }

/-- 
The isolated matrix algebra proving the exact topological sign flip.
We explicitly unroll the trace and multiplication natively.
-/
lemma kinematicSiversAlgebra (c s A B : ℂ) :
  let M := Matrix.of ![![A, B], ![B, -A]];
  let U_fwd := c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * s) • M;
  let U_rev := c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * -s) • M;
  siversTransverseKick U_fwd U_rev = - siversTransverseKick U_rev U_fwd := by
  intros M U_fwd U_rev
  unfold siversTransverseKick
  rw [trace_fin2, trace_fin2]
  repeat rw [mul_fin2]
  try unfold U_fwd U_rev M explicitSigmaX explicitSigmaY
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
  ring_nf

Litlib.theorem
  description "Kinematic Sivers Sign Flip"
/-- 
The Kinematic Sivers Sign Flip.

In standard perturbative QCD, the Sivers sign flip is phenomenologically derived by 
inserting gauge links via the Factorization Theorem, which inherently obscures the 
topological origin of the asymmetry.

In the Chiral Gauge Dynamics (CGD) framework, the emergent matter defect is bridged 
by a continuous topological flux tube. Because this background field is spatially 
uniform along the integration path, the field trivially commutes with itself at all 
points ($[A(z_1), A(z_2)] = 0$). Consequently, the continuous path-ordered integration 
(the Wilson line) collapses into the exact analytic matrix exponential $\exp(L \cdot A)$. 

This theorem demonstrates that the fundamental unbroken topology of the universe natively 
forces the transverse momentum observable to exactly invert its sign when the kinematic 
path is reversed from an outgoing (SIDIS, length $L$) to an incoming (Drell-Yan, length $-L$) 
trajectory.
-/
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
  
  -- Evaluate the physical universe observable into the raw SU(2) matrix states
  rw [CGD.Quantum.fluxTubeHolonomyEvaluation matrixExp pu alpha L h_field]
  rw [CGD.Quantum.fluxTubeHolonomyEvaluation matrixExp pu alpha (-L) h_field]
  
  -- Extract the spatial parity inversion into the trigonometric coefficients
  rw [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  
  -- Expand the generator matrix
  rw [obs_M_eq alpha]
  
  -- Route to the strict, unrolled scalar algebra
  exact kinematicSiversAlgebra (Complex.cos ↑L) (Complex.sin ↑L) (obs_M_A alpha) (obs_M_B alpha)

end CGD.Phenomenology

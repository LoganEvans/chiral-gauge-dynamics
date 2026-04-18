-- FILENAME: CGD/Quantum/Entanglement.lean

import Litlib.Y2001.bali2001qcd.Signature
import CGD.Quantum.Definitions
import CGD.Quantum.FluxTube
import CGD.Gravity.Geometry
import CGD.Foundations.TensorCalculus
import CGD.Foundations.Calculus
import CGD.Axioms.Ontology
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

set_option linter.unusedVariables false

open CGD.Foundations CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms Litlib.Y2001.bali2001qcd

namespace CGD.Quantum

-- Eradicated Trapdoors: These are now uninterpreted abstract variables constrained by Litlib Axioms
variable (spatialEnergy : (Fin 4 → SpacetimePoint → SL2C) → ℝ)
variable (intactFluxTube snappedFluxTube : ℝ → Fin 4 → SpacetimePoint → SL2C)

def isGlobalMinimum {α : Type*} (Energy : α → ℝ) (state : α) : Prop :=
  ∀ (other : α), Energy state ≤ Energy other

/-- 🟢 PREDICTION TARGET: Hamiltonian Crossover. 
Rigorously backed by the true Litlib macroscopic string bounds. -/
theorem kinematicHamiltonianCrossover {sigma M : ℝ} [eb : FluxTubeEnergyBounds (Fin 4 → SpacetimePoint → SL2C) spatialEnergy intactFluxTube snappedFluxTube sigma M]
  (L : ℝ) (h_sigma : sigma > 0) (h_L : L > (2 * M) / sigma) :
  spatialEnergy (intactFluxTube L) > spatialEnergy (snappedFluxTube L) := by
  rw [eb.intactEnergy L, eb.snappedEnergy L]
  have h_neq : sigma ≠ 0 := by linarith
  have h_div : (2 * M / sigma) * sigma = 2 * M := div_mul_cancel₀ (2 * M) h_neq
  have h_mul : (2 * M / sigma) * sigma < L * sigma := mul_lt_mul_of_pos_right h_L h_sigma
  rw [h_div] at h_mul
  have h_comm : L * sigma = sigma * L := mul_comm L sigma
  rw [h_comm] at h_mul
  exact h_mul

/-- 🟢 PREDICTION TARGET: The Death of Entanglement. -/
theorem dynamicEntanglementDecay {sigma M : ℝ} [eb : FluxTubeEnergyBounds (Fin 4 → SpacetimePoint → SL2C) spatialEnergy intactFluxTube snappedFluxTube sigma M]
  (L : ℝ) (h_sigma : sigma > 0) (h_L : L > (2 * M) / sigma) :
  ¬ isGlobalMinimum spatialEnergy (intactFluxTube L) := by
  intro h_min; unfold isGlobalMinimum at h_min
  have h_le := h_min (snappedFluxTube L)
  have h_lt := kinematicHamiltonianCrossover spatialEnergy intactFluxTube snappedFluxTube L h_sigma h_L
  linarith

private lemma to_sl2c_zero : toSl2c 0 = 0 := by
  apply Subtype.ext
  unfold toSl2c
  dsimp
  have h_tr : Matrix.trace (0 : Matrix (Fin 2) (Fin 2) Complex) = 0 := by simp[Matrix.trace]
  rw[h_tr]
  have h1 : (0 : ℂ) / 2 = 0 := by ring
  rw[h1, zero_smul, sub_zero]

lemma diff_ofReal_entanglement : Differentiable ℝ (fun z : ℝ => (z : ℂ)) := by
  intro z
  have h1 := hasDerivAt_id z
  have h2 := HasDerivAt.smul_const h1 (1 : ℂ)
  have eq1 : (fun (y : ℝ) => id y • (1 : ℂ)) = fun (s : ℝ) => (s : ℂ) := by ext x; simp
  have eq2 : (1 : ℝ) • (1 : ℂ) = 1 := by simp
  rw [eq1, eq2] at h2
  exact h2.differentiableAt

lemma diff_rotated_fluxTube_comp (C : ℝ) (sigma_A sigma_B : Matrix (Fin 2) (Fin 2) ℂ) :
  ∀ i j, Differentiable ℝ (fun z : ℝ => ((Complex.cos (C:ℂ)) • ((Complex.I * (z:ℂ)) • sigma_A) + (Complex.I * Complex.sin (C:ℂ) * (z:ℂ)) • sigma_B) i j) := by
  intro i j
  have h : (fun z : ℝ => ((Complex.cos (C:ℂ)) • ((Complex.I * (z:ℂ)) • sigma_A) + (Complex.I * Complex.sin (C:ℂ) * (z:ℂ)) • sigma_B) i j) =
           fun z : ℝ => (Complex.cos (C:ℂ) * Complex.I * sigma_A i j) * (z : ℂ) + (Complex.I * Complex.sin (C:ℂ) * sigma_B i j) * (z : ℂ) := by
    ext z; simp [Matrix.add_apply, Matrix.smul_apply]; ring
  rw [h]
  apply Differentiable.add
  · apply Differentiable.mul
    · exact differentiable_const _
    · exact diff_ofReal_entanglement
  · apply Differentiable.mul
    · exact differentiable_const _
    · exact diff_ofReal_entanglement

lemma math_partialDerivMat_rotate_fluxTube_time_0 (C : ℝ) (x : SpacetimePoint) : partialDerivMat 0 (fun p => (rotateZ fluxTubeFrame C 0 p).val) x = 0 := by
  have h0 : (fun p => (rotateZ fluxTubeFrame C 0 p).val) = fun _ => 0 := by ext p; rfl
  rw [h0]; exact partialDerivMat_const 0 0 x

lemma math_partialDerivMat_rotate_fluxTube_time_1 (C : ℝ) (x : SpacetimePoint) : partialDerivMat 0 (fun p => (rotateZ fluxTubeFrame C 1 p).val) x = 0 := by
  have h_neq : (0 : Fin 4) ≠ 1 := by decide
  have h1 : (fun p => (rotateZ fluxTubeFrame C 1 p).val) = fun p => (fun z : ℝ => (Complex.cos (C : ℂ)) • ((Complex.I * (z : ℂ)) • sigma2.val) + (Complex.I * Complex.sin (C : ℂ) * (z : ℂ)) • sigma1.val) (p 1) := by
    ext p; unfold rotateZ fluxTubeFrame; simp
  rw [h1]; exact math_partialDerivMat_comp_coord (fun z : ℝ => (Complex.cos (C : ℂ)) • ((Complex.I * (z : ℂ)) • sigma2.val) + (Complex.I * Complex.sin (C : ℂ) * (z : ℂ)) • sigma1.val) 1 0 h_neq x (diff_rotated_fluxTube_comp C sigma2.val sigma1.val)

lemma math_partialDerivMat_rotate_fluxTube_time_2 (C : ℝ) (x : SpacetimePoint) : partialDerivMat 0 (fun p => (rotateZ fluxTubeFrame C 2 p).val) x = 0 := by
  have h_neq : (0 : Fin 4) ≠ 1 := by decide
  have h2 : (fun p => (rotateZ fluxTubeFrame C 2 p).val) = fun p => (fun z : ℝ => (Complex.I * (z : ℂ)) • sigma2.val) (p 1) := by
    ext p; unfold rotateZ fluxTubeFrame; simp
  rw [h2]; exact math_partialDerivMat_comp_coord (fun z : ℝ => (Complex.I * (z : ℂ)) • sigma2.val) 1 0 h_neq x (diff_fluxTube_comp sigma2.val)

lemma math_partialDerivMat_rotate_fluxTube_time_3 (C : ℝ) (x : SpacetimePoint) : partialDerivMat 0 (fun p => (rotateZ fluxTubeFrame C 3 p).val) x = 0 := by
  have h_neq : (0 : Fin 4) ≠ 1 := by decide
  have h3 : (fun p => (rotateZ fluxTubeFrame C 3 p).val) = fun p => (fun z : ℝ => (Complex.I * (z : ℂ)) • sigma3.val) (p 1) := by
    ext p; unfold rotateZ fluxTubeFrame; simp
  rw [h3]; exact math_partialDerivMat_comp_coord (fun z : ℝ => (Complex.I * (z : ℂ)) • sigma3.val) 1 0 h_neq x (diff_fluxTube_comp sigma3.val)

lemma math_rotated_flux_tube_time_deriv (C : ℝ) (nu : Fin 4) (x : SpacetimePoint) :
  partialDerivSl2c 0 (rotateZ fluxTubeFrame C nu) x = 0 := by
  unfold partialDerivSl2c
  have h_val : partialDerivMat 0 (fun p => (rotateZ fluxTubeFrame C nu p).val) x = 0 := by
    fin_cases nu
    · exact math_partialDerivMat_rotate_fluxTube_time_0 C x
    · exact math_partialDerivMat_rotate_fluxTube_time_1 C x
    · exact math_partialDerivMat_rotate_fluxTube_time_2 C x
    · exact math_partialDerivMat_rotate_fluxTube_time_3 C x
  rw [h_val]
  apply Subtype.ext
  unfold toSl2c
  dsimp
  have ht : Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by simp[Matrix.trace]
  rw [ht]
  have hz : (0:ℂ) / 2 = 0 := by ring
  rw [hz, zero_smul, sub_zero]

lemma math_rotated_flux_tube_cross_deriv (C : ℝ) (nu : Fin 4) (x : SpacetimePoint) :
  partialDerivSl2c nu (rotateZ fluxTubeFrame C 0) x = 0 := by
  have h_zero : rotateZ fluxTubeFrame C 0 = fun _ => 0 := by ext p; rfl
  rw [h_zero]
  exact partialDerivSl2c_const 0 nu x

lemma rotated_flux_tube_electric_zero (C : ℝ) (nu : Fin 4) (x : SpacetimePoint) :
  curvatureSl2c (rotateZ fluxTubeFrame C) 0 nu x = 0 := by
  unfold curvatureSl2c
  rw[math_rotated_flux_tube_time_deriv C nu x, math_rotated_flux_tube_cross_deriv C nu x]
  have h_frame_0 : rotateZ fluxTubeFrame C 0 x = 0 := rfl
  rw [h_frame_0]
  have h_bracket : ⁅(0 : SL2C), rotateZ fluxTubeFrame C nu x⁆ = 0 := by 
    apply Subtype.ext
    change (0 : Matrix (Fin 2) (Fin 2) ℂ) * _ - _ * 0 = 0
    simp
  rw [h_bracket]
  change (0 : SL2C) - (0 : SL2C) + (0 : SL2C) = (0 : SL2C)
  rw [sub_self, add_zero]

lemma metric_electric_zero_from_F (F : Fin 4 → Fin 4 → SL2C) (nu : Fin 4)
  (hF : ∀ alpha, F 0 alpha = 0) : urbantkeMetric F 0 nu = 0 := by
  unfold urbantkeMetric
  apply Finset.sum_eq_zero; intro a _
  apply Finset.sum_eq_zero; intro b _
  apply Finset.sum_eq_zero; intro c _
  have h_sum : (∑ alpha : Fin 4, ∑ beta : Fin 4, ∑ gamma : Fin 4, ∑ delta : Fin 4, epsilon4 alpha beta gamma delta * project F a 0 alpha * project F b nu beta * project F c gamma delta) = 0 := by
    apply Finset.sum_eq_zero; intro alpha _
    apply Finset.sum_eq_zero; intro beta _
    apply Finset.sum_eq_zero; intro gamma _
    apply Finset.sum_eq_zero; intro delta _
    have h_proj : project F a 0 alpha = 0 := by
      unfold project
      rw[hF alpha]
      change 0.5 * Matrix.trace ((0 : SL2C).val * (getPauli a).val) = 0
      have h_z : (0 : SL2C).val = 0 := rfl
      rw [h_z]
      have h_mul : (0 : Matrix (Fin 2) (Fin 2) ℂ) * (getPauli a).val = 0 := by ext i j; simp
      rw [h_mul]
      have h_trace : Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by simp[Matrix.trace]
      rw [h_trace]; ring
    rw [h_proj]; ring
  rw [h_sum, mul_zero]

private lemma fluxTubeIsMinimal_curvature_congruence (A B : Fin 4 → SpacetimePoint → SL2C) (x : SpacetimePoint)
  (h_val : ∀ mu, A mu x = B mu x)
  (h_deriv : ∀ mu nu, partialDerivSl2c nu (A mu) x = partialDerivSl2c nu (B mu) x) :
  ∀ mu nu, curvatureSl2c A mu nu x = curvatureSl2c B mu nu x := by
  intros mu nu
  unfold curvatureSl2c
  change partialDerivSl2c mu (A nu) x - partialDerivSl2c nu (A mu) x + ⁅A mu x, A nu x⁆ = partialDerivSl2c mu (B nu) x - partialDerivSl2c nu (B mu) x + ⁅B mu x, B nu x⁆
  rw[h_deriv mu nu, h_deriv nu mu, h_val mu, h_val nu]

/-- 🟡 KINEMATIC: Entanglement is a Wormhole (Metric Rank Deficiency) -/
theorem kinematicEntanglementWormhole (u : Universe) :
  ∀ (x y : SpacetimePoint) (theta : ℝ),
    areEntangled u.light x y theta →
    (urbantkeMetric (fun m n => curvatureSl2c u.light m n x)).det = 0 ∧
    (urbantkeMetric (fun m n => curvatureSl2c u.light m n y)).det = 0 := by
  intros x y theta h_ent
  unfold areEntangled at h_ent
  rcases h_ent with ⟨γ, θ, h_γ0, h_γ1, h_θ0, h_θ1, h_path⟩

  have h_x : (urbantkeMetric (fun m n => curvatureSl2c u.light m n x)).det = 0 := by
    have h_t0 := h_path 0 (by norm_num) (by norm_num)
    rcases h_t0 with ⟨h_val', h_deriv'⟩
    have h_val : ∀ mu, u.light mu x = rotateZ fluxTubeFrame (θ 0) mu x := by
      intro mu; have h := h_val' mu; rw [h_γ0] at h; exact h
    have h_deriv : ∀ mu nu, partialDerivSl2c nu (u.light mu) x = partialDerivSl2c nu (rotateZ fluxTubeFrame (θ 0) mu) x := by
      intro mu nu; have h := h_deriv' mu nu; rw [h_γ0] at h; exact h
    have h_curv : ∀ mu nu, curvatureSl2c u.light mu nu x = curvatureSl2c (rotateZ fluxTubeFrame (θ 0)) mu nu x :=
      fluxTubeIsMinimal_curvature_congruence u.light (rotateZ fluxTubeFrame (θ 0)) x h_val h_deriv
    have h_F : (fun m n => curvatureSl2c u.light m n x) = (fun m n => curvatureSl2c (rotateZ fluxTubeFrame (θ 0)) m n x) := by
      funext m n; exact h_curv m n
    rw [h_F]
    apply Matrix.det_eq_zero_of_row_eq_zero 0
    intro j
    apply metric_electric_zero_from_F
    intro alpha
    exact rotated_flux_tube_electric_zero (θ 0) alpha x

  have h_y : (urbantkeMetric (fun m n => curvatureSl2c u.light m n y)).det = 0 := by
    have h_t1 := h_path 1 (by norm_num) (by norm_num)
    rcases h_t1 with ⟨h_val', h_deriv'⟩
    have h_val : ∀ mu, u.light mu y = rotateZ fluxTubeFrame (θ 1) mu y := by
      intro mu; have h := h_val' mu; rw [h_γ1] at h; exact h
    have h_deriv : ∀ mu nu, partialDerivSl2c nu (u.light mu) y = partialDerivSl2c nu (rotateZ fluxTubeFrame (θ 1) mu) y := by
      intro mu nu; have h := h_deriv' mu nu; rw[h_γ1] at h; exact h
    have h_curv : ∀ mu nu, curvatureSl2c u.light mu nu y = curvatureSl2c (rotateZ fluxTubeFrame (θ 1)) mu nu y :=
      fluxTubeIsMinimal_curvature_congruence u.light (rotateZ fluxTubeFrame (θ 1)) y h_val h_deriv
    have h_F : (fun m n => curvatureSl2c u.light m n y) = (fun m n => curvatureSl2c (rotateZ fluxTubeFrame (θ 1)) m n y) := by
      funext m n; exact h_curv m n
    rw [h_F]
    apply Matrix.det_eq_zero_of_row_eq_zero 0
    intro j
    apply metric_electric_zero_from_F
    intro alpha
    exact rotated_flux_tube_electric_zero (θ 1) alpha y

  exact ⟨h_x, h_y⟩

end CGD.Quantum

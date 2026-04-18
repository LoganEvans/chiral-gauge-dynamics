-- FILENAME: CGD/Quantum/FluxTube.lean

import Litlib.Y1973.nielsen1973vortex.Signature
import CGD.Quantum.Definitions
import CGD.Gravity.Geometry
import CGD.Foundations.Calculus
import CGD.Foundations.Action
import CGD.Axioms.Ontology
import CGD.Axioms.Dynamics
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option linter.unusedVariables false

open CGD.Foundations CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms Litlib.Y1973.nielsen1973vortex

namespace CGD.Quantum

def satisfies1DMinimalEnergyBound (A : Fin 4 → SpacetimePoint → SL2C) (x : SpacetimePoint) : Prop :=
  (∀ nu, curvatureSl2c A 0 nu x = 0) ∧
  (∀ nu, partialDerivSl2c 0 (A nu) x = 0)

@[simp] private lemma to_sl2c_zero : toSl2c 0 = 0 := by
  apply Subtype.ext; unfold toSl2c; dsimp
  have h_tr : Matrix.trace (0 : Matrix (Fin 2) (Fin 2) Complex) = 0 := by simp[Matrix.trace]
  rw[h_tr]; have h1 : (0 : ℂ) / 2 = 0 := by ring
  rw[h1, zero_smul, sub_zero]

lemma diff_ofReal : Differentiable ℝ (fun z : ℝ => (z : ℂ)) := by
  intro z
  have h1 := hasDerivAt_id z
  have h2 := HasDerivAt.smul_const h1 (1 : ℂ)
  have eq1 : (fun (y : ℝ) => id y • (1 : ℂ)) = fun (s : ℝ) => (s : ℂ) := by ext x; simp
  have eq2 : (1 : ℝ) • (1 : ℂ) = 1 := by simp
  rw [eq1, eq2] at h2
  exact h2.differentiableAt

lemma diff_fluxTube_comp (sigma : Matrix (Fin 2) (Fin 2) ℂ) :
  ∀ i j, Differentiable ℝ (fun z : ℝ => ((Complex.I * (z : ℂ)) • sigma) i j) := by
  intro i j
  have h : (fun z : ℝ => ((Complex.I * (z : ℂ)) • sigma) i j) = fun z : ℝ => (Complex.I * (z : ℂ)) * sigma i j := by ext z; rfl
  rw [h]
  apply Differentiable.mul
  · apply Differentiable.mul
    · exact differentiable_const _
    · exact diff_ofReal
  · exact differentiable_const _

lemma math_partialDerivMat_fluxTube_time_0 (x : SpacetimePoint) : partialDerivMat 0 (fun p => (fluxTubeFrame 0 p).val) x = 0 := by
  have h0 : (fun p => (fluxTubeFrame 0 p).val) = fun _ => 0 := by ext p; rfl
  rw [h0]; exact partialDerivMat_const 0 0 x

lemma math_partialDerivMat_fluxTube_time_1 (x : SpacetimePoint) : partialDerivMat 0 (fun p => (fluxTubeFrame 1 p).val) x = 0 := by
  have h_neq : (0 : Fin 4) ≠ 1 := by decide
  have h1 : (fun p => (fluxTubeFrame 1 p).val) = fun p => (fun z : ℝ => (Complex.I * (z : ℂ)) • sigma2.val) (p 1) := by
    ext p; unfold fluxTubeFrame; simp
  rw [h1]
  exact math_partialDerivMat_comp_coord (fun z : ℝ => (Complex.I * (z : ℂ)) • sigma2.val) 1 0 h_neq x (diff_fluxTube_comp sigma2.val)

lemma math_partialDerivMat_fluxTube_time_2 (x : SpacetimePoint) : partialDerivMat 0 (fun p => (fluxTubeFrame 2 p).val) x = 0 := by
  have h_neq : (0 : Fin 4) ≠ 1 := by decide
  have h2 : (fun p => (fluxTubeFrame 2 p).val) = fun p => (fun z : ℝ => (Complex.I * (z : ℂ)) • sigma2.val) (p 1) := by
    ext p; unfold fluxTubeFrame; simp
  rw [h2]
  exact math_partialDerivMat_comp_coord (fun z : ℝ => (Complex.I * (z : ℂ)) • sigma2.val) 1 0 h_neq x (diff_fluxTube_comp sigma2.val)

lemma math_partialDerivMat_fluxTube_time_3 (x : SpacetimePoint) : partialDerivMat 0 (fun p => (fluxTubeFrame 3 p).val) x = 0 := by
  have h_neq : (0 : Fin 4) ≠ 1 := by decide
  have h3 : (fun p => (fluxTubeFrame 3 p).val) = fun p => (fun z : ℝ => (Complex.I * (z : ℂ)) • sigma3.val) (p 1) := by
    ext p; unfold fluxTubeFrame; simp
  rw [h3]
  exact math_partialDerivMat_comp_coord (fun z : ℝ => (Complex.I * (z : ℂ)) • sigma3.val) 1 0 h_neq x (diff_fluxTube_comp sigma3.val)

lemma math_partialDerivSl2c_fluxTube_time (nu : Fin 4) (x : SpacetimePoint) :
  partialDerivSl2c 0 (fluxTubeFrame nu) x = 0 := by
  unfold partialDerivSl2c
  have h_val : partialDerivMat 0 (fun p => (fluxTubeFrame nu p).val) x = 0 := by
    fin_cases nu
    · exact math_partialDerivMat_fluxTube_time_0 x
    · exact math_partialDerivMat_fluxTube_time_1 x
    · exact math_partialDerivMat_fluxTube_time_2 x
    · exact math_partialDerivMat_fluxTube_time_3 x
  rw [h_val]
  apply Subtype.ext
  unfold toSl2c
  dsimp
  have ht : Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by simp[Matrix.trace]
  rw [ht]
  have hz : (0:ℂ) / 2 = 0 := by ring
  rw [hz, zero_smul, sub_zero]

lemma math_partialDerivSl2c_fluxTube_cross (nu : Fin 4) (x : SpacetimePoint) :
  partialDerivSl2c nu (fluxTubeFrame 0) x = 0 := by
  have h_zero : fluxTubeFrame 0 = fun _ => 0 := by ext p; rfl
  rw [h_zero]
  exact partialDerivSl2c_const 0 nu x

lemma flux_tube_electric_zero_at (nu : Fin 4) (x : SpacetimePoint) :
  curvatureSl2c fluxTubeFrame 0 nu x = 0 := by
  unfold curvatureSl2c
  rw[math_partialDerivSl2c_fluxTube_time nu x, math_partialDerivSl2c_fluxTube_cross nu x]
  have h_frame_0 : fluxTubeFrame 0 x = 0 := rfl
  rw [h_frame_0]
  have h_bracket : ⁅(0 : SL2C), fluxTubeFrame nu x⁆ = 0 := by
    apply Subtype.ext; change (0 : Matrix (Fin 2) (Fin 2) ℂ) * _ - _ * 0 = 0; simp
  rw [h_bracket]
  change (0 : SL2C) - (0 : SL2C) + (0 : SL2C) = (0 : SL2C)
  rw [sub_self, add_zero]

lemma metric_electric_zero_at (nu : Fin 4) (x : SpacetimePoint) :
  urbantkeMetric (fun m n => curvatureSl2c fluxTubeFrame m n x) 0 nu = 0 := by
  unfold urbantkeMetric
  apply Finset.sum_eq_zero; intro a _
  apply Finset.sum_eq_zero; intro b _
  apply Finset.sum_eq_zero; intro c _
  have h_sum : (∑ alpha : Fin 4, ∑ beta : Fin 4, ∑ gamma : Fin 4, ∑ delta : Fin 4,
    epsilon4 alpha beta gamma delta * project (fun m n => curvatureSl2c fluxTubeFrame m n x) a 0 alpha * project (fun m n => curvatureSl2c fluxTubeFrame m n x) b nu beta * project (fun m n => curvatureSl2c fluxTubeFrame m n x) c gamma delta) = 0 := by
    apply Finset.sum_eq_zero; intro alpha _
    apply Finset.sum_eq_zero; intro beta _
    apply Finset.sum_eq_zero; intro gamma _
    apply Finset.sum_eq_zero; intro delta _
    have h_F : curvatureSl2c fluxTubeFrame 0 alpha x = 0 := flux_tube_electric_zero_at alpha x
    have h_proj : project (fun m n => curvatureSl2c fluxTubeFrame m n x) a 0 alpha = 0 := by
      unfold project; change 0.5 * Matrix.trace ((curvatureSl2c fluxTubeFrame 0 alpha x).val * (getPauli a).val) = 0
      rw[h_F]; have h_zero : (0 : SL2C).val = 0 := rfl; rw [h_zero, zero_mul]
      have h_trace : Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by simp[Matrix.trace]
      rw [h_trace, mul_zero]
    rw[h_proj]; ring
  rw [h_sum, mul_zero]

lemma curvature_congruence (A B : Fin 4 → SpacetimePoint → SL2C) (x : SpacetimePoint)
  (h_val : ∀ mu, A mu x = B mu x)
  (h_deriv : ∀ mu nu, partialDerivSl2c nu (A mu) x = partialDerivSl2c nu (B mu) x) :
  ∀ mu nu, curvatureSl2c A mu nu x = curvatureSl2c B mu nu x := by
  intros mu nu; unfold curvatureSl2c
  rw[h_deriv mu nu, h_deriv nu mu, h_val mu, h_val nu]

/-- 🟢 PROVEN: The flux tube algebraically satisfies the 1D minimal energy differential bounds. -/
theorem fluxTubeIsMinimal : ∀ x, satisfies1DMinimalEnergyBound fluxTubeFrame x := by
  intro x; unfold satisfies1DMinimalEnergyBound; apply And.intro
  · intro nu; exact flux_tube_electric_zero_at nu x
  · intro nu; exact math_partialDerivSl2c_fluxTube_time nu x

/-- 🟡 KINEMATIC: Flux Tube Degeneracy -/
theorem kinematicFluxTubeStability (u : Universe) :
  ∀ (x : SpacetimePoint),
    isFluxTube u.self_dual x →
    (urbantkeMetric (fun m n => curvatureSl2c u.self_dual m n x)).det = 0 := by
  intros x h_flux; unfold isFluxTube at h_flux; rcases h_flux with ⟨h_val, h_deriv⟩
  have h_curv : ∀ mu nu, curvatureSl2c u.self_dual mu nu x = curvatureSl2c fluxTubeFrame mu nu x :=
    curvature_congruence u.self_dual fluxTubeFrame x h_val h_deriv
  have h_F : (fun m n => curvatureSl2c u.self_dual m n x) = (fun m n => curvatureSl2c fluxTubeFrame m n x) := by funext m n; exact h_curv m n
  rw[h_F]; apply Matrix.det_eq_zero_of_row_eq_zero 0; intro j; exact metric_electric_zero_at j x

end CGD.Quantum

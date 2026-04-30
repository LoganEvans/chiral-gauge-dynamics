-- FILENAME: CGD/Quantum/Entanglement.lean

import Litlib.Core
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Lagrangian
import CGD.Quantum.Definitions
import CGD.Axioms.Ontology
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import CGD.Gravity.Geometry
import Litlib.Y2001.bali2001qcd.Signature

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms Litlib.Y2001.bali2001qcd

namespace CGD.Quantum

variable (spatialEnergy : (Fin 4 → SpacetimePoint → SL2C) → ℝ)
variable (intactFluxTube snappedFluxTube : ℝ → Fin 4 → SpacetimePoint → SL2C)

def isGlobalMinimum {α : Type*} (Energy : α → ℝ) (state : α) : Prop :=
  ∀ (other : α), Energy state ≤ Energy other

Litlib.theorem
  description "Entanglement Hamiltonian Crossover"
/-- 
Based on the Litlib macroscopic flux tube bounds, if the spatial distance exceeds the ratio of the static mass to the string tension, the classical intact string geometry ceases to be the state of minimum energy.
-/
theorem kinematicHamiltonianCrossover {sigma M : ℝ} [eb : FluxTubeEnergyBounds (Fin 4 → SpacetimePoint → SL2C) spatialEnergy intactFluxTube snappedFluxTube sigma M]
  (L : ℝ) (h_sigma : sigma > 0) (h_L : L > (2 * M) / sigma) :
  spatialEnergy (intactFluxTube L) > spatialEnergy (snappedFluxTube L) := by
  have h_intact := eb.intactEnergy L
  have h_snapped := eb.snappedEnergy L
  rw [h_intact, h_snapped]
  have h_bound : sigma * ((2 * M) / sigma) < sigma * L := mul_lt_mul_of_pos_left h_L h_sigma
  have h_sigma_ne_zero : sigma ≠ 0 := ne_of_gt h_sigma
  have h_cancel : sigma * ((2 * M) / sigma) = 2 * M := mul_div_cancel₀ _ h_sigma_ne_zero
  rw [h_cancel] at h_bound
  exact h_bound

Litlib.theorem
  description "Entanglement Decay"
/--
When the distance exceeds the crossover bound, the intact flux tube holding the entangled pair drops out of the global minimum.
-/
theorem dynamicEntanglementDecay {sigma M : ℝ} [eb : FluxTubeEnergyBounds (Fin 4 → SpacetimePoint → SL2C) spatialEnergy intactFluxTube snappedFluxTube sigma M]
  (L : ℝ) (h_sigma : sigma > 0) (h_L : L > (2 * M) / sigma) :
  ¬ isGlobalMinimum spatialEnergy (intactFluxTube L) := by
  intro h_min
  unfold isGlobalMinimum at h_min
  have h_crossover := kinematicHamiltonianCrossover spatialEnergy intactFluxTube snappedFluxTube L h_sigma h_L
  have h_le := h_min (snappedFluxTube L)
  linarith

lemma toSl2c_zero_val : (toSl2c (0 : Matrix (Fin 2) (Fin 2) ℂ)).val = 0 := by
  unfold toSl2c
  dsimp
  have h_tr : Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by simp [Matrix.trace]
  rw [h_tr]
  have hz : (0:ℂ) / 2 = 0 := by norm_num
  rw [hz, zero_smul, sub_zero]

lemma fluxTubeFrame_0_eq_zero (p : SpacetimePoint) : (fluxTubeFrame 0 p).val = 0 := by
  have hz : (0 : Fin 4) = 0 := rfl
  have h_ite : (if (0 : Fin 4) = 0 then (0 : Matrix (Fin 2) (Fin 2) ℂ) else if (0 : Fin 4) = 1 then Complex.I • sigma3.val else if (0 : Fin 4) = 2 then Complex.I • sigma1.val else Complex.I • sigma2.val) = 0 := if_pos hz
  have h_def : (fluxTubeFrame 0 p).val = (toSl2c (if (0 : Fin 4) = 0 then (0 : Matrix (Fin 2) (Fin 2) ℂ) else if (0 : Fin 4) = 1 then Complex.I • sigma3.val else if (0 : Fin 4) = 2 then Complex.I • sigma1.val else Complex.I • sigma2.val)).val := rfl
  have h_subst : (fluxTubeFrame 0 p).val = (toSl2c 0).val := Eq.trans h_def (congr_arg (fun M => (toSl2c M).val) h_ite)
  exact Eq.trans h_subst toSl2c_zero_val

lemma rotateZ_math_partialDerivMat_fluxTube_time_0 (C : ℝ) (x : SpacetimePoint) : 
  partialDerivMat 0 (fun p => (rotateZ fluxTubeFrame C 0 p).val) x = 0 := by
  have h0 : (fun p => (rotateZ fluxTubeFrame C 0 p).val) = fun _ => 0 := by
    apply funext
    intro p
    have h_f0 : (fluxTubeFrame 0 p).val = 0 := fluxTubeFrame_0_eq_zero p
    have h_rot : (rotateZ fluxTubeFrame C 0 p).val = 
      (toSl2c (Matrix.of ![![Complex.cos (↑C / 2), -Complex.sin (↑C / 2)], ![Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] * 
      (fluxTubeFrame 0 p).val * 
      Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]])).val := rfl
    have h_subst : (rotateZ fluxTubeFrame C 0 p).val = 
      (toSl2c (Matrix.of ![![Complex.cos (↑C / 2), -Complex.sin (↑C / 2)], ![Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] * 
      0 * 
      Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]])).val := congr_arg (fun M => (toSl2c (Matrix.of ![![Complex.cos (↑C / 2), -Complex.sin (↑C / 2)], ![Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] * M * Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]])).val) h_f0
    have h_mul1 : Matrix.of ![![Complex.cos (↑C / 2), -Complex.sin (↑C / 2)], ![Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] * 0 = 0 := Matrix.mul_zero _
    have h_mul1_congr : Matrix.of ![![Complex.cos (↑C / 2), -Complex.sin (↑C / 2)], ![Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] * 0 * Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] = 0 * Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] := congr_arg (fun M => M * Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]]) h_mul1
    have h_mul2 : 0 * Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] = 0 := Matrix.zero_mul _
    have h_inner_eq : Matrix.of ![![Complex.cos (↑C / 2), -Complex.sin (↑C / 2)], ![Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] * 0 * Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] = 0 := Eq.trans h_mul1_congr h_mul2
    have h_subst2 : (rotateZ fluxTubeFrame C 0 p).val = (toSl2c 0).val := Eq.trans h_subst (congr_arg (fun M => (toSl2c M).val) h_inner_eq)
    exact Eq.trans h_subst2 toSl2c_zero_val
  have h_pd : partialDerivMat 0 (fun p => (rotateZ fluxTubeFrame C 0 p).val) x = partialDerivMat 0 (fun _ => 0) x := congr_arg (fun f => partialDerivMat 0 f x) h0
  exact Eq.trans h_pd (partialDerivMat_const 0 0 x)

lemma fluxTubeFrame_eval_1 (p : SpacetimePoint) : 
  fluxTubeFrame 1 p = toSl2c (Complex.I • sigma3.val) := by
  unfold fluxTubeFrame
  have h1 : (1:Fin 4) ≠ 0 := by decide
  have h2 : (1:Fin 4) = 1 := rfl
  have h_ite : (if (1:Fin 4) = 0 then (0 : Matrix (Fin 2) (Fin 2) ℂ) else if (1:Fin 4) = 1 then Complex.I • sigma3.val else if (1:Fin 4) = 2 then Complex.I • sigma1.val else Complex.I • sigma2.val) = Complex.I • sigma3.val := by
    rw [if_neg h1, if_pos h2]
  exact congr_arg toSl2c h_ite

lemma fluxTubeFrame_eval_2 (p : SpacetimePoint) : 
  fluxTubeFrame 2 p = toSl2c (Complex.I • sigma1.val) := by
  unfold fluxTubeFrame
  have h1 : (2:Fin 4) ≠ 0 := by decide
  have h2 : (2:Fin 4) ≠ 1 := by decide
  have h3 : (2:Fin 4) = 2 := rfl
  have h_ite : (if (2:Fin 4) = 0 then (0 : Matrix (Fin 2) (Fin 2) ℂ) else if (2:Fin 4) = 1 then Complex.I • sigma3.val else if (2:Fin 4) = 2 then Complex.I • sigma1.val else Complex.I • sigma2.val) = Complex.I • sigma1.val := by
    rw [if_neg h1, if_neg h2, if_pos h3]
  exact congr_arg toSl2c h_ite

lemma fluxTubeFrame_eval_3 (p : SpacetimePoint) : 
  fluxTubeFrame 3 p = toSl2c (Complex.I • sigma2.val) := by
  unfold fluxTubeFrame
  have h1 : (3:Fin 4) ≠ 0 := by decide
  have h2 : (3:Fin 4) ≠ 1 := by decide
  have h3 : (3:Fin 4) ≠ 2 := by decide
  have h_ite : (if (3:Fin 4) = 0 then (0 : Matrix (Fin 2) (Fin 2) ℂ) else if (3:Fin 4) = 1 then Complex.I • sigma3.val else if (3:Fin 4) = 2 then Complex.I • sigma1.val else Complex.I • sigma2.val) = Complex.I • sigma2.val := by
    rw [if_neg h1, if_neg h2, if_neg h3]
  exact congr_arg toSl2c h_ite

lemma rotateZ_math_partialDerivMat_fluxTube_time_1 (C : ℝ) (x : SpacetimePoint) : 
  partialDerivMat 0 (fun p => (rotateZ fluxTubeFrame C 1 p).val) x = 0 := by
  have h1 : (fun p => (rotateZ fluxTubeFrame C 1 p).val) = fun _ => (rotateZ fluxTubeFrame C 1 x).val := by
    apply funext
    intro p
    have hp : fluxTubeFrame 1 p = fluxTubeFrame 1 x := by
      have hp1 : fluxTubeFrame 1 p = toSl2c (Complex.I • sigma3.val) := fluxTubeFrame_eval_1 p
      have hx1 : fluxTubeFrame 1 x = toSl2c (Complex.I • sigma3.val) := fluxTubeFrame_eval_1 x
      exact Eq.trans hp1 (Eq.symm hx1)
    unfold rotateZ
    exact congr_arg (fun A => (toSl2c (Matrix.of ![![Complex.cos (↑C / 2), -Complex.sin (↑C / 2)], ![Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] * A.val * Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]])).val) hp
  rw [h1]; exact partialDerivMat_const _ 0 x

lemma rotateZ_math_partialDerivMat_fluxTube_time_2 (C : ℝ) (x : SpacetimePoint) : 
  partialDerivMat 0 (fun p => (rotateZ fluxTubeFrame C 2 p).val) x = 0 := by
  have h2 : (fun p => (rotateZ fluxTubeFrame C 2 p).val) = fun _ => (rotateZ fluxTubeFrame C 2 x).val := by
    apply funext
    intro p
    have hp : fluxTubeFrame 2 p = fluxTubeFrame 2 x := by
      have hp1 : fluxTubeFrame 2 p = toSl2c (Complex.I • sigma1.val) := fluxTubeFrame_eval_2 p
      have hx1 : fluxTubeFrame 2 x = toSl2c (Complex.I • sigma1.val) := fluxTubeFrame_eval_2 x
      exact Eq.trans hp1 (Eq.symm hx1)
    unfold rotateZ
    exact congr_arg (fun A => (toSl2c (Matrix.of ![![Complex.cos (↑C / 2), -Complex.sin (↑C / 2)], ![Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] * A.val * Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]])).val) hp
  rw [h2]; exact partialDerivMat_const _ 0 x

lemma rotateZ_math_partialDerivMat_fluxTube_time_3 (C : ℝ) (x : SpacetimePoint) : 
  partialDerivMat 0 (fun p => (rotateZ fluxTubeFrame C 3 p).val) x = 0 := by
  have h3 : (fun p => (rotateZ fluxTubeFrame C 3 p).val) = fun _ => (rotateZ fluxTubeFrame C 3 x).val := by
    apply funext
    intro p
    have hp : fluxTubeFrame 3 p = fluxTubeFrame 3 x := by
      have hp1 : fluxTubeFrame 3 p = toSl2c (Complex.I • sigma2.val) := fluxTubeFrame_eval_3 p
      have hx1 : fluxTubeFrame 3 x = toSl2c (Complex.I • sigma2.val) := fluxTubeFrame_eval_3 x
      exact Eq.trans hp1 (Eq.symm hx1)
    unfold rotateZ
    exact congr_arg (fun A => (toSl2c (Matrix.of ![![Complex.cos (↑C / 2), -Complex.sin (↑C / 2)], ![Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] * A.val * Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]])).val) hp
  rw [h3]; exact partialDerivMat_const _ 0 x

lemma rotateZ_math_partialDerivSl2c_fluxTube_time (C : ℝ) (nu : Fin 4) (x : SpacetimePoint) :
  partialDerivSl2c 0 (rotateZ fluxTubeFrame C nu) x = 0 := by
  unfold partialDerivSl2c
  have h_val : partialDerivMat 0 (fun p => (rotateZ fluxTubeFrame C nu p).val) x = 0 := by
    fin_cases nu
    · exact rotateZ_math_partialDerivMat_fluxTube_time_0 C x
    · exact rotateZ_math_partialDerivMat_fluxTube_time_1 C x
    · exact rotateZ_math_partialDerivMat_fluxTube_time_2 C x
    · exact rotateZ_math_partialDerivMat_fluxTube_time_3 C x
  rw [h_val]
  apply Subtype.ext
  exact toSl2c_zero_val

lemma rotateZ_math_partialDerivSl2c_fluxTube_cross (C : ℝ) (nu : Fin 4) (x : SpacetimePoint) :
  partialDerivSl2c nu (rotateZ fluxTubeFrame C 0) x = 0 := by
  have h_zero : rotateZ fluxTubeFrame C 0 = fun _ => 0 := by 
    apply funext
    intro p
    unfold rotateZ
    have h_f0 : (fluxTubeFrame 0 p).val = 0 := fluxTubeFrame_0_eq_zero p
    have h_mul1 : Matrix.of ![![Complex.cos (↑C / 2), -Complex.sin (↑C / 2)], ![Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] * (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := Matrix.mul_zero _
    have h_mul2 : (0 : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] = 0 := Matrix.zero_mul _
    have h_subst : toSl2c (Matrix.of ![![Complex.cos (↑C / 2), -Complex.sin (↑C / 2)], ![Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] * (fluxTubeFrame 0 p).val * Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]]) = toSl2c 0 := by
      rw [h_f0, h_mul1, h_mul2]
    rw [h_subst]
    apply Subtype.ext
    exact toSl2c_zero_val
  rw [h_zero]
  exact partialDerivSl2c_const 0 nu x

lemma rotateZ_flux_tube_electric_zero_at (C : ℝ) (nu : Fin 4) (x : SpacetimePoint) :
  curvatureSl2c (rotateZ fluxTubeFrame C) 0 nu x = 0 := by
  unfold curvatureSl2c
  rw[rotateZ_math_partialDerivSl2c_fluxTube_time C nu x, rotateZ_math_partialDerivSl2c_fluxTube_cross C nu x]
  have h_frame_0 : rotateZ fluxTubeFrame C 0 x = 0 := by 
    apply Subtype.ext
    unfold rotateZ
    have h_f0 : (fluxTubeFrame 0 x).val = 0 := fluxTubeFrame_0_eq_zero x
    have h_mul1 : Matrix.of ![![Complex.cos (↑C / 2), -Complex.sin (↑C / 2)], ![Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] * (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := Matrix.mul_zero _
    have h_mul2 : (0 : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] = 0 := Matrix.zero_mul _
    have h_subst : toSl2c (Matrix.of ![![Complex.cos (↑C / 2), -Complex.sin (↑C / 2)], ![Complex.sin (↑C / 2), Complex.cos (↑C / 2)]] * (fluxTubeFrame 0 x).val * Matrix.of ![![Complex.cos (↑C / 2), Complex.sin (↑C / 2)], ![-Complex.sin (↑C / 2), Complex.cos (↑C / 2)]]) = toSl2c 0 := by
      rw [h_f0, h_mul1, h_mul2]
    rw [h_subst]
    exact toSl2c_zero_val
  rw [h_frame_0]
  have h_bracket : ⁅(0 : SL2C), rotateZ fluxTubeFrame C nu x⁆ = 0 := by
    apply Subtype.ext; change (0 : Matrix (Fin 2) (Fin 2) ℂ) * _ - _ * 0 = 0; simp
  rw [h_bracket]
  change (0 : SL2C) - (0 : SL2C) + (0 : SL2C) = (0 : SL2C)
  rw [sub_self, add_zero]

lemma rotateZ_metric_electric_zero_at (C : ℝ) (nu : Fin 4) (x : SpacetimePoint) :
  urbantkeMetric (fun m n => curvatureSl2c (rotateZ fluxTubeFrame C) m n x) 0 nu = 0 := by
  unfold urbantkeMetric
  apply Finset.sum_eq_zero; intro a _
  apply Finset.sum_eq_zero; intro b _
  apply Finset.sum_eq_zero; intro c _
  have h_sum : (∑ alpha : Fin 4, ∑ beta : Fin 4, ∑ gamma : Fin 4, ∑ delta : Fin 4,
    epsilon4 alpha beta gamma delta * project (fun m n => curvatureSl2c (rotateZ fluxTubeFrame C) m n x) a 0 alpha * project (fun m n => curvatureSl2c (rotateZ fluxTubeFrame C) m n x) b nu beta * project (fun m n => curvatureSl2c (rotateZ fluxTubeFrame C) m n x) c gamma delta) = 0 := by
    apply Finset.sum_eq_zero; intro alpha _
    apply Finset.sum_eq_zero; intro beta _
    apply Finset.sum_eq_zero; intro gamma _
    apply Finset.sum_eq_zero; intro delta _
    have h_F : curvatureSl2c (rotateZ fluxTubeFrame C) 0 alpha x = 0 := rotateZ_flux_tube_electric_zero_at C alpha x
    have h_proj : project (fun m n => curvatureSl2c (rotateZ fluxTubeFrame C) m n x) a 0 alpha = 0 := by
      unfold project; change 0.5 * Matrix.trace ((curvatureSl2c (rotateZ fluxTubeFrame C) 0 alpha x).val * (getPauli a).val) = 0
      rw[h_F]; have h_zero : (0 : SL2C).val = 0 := rfl; rw [h_zero, zero_mul]
      have h_trace : Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by simp[Matrix.trace]
      rw [h_trace, mul_zero]
    rw[h_proj]; ring
  rw [h_sum, mul_zero]

lemma entang_curvature_congruence (A B : Fin 4 → SpacetimePoint → SL2C) (x : SpacetimePoint)
  (h_val : ∀ mu, A mu x = B mu x)
  (h_deriv : ∀ mu nu, partialDerivSl2c nu (A mu) x = partialDerivSl2c nu (B mu) x) :
  ∀ mu nu, curvatureSl2c A mu nu x = curvatureSl2c B mu nu x := by
  intros mu nu; unfold curvatureSl2c
  rw[h_deriv mu nu, h_deriv nu mu, h_val mu, h_val nu]

Litlib.theorem
  description "Entanglement Metric Rank Deficiency"
/--
The spatial metric defining the wormhole channel connecting entangled particles has a rigorously zero determinant, confirming its non-local, degenerate topology.
-/
theorem kinematicEntanglementWormhole (u : Universe) :
  ∀ (x y : SpacetimePoint) (theta : ℝ),
    areEntangled u.sd_sector x y theta →
    (urbantkeMetric (fun m n => curvatureSl2c u.sd_sector m n x)).det = 0 ∧
    (urbantkeMetric (fun m n => curvatureSl2c u.sd_sector m n y)).det = 0 := by
  intros x y theta h_entangled
  unfold areEntangled at h_entangled
  rcases h_entangled with ⟨γ, θ, h_γ_0, h_γ_1, h_θ_0, h_θ_1, h_path⟩

  have h_x_val : ∀ mu, u.sd_sector mu x = rotateZ fluxTubeFrame (θ 0) mu x := by
    intro mu
    have h_t := (h_path 0) (by linarith) (by linarith)
    have h_eval := h_t.1 mu
    rw [h_γ_0] at h_eval
    exact h_eval

  have h_x_deriv : ∀ mu nu, partialDerivSl2c nu (u.sd_sector mu) x = partialDerivSl2c nu (rotateZ fluxTubeFrame (θ 0) mu) x := by
    intro mu nu
    have h_t := (h_path 0) (by linarith) (by linarith)
    have h_eval := h_t.2 mu nu
    rw [h_γ_0] at h_eval
    exact h_eval

  have h_curv_x : ∀ mu nu, curvatureSl2c u.sd_sector mu nu x = curvatureSl2c (rotateZ fluxTubeFrame (θ 0)) mu nu x :=
    entang_curvature_congruence u.sd_sector (rotateZ fluxTubeFrame (θ 0)) x h_x_val h_x_deriv

  have h_F_x : (fun m n => curvatureSl2c u.sd_sector m n x) = (fun m n => curvatureSl2c (rotateZ fluxTubeFrame (θ 0)) m n x) := by funext m n; exact h_curv_x m n
  have h_det_x : (urbantkeMetric (fun m n => curvatureSl2c u.sd_sector m n x)).det = 0 := by
    rw [h_F_x]
    apply Matrix.det_eq_zero_of_row_eq_zero 0
    intro j
    exact rotateZ_metric_electric_zero_at (θ 0) j x

  have h_y_val : ∀ mu, u.sd_sector mu y = rotateZ fluxTubeFrame (θ 1) mu y := by
    intro mu
    have h_t := (h_path 1) (by linarith) (by linarith)
    have h_eval := h_t.1 mu
    rw [h_γ_1] at h_eval
    exact h_eval

  have h_y_deriv : ∀ mu nu, partialDerivSl2c nu (u.sd_sector mu) y = partialDerivSl2c nu (rotateZ fluxTubeFrame (θ 1) mu) y := by
    intro mu nu
    have h_t := (h_path 1) (by linarith) (by linarith)
    have h_eval := h_t.2 mu nu
    rw [h_γ_1] at h_eval
    exact h_eval

  have h_curv_y : ∀ mu nu, curvatureSl2c u.sd_sector mu nu y = curvatureSl2c (rotateZ fluxTubeFrame (θ 1)) mu nu y :=
    entang_curvature_congruence u.sd_sector (rotateZ fluxTubeFrame (θ 1)) y h_y_val h_y_deriv

  have h_F_y : (fun m n => curvatureSl2c u.sd_sector m n y) = (fun m n => curvatureSl2c (rotateZ fluxTubeFrame (θ 1)) m n y) := by funext m n; exact h_curv_y m n
  have h_det_y : (urbantkeMetric (fun m n => curvatureSl2c u.sd_sector m n y)).det = 0 := by
    rw [h_F_y]
    apply Matrix.det_eq_zero_of_row_eq_zero 0
    intro j
    exact rotateZ_metric_electric_zero_at (θ 1) j y

  exact And.intro h_det_x h_det_y

end CGD.Quantum

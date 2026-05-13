-- FILENAME: CGD/Quantum/Holonomy.lean

import Litlib.Core
import CGD.Quantum.Holonomy.PathEval
import CGD.Quantum.Holonomy.Bell
import CGD.Quantum.Holonomy.Observables
import CGD.Quantum.Holonomy.Pauli
import CGD.Quantum.Holonomy.Basic
import CGD.Quantum.Definitions
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology
import Litlib.Y2000.hall2000elementary.Signature

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations Matrix Complex BigOperators CGD.Axioms Litlib.Y2000.hall2000elementary

namespace CGD.Quantum

Litlib.theorem
  description "Holonomic Bell Violation (Tsirelson Bound)"
/-- 
Macroscopic SU(2) string holonomies fundamentally violate classical Bell inequalities, structurally bounding at the Tsirelson limit.
-/
theorem kinematicHolonomicBellViolation 
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (holonomy integral : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
  (h_holonomy_comm : ∀ A t0 t1, (∀ s t, A s * A t = A t * A s) → holonomy A t0 t1 = matrixExp (integral A t0 t1))
  (h_integral_const : ∀ C t0 t1, integral (fun _ => C) t0 t1 = (t1 - t0 : ℂ) • C)
  (h_exp_pauli : ∀ θ, matrixExp ((Complex.I * (Real.pi / 2 : ℂ)) • obs_M θ) = Complex.I • obs_M θ)
  [CommutingExponential (Fin 2) matrixExp]
  [OneParameterSubgroups (Fin 2) matrixExp]
  [DeterminantExponential (Fin 2) matrixExp]
  [LieProductFormula (Fin 2) matrixExp]
  (u : Universe) (D : ℝ) :
  (∀ t, u.sd_sector 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t)) →
  D > 0 →
  (CGD.Gravity.urbantkeMetric (fun m n => CGD.Foundations.curvatureSl2c u.sd_sector m n (straightLinePath 0)) 1 1).re > D →
  let L := Real.pi / 2;
  let A1 := macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) 0 mu p) 1 L;
  let A2 := macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (Real.pi / 2) mu p) 1 L;
  let B1 := macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (Real.pi / 4) mu p) 1 L;
  let B2 := macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (- (Real.pi / 4)) mu p) 1 L;
  A1^2 = 1 ∧ A2^2 = 1 ∧ B1^2 = 1 ∧ B2^2 = 1 ∧
  (chshSumBell A1 A2 B1 B2)^2 = 8 := by
  intro h_field hD_pos hD_bound

  let γ := straightLinePath
  have h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0 := straightLinePath_prop
  
  have ev_A1 : macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) 0 mu p) 1 (Real.pi / 2) = obs_M 0 := 
    eval_obs matrixExp holonomy integral h_holonomy_comm h_integral_const h_exp_pauli u 0 γ h_path h_field
  have ev_A2 : macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (Real.pi / 2) mu p) 1 (Real.pi / 2) = obs_M (Real.pi / 2) := 
    eval_obs matrixExp holonomy integral h_holonomy_comm h_integral_const h_exp_pauli u (Real.pi / 2) γ h_path h_field
  have ev_B1 : macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (Real.pi / 4) mu p) 1 (Real.pi / 2) = obs_M (Real.pi / 4) := 
    eval_obs matrixExp holonomy integral h_holonomy_comm h_integral_const h_exp_pauli u (Real.pi / 4) γ h_path h_field
  have ev_B2 : macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (- (Real.pi / 4)) mu p) 1 (Real.pi / 2) = obs_M (- (Real.pi / 4)) := 
    eval_obs matrixExp holonomy integral h_holonomy_comm h_integral_const h_exp_pauli u (- (Real.pi / 4)) γ h_path h_field

  have hA1 : (macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) 0 mu p) 1 (Real.pi / 2))^2 = 1 := by
    rw [ev_A1, pow_two, M_sq 0]
  have hA2 : (macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (Real.pi / 2) mu p) 1 (Real.pi / 2))^2 = 1 := by
    rw [ev_A2, pow_two, M_sq (Real.pi / 2)]
  have hB1 : (macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (Real.pi / 4) mu p) 1 (Real.pi / 2))^2 = 1 := by
    rw [ev_B1, pow_two, M_sq (Real.pi / 4)]
  have hB2 : (macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (- (Real.pi / 4)) mu p) 1 (Real.pi / 2))^2 = 1 := by
    rw [ev_B2, pow_two, M_sq (- (Real.pi / 4))]
  have hCHSH : (chshSumBell 
      (macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) 0 mu p) 1 (Real.pi / 2))
      (macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (Real.pi / 2) mu p) 1 (Real.pi / 2))
      (macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (Real.pi / 4) mu p) 1 (Real.pi / 2))
      (macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) (- (Real.pi / 4)) mu p) 1 (Real.pi / 2))
    )^2 = 8 := by
    rw [ev_A1, ev_A2, ev_B1, ev_B2]
    exact chsh_obs_M_violation

  dsimp only
  exact ⟨hA1, hA2, hB1, hB2, hCHSH⟩


Litlib.theorem
  description "Singlet Correlation Emergence"
/-- 
Without the artificial twist of entanglement, the exact quantum singlet correlation (-cos(a-b)) natively emerges from the pure classical SU(2) geometry of the intact macroscopic string.
-/
theorem kinematicHolonomicDegeneracy 
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (holonomy integral : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
  (h_holonomy_comm : ∀ A t0 t1, (∀ s t, A s * A t = A t * A s) → holonomy A t0 t1 = matrixExp (integral A t0 t1))
  (h_integral_const : ∀ C t0 t1, integral (fun _ => C) t0 t1 = (t1 - t0 : ℂ) • C)
  (h_exp_pauli : ∀ θ, matrixExp ((Complex.I * (Real.pi / 2 : ℂ)) • obs_M θ) = Complex.I • obs_M θ)
  [CommutingExponential (Fin 2) matrixExp]
  [OneParameterSubgroups (Fin 2) matrixExp]
  [DeterminantExponential (Fin 2) matrixExp]
  [LieProductFormula (Fin 2) matrixExp]
  (u : Universe) :
  ∀ (alpha beta D : ℝ),
    (∀ t, u.sd_sector 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t)) →
    D > 0 →
    (CGD.Gravity.urbantkeMetric (fun m n => CGD.Foundations.curvatureSl2c u.sd_sector m n (straightLinePath 0)) 1 1).re > D →
    let L := Real.pi / 2;
    let obs_x := macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 L;
    let obs_y := macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) beta mu p) 1 L;
    bellCorrelationDeg obs_x (- obs_y)
      = - Complex.cos ((alpha : ℂ) - (beta : ℂ)) := by
  intro alpha beta D h_field hD_pos hD_bound
  
  let γ := straightLinePath
  have h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0 := straightLinePath_prop
  
  have ev_x : macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 (Real.pi / 2) = obs_M alpha := 
    eval_obs matrixExp holonomy integral h_holonomy_comm h_integral_const h_exp_pauli u alpha γ h_path h_field
  have ev_y : macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) beta mu p) 1 (Real.pi / 2) = obs_M beta := 
    eval_obs matrixExp holonomy integral h_holonomy_comm h_integral_const h_exp_pauli u beta γ h_path h_field

  dsimp only
  rw [ev_x, ev_y]
  rw [← Complex.ofReal_sub]
  exact obs_M_correlation alpha beta

end CGD.Quantum

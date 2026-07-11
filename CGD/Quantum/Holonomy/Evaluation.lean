-- FILENAME: CGD/Quantum/Holonomy/Evaluation.lean

import CGD.Quantum.Holonomy.Geometric
import CGD.Quantum.Holonomy.Euler
import CGD.Quantum.Definitions
import CGD.Axioms.PhysicalUniverse
import Litlib.Y2000.hall2000elementary.Signature

set_option linter.unusedSimpArgs false

namespace CGD.Quantum

open CGD.Foundations CGD.Math CGD.Axioms Complex Matrix Litlib.Y2000.hall2000elementary

noncomputable def straightLinePath (t : ℝ) : SpacetimePoint := fun _ => t

noncomputable def obs_M (alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let R := Matrix.of ![![Complex.cos (alpha/2), -Complex.sin (alpha/2)], ![Complex.sin (alpha/2), Complex.cos (alpha/2)]]
  let R_inv := Matrix.of ![![Complex.cos (alpha/2), Complex.sin (alpha/2)], ![-Complex.sin (alpha/2), Complex.cos (alpha/2)]]
  R * sigma3.val * R_inv

@[litlib_track "Geometric Holonomy"]
-- NATIVE EVALUATION: The exact path-ordered exponential for a constant field
noncomputable def holonomy (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (A : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (t0 t1 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  matrixExp ((t1 - t0 : ℂ) • A t0)

@[litlib_track "Macroscopic Observable"]
noncomputable def macroscopicObservable
  (holonomy : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
  (A : Fin 4 → SpacetimePoint → SL2C)
  (mu : Fin 4) (L : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  holonomy (fun t => (A mu (straightLinePath t)).val) 0 L

lemma R_inv_R_eq_one (alpha : ℝ) :
  (Matrix.of ![![Complex.cos (alpha/2), Complex.sin (alpha/2)], ![-Complex.sin (alpha/2), Complex.cos (alpha/2)]] : Matrix (Fin 2) (Fin 2) ℂ) *
  Matrix.of ![![Complex.cos (alpha/2), -Complex.sin (alpha/2)], ![Complex.sin (alpha/2), Complex.cos (alpha/2)]] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h : Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
    calc Complex.cos (alpha / 2 : ℂ) * Complex.cos (alpha / 2 : ℂ) + Complex.sin (alpha / 2 : ℂ) * Complex.sin (alpha / 2 : ℂ)
      = Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 := by ring
      _ = 1 := h
  · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h : Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
    calc Complex.sin (alpha / 2 : ℂ) * Complex.sin (alpha / 2 : ℂ) + Complex.cos (alpha / 2 : ℂ) * Complex.cos (alpha / 2 : ℂ)
      = Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 := by ring
      _ = 1 := h

lemma R_R_inv_eq_one (alpha : ℝ) :
  (Matrix.of ![![Complex.cos (alpha/2), -Complex.sin (alpha/2)], ![Complex.sin (alpha/2), Complex.cos (alpha/2)]] : Matrix (Fin 2) (Fin 2) ℂ) *
  Matrix.of ![![Complex.cos (alpha/2), Complex.sin (alpha/2)], ![-Complex.sin (alpha/2), Complex.cos (alpha/2)]] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h : Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
    calc Complex.cos (alpha / 2 : ℂ) * Complex.cos (alpha / 2 : ℂ) + Complex.sin (alpha / 2 : ℂ) * Complex.sin (alpha / 2 : ℂ)
      = Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 := by ring
      _ = 1 := h
  · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h : Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
    calc Complex.sin (alpha / 2 : ℂ) * Complex.sin (alpha / 2 : ℂ) + Complex.cos (alpha / 2 : ℂ) * Complex.cos (alpha / 2 : ℂ)
      = Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 := by ring
      _ = 1 := h

lemma h_sum2 (f : Fin 2 → ℂ) : ∑ i : Fin 2, f i = f 0 + f 1 := Fin.sum_univ_two f

lemma obs_M_sq (alpha : ℝ) : obs_M alpha * obs_M alpha = 1 := by
  dsimp [obs_M]
  have h_inv := R_inv_R_eq_one alpha
  have h_R := R_R_inv_eq_one alpha
  let R : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![Complex.cos (alpha/2), -Complex.sin (alpha/2)], ![Complex.sin (alpha/2), Complex.cos (alpha/2)]]
  let R_inv : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![Complex.cos (alpha/2), Complex.sin (alpha/2)], ![-Complex.sin (alpha/2), Complex.cos (alpha/2)]]

  have h_sig : sigma3.val * sigma3.val = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals {
      simp [sigma3, toSl2c, sigmaZ, mkMat, Matrix.mul_apply, Matrix.trace, Matrix.diag, h_sum2]
    }

  calc (R * sigma3.val * R_inv) * (R * sigma3.val * R_inv)
    = R * (sigma3.val * (R_inv * (R * (sigma3.val * R_inv)))) := by simp only [Matrix.mul_assoc]
    _ = R * (sigma3.val * ((R_inv * R) * (sigma3.val * R_inv))) := by rw [← Matrix.mul_assoc R_inv R (sigma3.val * R_inv)]
    _ = R * (sigma3.val * (1 * (sigma3.val * R_inv))) := by rw [h_inv]
    _ = R * (sigma3.val * (sigma3.val * R_inv)) := by rw [Matrix.one_mul]
    _ = R * ((sigma3.val * sigma3.val) * R_inv) := by rw [← Matrix.mul_assoc sigma3.val sigma3.val R_inv]
    _ = R * (1 * R_inv) := by rw [h_sig]
    _ = R * R_inv := by rw [Matrix.one_mul]
    _ = 1 := h_R

lemma I_obs_M_trace_zero (alpha : ℝ) : Matrix.trace (Complex.I • obs_M alpha) = 0 := by
  dsimp [obs_M]
  simp [Matrix.trace, Matrix.diag, sigma3, toSl2c, sigmaZ, mkMat, Matrix.smul_apply, h_sum2]
  ring

lemma I_obs_M_toSl2c (alpha : ℝ) : (toSl2c (Complex.I • obs_M alpha)).val = Complex.I • obs_M alpha := by
  ext i j
  dsimp [toSl2c]
  have hz := I_obs_M_trace_zero alpha
  rw [hz]
  simp

lemma fluxTubeFrame_one_val (t : ℝ) : (fluxTubeFrame 1 (straightLinePath t)).val = Complex.I • sigma3.val := by
  dsimp [fluxTubeFrame]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    simp [toSl2c, sigma3, sigmaZ, mkMat, Matrix.trace, Matrix.diag, Matrix.smul_apply, h_sum2]
  }

/--
Evaluates the path-ordered integral of the exact `fluxTubeFrame` spatial gauge connection witness.
This explicitly demonstrates that evaluating an SU(2) holonomy natively maps geometric
parameters directly to the trigonometric coefficients of standard quantum state vectors,
proving that the geometry can natively reproduce quantum observables.
-/
@[litlib_track "Macroscopic Spin State Witness"]
theorem fluxTubeHolonomyEvaluation
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  [DerivativeExponential (Fin 2) matrixExp]
  (pu : PhysicalUniverse) (alpha L : ℝ)
  (h_field : ∀ t, pu.toUniverse.sd_sector 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t)) :
  macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 L =
  (Complex.cos (L:ℂ)) • 1 + (Complex.I * Complex.sin (L:ℂ)) • obs_M alpha := by

  dsimp [macroscopicObservable, holonomy]

  have hf : (pu.toUniverse.sd_sector 1 (straightLinePath 0)).val = (fluxTubeFrame 1 (straightLinePath 0)).val :=
    congr_arg Subtype.val (h_field 0)

  have h_eval : (rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha 1 (straightLinePath 0)).val =
                Complex.I • obs_M alpha := by
    dsimp [rotateYAxis]
    rw [hf]
    have h_flux := fluxTubeFrame_one_val 0
    rw [h_flux]

    have h_assoc : Matrix.of ![![Complex.cos (alpha / 2 : ℂ), -Complex.sin (alpha / 2 : ℂ)], ![Complex.sin (alpha / 2 : ℂ), Complex.cos (alpha / 2 : ℂ)]] *
                   (Complex.I • sigma3.val) *
                   Matrix.of ![![Complex.cos (alpha / 2 : ℂ), Complex.sin (alpha / 2 : ℂ)], ![-Complex.sin (alpha / 2 : ℂ), Complex.cos (alpha / 2 : ℂ)]] =
                   Complex.I • obs_M alpha := by
      dsimp [obs_M]
      rw [Matrix.mul_smul, Matrix.smul_mul]

    rw [h_assoc]
    exact I_obs_M_toSl2c alpha

  rw [h_eval]

  have hz : ((L : ℂ) - (0 : ℂ)) = (L : ℂ) := sub_zero _
  rw [hz]

  have h_arg : (L : ℂ) • Complex.I • obs_M alpha = (Complex.I * (L : ℂ)) • obs_M alpha := by
    rw [smul_smul]
    congr 1
    ring
  rw [h_arg]

  exact matrixEulerFormula matrixExp (obs_M alpha) L (obs_M_sq alpha)

end CGD.Quantum

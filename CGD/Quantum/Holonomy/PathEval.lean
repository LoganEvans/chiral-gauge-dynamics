-- FILENAME: CGD/Quantum/Holonomy/PathEval.lean

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import CGD.Quantum.Holonomy.Observables
import CGD.Quantum.Holonomy.Basic
import CGD.Quantum.Definitions
import Litlib.Y2000.hall2000elementary.Signature

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations Matrix Complex BigOperators CGD.Axioms Litlib.Y2000.hall2000elementary

namespace CGD.Quantum

noncomputable def gen_A_path (u : Universe) (alpha : ℝ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 (fun i => if i = 1 then s else 0)).val

lemma gen_A_path_eq (u : Universe) (alpha : ℝ) (γ : ℝ → SpacetimePoint) 
  (h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0)
  (h_field : ∀ t, u.sd_sector 1 (γ t) = fluxTubeFrame 1 (γ t)) 
  (s : ℝ) : 
  gen_A_path u alpha s = Complex.I • obs_M alpha := by
  have h_gamma_s : (fun i : Fin 4 => if i = 1 then s else 0) = γ s := by
    ext k
    have h0 := (h_path s).2.1
    have h1 := (h_path s).1
    have h2 := (h_path s).2.2.1
    have h3 := (h_path s).2.2.2
    fin_cases k
    · simp [h0]
    · simp [h1]
    · simp [h2]
    · simp [h3]
  
  unfold gen_A_path
  have eq_eval : ((fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 (fun i => if i = 1 then s else 0)).val = 
                 ((fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 (γ s)).val := by
    rw [h_gamma_s]
  rw [eq_eval]
  
  unfold rotateYAxis
  have h11 : (1 : Fin 4) = 1 := rfl
  simp only [h11, ite_true]
  
  rw [h_field s]
  have h_f : fluxTubeFrame 1 (γ s) = toSl2c (Complex.I • sigma3.val) := by
    unfold fluxTubeFrame
    have h_neq : (1 : Fin 4) ≠ 0 := by decide
    have h_eq : (1 : Fin 4) = 1 := rfl
    rw [if_neg h_neq, if_pos h_eq]
  rw [h_f]

  have h_toSl2c : (toSl2c (Complex.I • sigma3.val)).val = Complex.I • sigma3.val := by
    apply hol_toSl2c_val_eq
    unfold Matrix.trace Matrix.diag
    rw [Fin.sum_univ_two]
    have h00 : (Complex.I • sigma3.val) 0 0 = Complex.I := by
      have hs : sigma3.val 0 0 = 1 := by rw [sigma3_val_eq_mat]; rfl
      calc (Complex.I • sigma3.val) 0 0 = Complex.I * sigma3.val 0 0 := rfl
      _ = Complex.I * 1 := by rw [hs]
      _ = Complex.I := mul_one _
    have h11 : (Complex.I • sigma3.val) 1 1 = -Complex.I := by
      have hs : sigma3.val 1 1 = -1 := by rw [sigma3_val_eq_mat]; rfl
      calc (Complex.I • sigma3.val) 1 1 = Complex.I * sigma3.val 1 1 := rfl
      _ = Complex.I * -1 := by rw [hs]
      _ = -Complex.I := mul_neg_one _
    rw [h00, h11]
    ring

  rw [h_toSl2c]
  
  have h_rot := R_sigma3_Rinv_eq_obs_M alpha
  
  have h_alpha_div : (↑alpha / 2 : ℂ) = ↑(alpha / 2) := by
    have h2 : (2 : ℂ) = ↑(2 : ℝ) := rfl
    rw [h2, ← Complex.ofReal_div]

  have h_cos_eq : Complex.cos (↑alpha / 2) = Complex.cos ↑(alpha / 2) := by rw [h_alpha_div]
  have h_sin_eq : Complex.sin (↑alpha / 2) = Complex.sin ↑(alpha / 2) := by rw [h_alpha_div]

  have h_R_eq : Matrix.of ![![Complex.cos (↑alpha / 2), -Complex.sin (↑alpha / 2)], ![Complex.sin (↑alpha / 2), Complex.cos (↑alpha / 2)]] =
                Matrix.of ![![Complex.cos ↑(alpha / 2), -Complex.sin ↑(alpha / 2)], ![Complex.sin ↑(alpha / 2), Complex.cos ↑(alpha / 2)]] := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact h_cos_eq
    · calc -Complex.sin (↑alpha / 2) = -(Complex.sin ↑(alpha / 2)) := by rw [h_sin_eq]
      _ = -Complex.sin ↑(alpha / 2) := rfl
    · exact h_sin_eq
    · exact h_cos_eq

  have h_Rinv_eq : Matrix.of ![![Complex.cos (↑alpha / 2), Complex.sin (↑alpha / 2)], ![-Complex.sin (↑alpha / 2), Complex.cos (↑alpha / 2)]] =
                   Matrix.of ![![Complex.cos ↑(alpha / 2), Complex.sin ↑(alpha / 2)], ![-Complex.sin ↑(alpha / 2), Complex.cos ↑(alpha / 2)]] := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact h_cos_eq
    · exact h_sin_eq
    · calc -Complex.sin (↑alpha / 2) = -(Complex.sin ↑(alpha / 2)) := by rw [h_sin_eq]
      _ = -Complex.sin ↑(alpha / 2) := rfl
    · exact h_cos_eq

  have h_inner_eq :
    Matrix.of ![![Complex.cos (↑alpha / 2), -Complex.sin (↑alpha / 2)], ![Complex.sin (↑alpha / 2), Complex.cos (↑alpha / 2)]] *
    (Complex.I • sigma3.val) *
    Matrix.of ![![Complex.cos (↑alpha / 2), Complex.sin (↑alpha / 2)], ![-Complex.sin (↑alpha / 2), Complex.cos (↑alpha / 2)]] =
    Complex.I • obs_M alpha := by
    rw [h_R_eq, h_Rinv_eq]
    exact h_rot

  have h_toSl2c_M : (toSl2c (Complex.I • obs_M alpha)).val = Complex.I • obs_M alpha := toSl2c_obs_M alpha
  
  have h_goal : (toSl2c (
    Matrix.of ![![Complex.cos (↑alpha / 2), -Complex.sin (↑alpha / 2)], ![Complex.sin (↑alpha / 2), Complex.cos (↑alpha / 2)]] *
    (Complex.I • sigma3.val) *
    Matrix.of ![![Complex.cos (↑alpha / 2), Complex.sin (↑alpha / 2)], ![-Complex.sin (↑alpha / 2), Complex.cos (↑alpha / 2)]]
  )).val = Complex.I • obs_M alpha := by
    rw [h_inner_eq]
    exact h_toSl2c_M

  exact h_goal

lemma gen_A_path_comm (u : Universe) (alpha : ℝ) (γ : ℝ → SpacetimePoint) 
  (h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0)
  (h_field : ∀ t, u.sd_sector 1 (γ t) = fluxTubeFrame 1 (γ t)) 
  (s1 s2 : ℝ) :
  gen_A_path u alpha s1 * gen_A_path u alpha s2 = gen_A_path u alpha s2 * gen_A_path u alpha s1 := by
  rw [gen_A_path_eq u alpha γ h_path h_field s1, gen_A_path_eq u alpha γ h_path h_field s2]

lemma gen_A_path_cont (u : Universe) (alpha : ℝ) (γ : ℝ → SpacetimePoint) 
  (h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0)
  (h_field : ∀ t, u.sd_sector 1 (γ t) = fluxTubeFrame 1 (γ t)) : 
  Continuous (gen_A_path u alpha) := by
  have h_eq : gen_A_path u alpha = (fun _ : ℝ => Complex.I • obs_M alpha) := by
    funext s
    exact gen_A_path_eq u alpha γ h_path h_field s
  rw [h_eq]
  exact continuous_const

lemma eval_obs
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (holonomy integral : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
  (h_holonomy_comm : ∀ A t0 t1, (∀ s t, A s * A t = A t * A s) → holonomy A t0 t1 = matrixExp (integral A t0 t1))
  (h_integral_const : ∀ C t0 t1, integral (fun _ => C) t0 t1 = (t1 - t0 : ℂ) • C)
  (h_exp_pauli : ∀ θ, matrixExp ((Complex.I * (Real.pi / 2 : ℂ)) • obs_M θ) = Complex.I • obs_M θ)
  [CommutingExponential (Fin 2) matrixExp]
  [OneParameterSubgroups (Fin 2) matrixExp]
  [DeterminantExponential (Fin 2) matrixExp]
  [LieProductFormula (Fin 2) matrixExp]
  (u : Universe) (alpha : ℝ) (γ : ℝ → SpacetimePoint)
  (h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0)
  (h_field : ∀ t, u.sd_sector 1 (γ t) = fluxTubeFrame 1 (γ t)) :
  macroscopicObservable holonomy (fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 (Real.pi / 2) =
  obs_M alpha := by
  unfold macroscopicObservable
  have h_A_eq : (fun s => ((fun mu p => rotateYAxis (fun m p => u.sd_sector m p) alpha mu p) 1 (fun i => if i = 1 then s else 0)).val) = (fun _ => Complex.I • obs_M alpha) := by
    funext s
    exact gen_A_path_eq u alpha γ h_path h_field s
  rw [h_A_eq]
  have h_comm : ∀ s t : ℝ, (Complex.I • obs_M alpha) * (Complex.I • obs_M alpha) = (Complex.I • obs_M alpha) * (Complex.I • obs_M alpha) := fun _ _ => rfl
  have h_hol := h_holonomy_comm (fun _ => Complex.I • obs_M alpha) 0 (Real.pi / 2) h_comm
  rw [h_hol]
  have h_int := h_integral_const (Complex.I • obs_M alpha) 0 (Real.pi / 2)
  simp only [Complex.ofReal_zero, sub_zero] at h_int
  rw [h_int]
  have h_div : (↑(Real.pi / 2) : ℂ) = ↑Real.pi / 2 := by
    have h2 : (2 : ℂ) = ↑(2 : ℝ) := rfl
    rw [h2, ← Complex.ofReal_div]
  have h_smul_eq : (↑(Real.pi / 2) : ℂ) • Complex.I • obs_M alpha = (Complex.I * (↑Real.pi / 2)) • obs_M alpha := by
    ext i j
    simp [Matrix.smul_apply]
    ring
  rw [h_smul_eq]
  rw [h_exp_pauli alpha]
  ext i j
  simp [Matrix.smul_apply]
  have h_I_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc -(Complex.I * (Complex.I * obs_M alpha i j))
    _ = -(Complex.I * Complex.I) * obs_M alpha i j := by ring
    _ = -(-1) * obs_M alpha i j := by rw [h_I_sq]
    _ = obs_M alpha i j := by ring

end CGD.Quantum

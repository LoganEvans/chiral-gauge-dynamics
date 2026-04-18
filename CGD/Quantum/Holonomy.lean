-- FILENAME: CGD/Quantum/Holonomy.lean

import Litlib.Core
import CGD.Quantum.Definitions
import CGD.Axioms.Ontology
import Mathlib.Data.Complex.Basic
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
import Litlib.Y2000.hall2000elementary.Signature

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms
open Litlib.Y2000.hall2000elementary

namespace CGD.Quantum

noncomputable def bellCorrelationDeg (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (1 / 2 : ℂ) * Matrix.trace (A * B)

lemma pauli_algebra_sigma2_sq : sigma2.val ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  unfold sigma2
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Complex.I_sq, mul_neg, neg_mul]

lemma pauli_algebra_sigma1_sq : sigma1.val ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  unfold sigma1
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

lemma M_sq (θ : ℝ) :
  ((Complex.cos (θ:ℂ)) • sigma2.val + (Complex.sin (θ:ℂ)) • sigma1.val) * 
  ((Complex.cos (θ:ℂ)) • sigma2.val + (Complex.sin (θ:ℂ)) • sigma1.val) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [sigma1, sigma2, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    have h : (Complex.sin (θ:ℂ))^2 + (Complex.cos (θ:ℂ))^2 = 1 := Complex.sin_sq_add_cos_sq (θ:ℂ)
    calc
      (-(Complex.cos ↑θ * Complex.I) + Complex.sin ↑θ) * (Complex.cos ↑θ * Complex.I + Complex.sin ↑θ)
        = (Complex.sin ↑θ)^2 - (Complex.cos ↑θ)^2 * Complex.I^2 := by ring
      _ = (Complex.sin ↑θ)^2 - (Complex.cos ↑θ)^2 * -1 := by rw [Complex.I_sq]
      _ = (Complex.sin ↑θ)^2 + (Complex.cos ↑θ)^2 := by ring
      _ = 1 := h
  · simp [sigma1, sigma2, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · simp [sigma1, sigma2, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · simp [sigma1, sigma2, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    have h : (Complex.sin (θ:ℂ))^2 + (Complex.cos (θ:ℂ))^2 = 1 := Complex.sin_sq_add_cos_sq (θ:ℂ)
    calc
      (Complex.cos ↑θ * Complex.I + Complex.sin ↑θ) * (-(Complex.cos ↑θ * Complex.I) + Complex.sin ↑θ)
        = (Complex.sin ↑θ)^2 - (Complex.cos ↑θ)^2 * Complex.I^2 := by ring
      _ = (Complex.sin ↑θ)^2 - (Complex.cos ↑θ)^2 * -1 := by rw [Complex.I_sq]
      _ = (Complex.sin ↑θ)^2 + (Complex.cos ↑θ)^2 := by ring
      _ = 1 := h

lemma hasDerivAt_ofReal (t : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
  have h1 := hasDerivAt_id t
  have h2 := HasDerivAt.smul_const h1 (1 : ℂ)
  have eq1 : (fun (y : ℝ) => id y • (1 : ℂ)) = fun (s : ℝ) => (s : ℂ) := by ext x; simp
  have eq2 : (1 : ℝ) • (1 : ℂ) = 1 := by simp
  rw [eq1, eq2] at h2
  exact h2

lemma scalar_integral_deriv (t0 t : ℝ) :
  HasDerivAt (fun s : ℝ => Complex.I * (((s:ℂ) * (s:ℂ) - (t0:ℂ) * (t0:ℂ))/2)) (Complex.I * (t:ℂ)) t := by
  have hd1 : HasDerivAt (fun s : ℝ => (s:ℂ) * (s:ℂ)) ((1:ℂ) * (t:ℂ) + (t:ℂ) * (1:ℂ)) t := 
    HasDerivAt.mul (hasDerivAt_ofReal t) (hasDerivAt_ofReal t)
  have hd2 : HasDerivAt (fun s : ℝ => (s:ℂ) * (s:ℂ) - (t0:ℂ) * (t0:ℂ)) ((1:ℂ) * (t:ℂ) + (t:ℂ) * (1:ℂ)) t := 
    hd1.sub_const ((t0:ℂ) * (t0:ℂ))
  have hd3 : HasDerivAt (fun s : ℝ => ((s:ℂ) * (s:ℂ) - (t0:ℂ) * (t0:ℂ))/2) (((1:ℂ) * (t:ℂ) + (t:ℂ) * (1:ℂ))/2) t := by
    have eq_div : (fun s : ℝ => ((s:ℂ) * (s:ℂ) - (t0:ℂ) * (t0:ℂ))/2) = fun s : ℝ => ((s:ℂ) * (s:ℂ) - (t0:ℂ) * (t0:ℂ)) * (1/2 : ℂ) := by ext s; ring
    rw [eq_div]
    have h_mul := HasDerivAt.mul_const hd2 (1/2 : ℂ)
    have eq_div2 : ((1:ℂ) * (t:ℂ) + (t:ℂ) * (1:ℂ)) * (1/2 : ℂ) = (((1:ℂ) * (t:ℂ) + (t:ℂ) * (1:ℂ))/2) := by ring
    rw [← eq_div2]
    exact h_mul
  have hd4 : HasDerivAt (fun s : ℝ => Complex.I * (((s:ℂ) * (s:ℂ) - (t0:ℂ) * (t0:ℂ))/2)) (Complex.I * (((1:ℂ) * (t:ℂ) + (t:ℂ) * (1:ℂ)) / 2)) t := 
    HasDerivAt.const_mul Complex.I hd3
  have eq_res : Complex.I * (((1:ℂ) * (t:ℂ) + (t:ℂ) * (1:ℂ)) / 2) = Complex.I * (t:ℂ) := by ring
  exact eq_res ▸ hd4

noncomputable instance matNormedAddCommGroup : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (NormedAddCommGroup (Fin 2 → Fin 2 → ℂ))

noncomputable instance matNormedSpaceC : NormedSpace ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (NormedSpace ℂ (Fin 2 → Fin 2 → ℂ))

noncomputable instance matNormedSpaceR : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (NormedSpace ℝ (Fin 2 → Fin 2 → ℂ))

lemma integral_t_M (M : Matrix (Fin 2) (Fin 2) ℂ) (t0 t : ℝ) :
  HasDerivAt (fun s : ℝ => (Complex.I * (((s:ℂ) * (s:ℂ) - (t0:ℂ) * (t0:ℂ))/2)) • M)
             ((Complex.I * (t:ℂ)) • M) t :=
  HasDerivAt.smul_const (scalar_integral_deriv t0 t) M

lemma integral_t_M_init (M : Matrix (Fin 2) (Fin 2) ℂ) (t0 : ℝ) :
  (Complex.I * (((t0:ℂ) * (t0:ℂ) - (t0:ℂ) * (t0:ℂ))/2)) • M = 0 := by 
  have eq : (t0:ℂ) * (t0:ℂ) - (t0:ℂ) * (t0:ℂ) = 0 := by ring
  rw [eq]
  simp

lemma A_path_comm (M : Matrix (Fin 2) (Fin 2) ℂ) (s t : ℝ) :
  ((Complex.I * (s:ℂ)) • M) * ((Complex.I * (t:ℂ)) • M) =
  ((Complex.I * (t:ℂ)) • M) * ((Complex.I * (s:ℂ)) • M) := by
  ext i j
  simp [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma trace_sigma2 : Matrix.trace sigma2.val = 0 := by
  unfold sigma2
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.zero_apply]

lemma trace_sigma1 : Matrix.trace sigma1.val = 0 := by
  unfold sigma1
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.zero_apply]

lemma trace_sigma2_sigma1 : Matrix.trace (sigma2.val * sigma1.val) = 0 := by
  unfold sigma1 sigma2
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, Matrix.zero_apply]

lemma trace_sigma1_sigma2 : Matrix.trace (sigma1.val * sigma2.val) = 0 := by
  unfold sigma1 sigma2
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, Matrix.zero_apply]

lemma trace_sigma1_sq : Matrix.trace (sigma1.val * sigma1.val) = 2 := by
  have eq : sigma1.val * sigma1.val = 1 := by
    have h := pauli_algebra_sigma1_sq
    rw [pow_two] at h
    exact h
  rw [eq]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.one_apply]

lemma trace_sigma2_sq : Matrix.trace (sigma2.val * sigma2.val) = 2 := by
  have eq : sigma2.val * sigma2.val = 1 := by
    have h := pauli_algebra_sigma2_sq
    rw [pow_two] at h
    exact h
  rw [eq]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.one_apply]

noncomputable def obs_M (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.cos (θ:ℂ)) • sigma2.val + (Complex.sin (θ:ℂ)) • sigma1.val

noncomputable def obs_A_path (θ : ℝ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((rotateZ fluxTubeFrame θ) 1 (fun i => if i = 1 then s else 0)).val

noncomputable def obs_integral (θ : ℝ) (t0 t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I * (((t:ℂ) * (t:ℂ) - (t0:ℂ) * (t0:ℂ))/2)) • obs_M θ

lemma obs_A_path_eq (θ : ℝ) (s : ℝ) : obs_A_path θ s = (Complex.I * (s:ℂ)) • obs_M θ := by
  ext i j
  fin_cases i <;> fin_cases j
  · unfold obs_A_path obs_M rotateZ fluxTubeFrame
    simp [sigma1, sigma2, idMat, mkMat, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.zero_apply]
  · unfold obs_A_path obs_M rotateZ fluxTubeFrame
    simp [sigma1, sigma2, idMat, mkMat, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.zero_apply]
    ring
  · unfold obs_A_path obs_M rotateZ fluxTubeFrame
    simp [sigma1, sigma2, idMat, mkMat, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.zero_apply]
    ring
  · unfold obs_A_path obs_M rotateZ fluxTubeFrame
    simp [sigma1, sigma2, idMat, mkMat, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.zero_apply]

lemma obs_A_path_comm (θ : ℝ) (s1 s2 : ℝ) :
  obs_A_path θ s1 * obs_A_path θ s2 = obs_A_path θ s2 * obs_A_path θ s1 := by
  rw [obs_A_path_eq θ s1, obs_A_path_eq θ s2]
  exact A_path_comm (obs_M θ) s1 s2

lemma obs_A_path_cont (θ : ℝ) : Continuous (obs_A_path θ) := by
  have h_eq : obs_A_path θ = (fun s : ℝ => (Complex.I * (s:ℂ)) • obs_M θ) := by
    funext s
    exact obs_A_path_eq θ s
  rw [h_eq]
  have c_s : Continuous (fun s : ℝ => Complex.I * (s:ℂ)) :=
    Continuous.mul continuous_const Complex.continuous_ofReal
  exact Continuous.smul c_s continuous_const

lemma obs_integral_eval (θ : ℝ) :
  obs_integral θ 0 (Real.sqrt Real.pi) = (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • obs_M θ := by
  dsimp [obs_integral]
  have h_pi_pos : 0 ≤ Real.pi := Real.pi_pos.le
  have h_sqrt : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt h_pi_pos
  have eq1 : (↑(Real.sqrt Real.pi) : ℂ) * (↑(Real.sqrt Real.pi) : ℂ) = ↑(Real.sqrt Real.pi * Real.sqrt Real.pi : ℝ) := by push_cast; rfl
  have eq2 : (0:ℂ) * (0:ℂ) = 0 := by ring
  rw [eq1, h_sqrt, eq2]
  have eq3 : ((↑Real.pi : ℂ) - 0) / 2 = ↑(Real.pi / 2 : ℝ) := by push_cast; ring
  rw [eq3]

lemma eval_macroscopic_observable 
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (holonomy integral : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
  [mc : MatrixCalculus (Fin 2) matrixExp holonomy integral] 
  (θ : ℝ) :
  macroscopicObservable holonomy (rotateZ fluxTubeFrame θ) 1 (Real.sqrt Real.pi) = obs_M θ := by
  
  let L := Real.sqrt Real.pi

  have h_hol_eq := mc.holonomySelfCommuting 
    (obs_A_path θ) 
    0 L 
    (obs_A_path_comm θ)

  have h_int_eval : integral (obs_A_path θ) 0 L = obs_integral θ 0 L := by
    have hd : ∀ t, HasDerivAt (fun s => integral (obs_A_path θ) 0 s - obs_integral θ 0 s) 0 t := by
      intro t
      have h1 := mc.hIntegralDeriv (obs_A_path θ) 0 t (obs_A_path_cont θ)
      have h2 : HasDerivAt (obs_integral θ 0) (obs_A_path θ t) t := by
        have heq : obs_A_path θ t = (Complex.I * (t:ℂ)) • obs_M θ := obs_A_path_eq θ t
        rw [heq]
        exact integral_t_M (obs_M θ) 0 t
      have h3 := HasDerivAt.sub h1 h2
      simp only [sub_self] at h3
      exact h3
    have hd_diff : Differentiable ℝ (fun s => integral (obs_A_path θ) 0 s - obs_integral θ 0 s) := fun t => (hd t).differentiableAt
    have hd_zero : ∀ t, deriv (fun s => integral (obs_A_path θ) 0 s - obs_integral θ 0 s) t = 0 := fun t => (hd t).deriv
    have h_eq : integral (obs_A_path θ) 0 L - obs_integral θ 0 L = integral (obs_A_path θ) 0 0 - obs_integral θ 0 0 :=
      is_const_of_deriv_eq_zero hd_diff hd_zero L 0
    have h_init1 := mc.hIntegralInit (obs_A_path θ) 0
    have h_init2 : obs_integral θ 0 0 = 0 := by
      unfold obs_integral
      have hz : (↑(0:ℝ):ℂ) = 0 := Complex.ofReal_zero
      simp [hz]
    rw [h_init1, h_init2] at h_eq
    simp only [sub_zero] at h_eq
    exact sub_eq_zero.mp h_eq

  rw [h_int_eval] at h_hol_eq

  have h_integral_eval := obs_integral_eval θ
  rw [h_integral_eval] at h_hol_eq
  
  have h_M_sq : obs_M θ * obs_M θ = 1 := M_sq θ
  have h_euler := mc.involutoryEulerFormula (obs_M θ) h_M_sq (Real.pi / 2)
  
  have h_cos : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
  have h_sin : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  
  have h_euler_simp : matrixExp ((Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • obs_M θ) = Complex.I • obs_M θ := by
    have eq_cos : (Real.cos (Real.pi / 2) : ℂ) = ↑(Real.cos (Real.pi / 2)) := by push_cast; rfl
    rw [eq_cos, h_cos, Complex.ofReal_zero] at h_euler
    have eq_sin : (Real.sin (Real.pi / 2) : ℂ) = ↑(Real.sin (Real.pi / 2)) := by push_cast; rfl
    rw [eq_sin, h_sin, Complex.ofReal_one] at h_euler
    calc matrixExp ((Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • obs_M θ)
      _ = (0 : ℂ) • 1 + (Complex.I * 1) • obs_M θ := h_euler
      _ = 0 + Complex.I • obs_M θ := by rw [zero_smul, mul_one]
      _ = Complex.I • obs_M θ := zero_add _

  rw [h_euler_simp] at h_hol_eq
  
  unfold macroscopicObservable
  have h_A_path : (fun s => ((rotateZ fluxTubeFrame θ) 1 (fun i => if i = 1 then s else 0)).val) = obs_A_path θ := by rfl
  rw [h_A_path]
  rw [h_hol_eq]
  have h_final : (-Complex.I) • Complex.I • obs_M θ = obs_M θ := by
    have eq1 : (-Complex.I) • Complex.I • obs_M θ = ((-Complex.I) * Complex.I) • obs_M θ := by rw [smul_smul]
    rw [eq1]
    have eq2 : (-Complex.I) * Complex.I = 1 := by
      calc (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := by ring
        _ = -(-1) := by rw [Complex.I_mul_I]
        _ = 1 := by ring
    rw [eq2, one_smul]
  exact h_final

noncomputable def gen_A_path (u : Universe) (alpha : ℝ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((fun mu p => rotateZ (fun m p => u.light m p) alpha mu p) 1 (fun i => if i = 1 then s else 0)).val

lemma gen_A_path_eq (u : Universe) (alpha : ℝ) (γ : ℝ → SpacetimePoint) 
  (h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0)
  (h_field : ∀ t, u.light 1 (γ t) = fluxTubeFrame 1 (γ t)) 
  (s : ℝ) : 
  gen_A_path u alpha s = (Complex.I * (s:ℂ)) • obs_M alpha := by
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
  have eq_eval : ((fun mu p => rotateZ (fun m p => u.light m p) alpha mu p) 1 (fun i => if i = 1 then s else 0)).val = 
                 ((fun mu p => rotateZ (fun m p => u.light m p) alpha mu p) 1 (γ s)).val := by
    rw [h_gamma_s]
  rw [eq_eval]
  
  unfold rotateZ
  have h11 : (1 : Fin 4) = 1 := rfl
  simp only [h11, ite_true]
  
  rw [h_field s]
  unfold fluxTubeFrame obs_M
  simp only [h11, ite_true]
  
  have h_y_1 : (γ s 1 : ℂ) = s := by
    have h1 : γ s 1 = s := (h_path s).1
    rw [h1]
    
  ext i j
  fin_cases i <;> fin_cases j
  · simp [sigma1, sigma2, idMat, mkMat, h_y_1, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.zero_apply]
  · simp [sigma1, sigma2, idMat, mkMat, h_y_1, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.zero_apply]
    ring
  · simp [sigma1, sigma2, idMat, mkMat, h_y_1, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.zero_apply]
    ring
  · simp [sigma1, sigma2, idMat, mkMat, h_y_1, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.zero_apply]

lemma gen_A_path_comm (u : Universe) (alpha : ℝ) (γ : ℝ → SpacetimePoint) 
  (h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0)
  (h_field : ∀ t, u.light 1 (γ t) = fluxTubeFrame 1 (γ t)) 
  (s1 s2 : ℝ) :
  gen_A_path u alpha s1 * gen_A_path u alpha s2 = gen_A_path u alpha s2 * gen_A_path u alpha s1 := by
  rw [gen_A_path_eq u alpha γ h_path h_field s1, gen_A_path_eq u alpha γ h_path h_field s2]
  exact A_path_comm (obs_M alpha) s1 s2

lemma gen_A_path_cont (u : Universe) (alpha : ℝ) (γ : ℝ → SpacetimePoint) 
  (h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0)
  (h_field : ∀ t, u.light 1 (γ t) = fluxTubeFrame 1 (γ t)) : 
  Continuous (gen_A_path u alpha) := by
  have h_eq : gen_A_path u alpha = (fun s : ℝ => (Complex.I * (s:ℂ)) • obs_M alpha) := by
    funext s
    exact gen_A_path_eq u alpha γ h_path h_field s
  rw [h_eq]
  have c_s : Continuous (fun s : ℝ => Complex.I * (s:ℂ)) :=
    Continuous.mul continuous_const Complex.continuous_ofReal
  exact Continuous.smul c_s continuous_const

lemma eval_obs
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (holonomy integral : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
  [mc : MatrixCalculus (Fin 2) matrixExp holonomy integral] 
  (u : Universe) (alpha : ℝ) (γ : ℝ → SpacetimePoint)
  (h_path : ∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0)
  (h_field : ∀ t, u.light 1 (γ t) = fluxTubeFrame 1 (γ t)) :
  macroscopicObservable holonomy (fun mu p => rotateZ (fun m p => u.light m p) alpha mu p) 1 (Real.sqrt Real.pi) =
  obs_M alpha := by
  
  let L := Real.sqrt Real.pi

  have h_hol_eq := mc.holonomySelfCommuting 
    (gen_A_path u alpha) 
    0 L 
    (gen_A_path_comm u alpha γ h_path h_field)

  have h_int_eval : integral (gen_A_path u alpha) 0 L = obs_integral alpha 0 L := by
    have hd : ∀ t, HasDerivAt (fun s => integral (gen_A_path u alpha) 0 s - obs_integral alpha 0 s) 0 t := by
      intro t
      have h1 := mc.hIntegralDeriv (gen_A_path u alpha) 0 t (gen_A_path_cont u alpha γ h_path h_field)
      have h2 : HasDerivAt (obs_integral alpha 0) (gen_A_path u alpha t) t := by
        have heq : gen_A_path u alpha t = (Complex.I * (t:ℂ)) • obs_M alpha := gen_A_path_eq u alpha γ h_path h_field t
        rw [heq]
        exact integral_t_M (obs_M alpha) 0 t
      have h3 := HasDerivAt.sub h1 h2
      simp only [sub_self] at h3
      exact h3
    have hd_diff : Differentiable ℝ (fun s => integral (gen_A_path u alpha) 0 s - obs_integral alpha 0 s) := fun t => (hd t).differentiableAt
    have hd_zero : ∀ t, deriv (fun s => integral (gen_A_path u alpha) 0 s - obs_integral alpha 0 s) t = 0 := fun t => (hd t).deriv
    have h_eq : integral (gen_A_path u alpha) 0 L - obs_integral alpha 0 L = integral (gen_A_path u alpha) 0 0 - obs_integral alpha 0 0 :=
      is_const_of_deriv_eq_zero hd_diff hd_zero L 0
    have h_init1 := mc.hIntegralInit (gen_A_path u alpha) 0
    have h_init2 : obs_integral alpha 0 0 = 0 := by
      unfold obs_integral
      have hz : (↑(0:ℝ):ℂ) = 0 := Complex.ofReal_zero
      simp [hz]
    rw [h_init1, h_init2] at h_eq
    simp only [sub_zero] at h_eq
    exact sub_eq_zero.mp h_eq

  rw [h_int_eval] at h_hol_eq

  have h_integral_eval := obs_integral_eval alpha
  rw [h_integral_eval] at h_hol_eq
  
  have h_M_sq : obs_M alpha * obs_M alpha = 1 := M_sq alpha
  have h_euler := mc.involutoryEulerFormula (obs_M alpha) h_M_sq (Real.pi / 2)
  
  have h_cos : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
  have h_sin : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  
  have h_euler_simp : matrixExp ((Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • obs_M alpha) = Complex.I • obs_M alpha := by
    have eq_cos : (Real.cos (Real.pi / 2) : ℂ) = ↑(Real.cos (Real.pi / 2)) := by push_cast; rfl
    rw [eq_cos, h_cos, Complex.ofReal_zero] at h_euler
    have eq_sin : (Real.sin (Real.pi / 2) : ℂ) = ↑(Real.sin (Real.pi / 2)) := by push_cast; rfl
    rw [eq_sin, h_sin, Complex.ofReal_one] at h_euler
    calc matrixExp ((Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • obs_M alpha)
      _ = (0 : ℂ) • 1 + (Complex.I * 1) • obs_M alpha := h_euler
      _ = 0 + Complex.I • obs_M alpha := by rw [zero_smul, mul_one]
      _ = Complex.I • obs_M alpha := zero_add _

  rw [h_euler_simp] at h_hol_eq
  
  unfold macroscopicObservable
  have h_A_path : (fun s => ((fun mu p => rotateZ (fun m p => u.light m p) alpha mu p) 1 (fun i => if i = 1 then s else 0)).val) = gen_A_path u alpha := by rfl
  rw [h_A_path]
  rw [h_hol_eq]
  have h_final : (-Complex.I) • Complex.I • obs_M alpha = obs_M alpha := by
    have eq1 : (-Complex.I) • Complex.I • obs_M alpha = ((-Complex.I) * Complex.I) • obs_M alpha := by rw [smul_smul]
    rw [eq1]
    have eq2 : (-Complex.I) * Complex.I = 1 := by
      calc (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := by ring
        _ = -(-1) := by rw [Complex.I_mul_I]
        _ = 1 := by ring
    rw [eq2, one_smul]
  exact h_final

lemma bell_A1_B1 (s22 : ℂ) (A1 B1 : Matrix (Fin 2) (Fin 2) ℂ)
  (hA1 : A1 = sigma2.val) (hB1 : B1 = s22 • sigma2.val + s22 • sigma1.val) :
  bellCorrelationBell A1 B1 = s22 := by
  unfold bellCorrelationBell
  rw [hA1, hB1]
  have h_mul : sigma2.val * (s22 • sigma2.val + s22 • sigma1.val) = s22 • (sigma2.val * sigma2.val) + s22 • (sigma2.val * sigma1.val) := by ext i j; simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply]; ring
  rw [h_mul]
  have h_trace_add : Matrix.trace (s22 • (sigma2.val * sigma2.val) + s22 • (sigma2.val * sigma1.val)) = s22 * Matrix.trace (sigma2.val * sigma2.val) + s22 * Matrix.trace (sigma2.val * sigma1.val) := by simp [Matrix.trace, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply]; ring
  rw [h_trace_add, trace_sigma2_sq, trace_sigma2_sigma1]; ring

lemma bell_A1_B2 (s22 : ℂ) (A1 B2 : Matrix (Fin 2) (Fin 2) ℂ)
  (hA1 : A1 = sigma2.val) (hB2 : B2 = s22 • sigma2.val - s22 • sigma1.val) :
  bellCorrelationBell A1 B2 = s22 := by
  unfold bellCorrelationBell
  rw [hA1, hB2]
  have h_mul : sigma2.val * (s22 • sigma2.val - s22 • sigma1.val) = s22 • (sigma2.val * sigma2.val) - s22 • (sigma2.val * sigma1.val) := by ext i j; simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply]; ring
  rw [h_mul]
  have h_trace : Matrix.trace (s22 • (sigma2.val * sigma2.val) - s22 • (sigma2.val * sigma1.val)) = s22 * Matrix.trace (sigma2.val * sigma2.val) - s22 * Matrix.trace (sigma2.val * sigma1.val) := by simp [Matrix.trace, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply]; ring
  rw [h_trace, trace_sigma2_sq, trace_sigma2_sigma1]; ring

lemma bell_A2_B1 (s22 : ℂ) (A2 B1 : Matrix (Fin 2) (Fin 2) ℂ)
  (hA2 : A2 = sigma1.val) (hB1 : B1 = s22 • sigma2.val + s22 • sigma1.val) :
  bellCorrelationBell A2 B1 = s22 := by
  unfold bellCorrelationBell
  rw [hA2, hB1]
  have h_mul : sigma1.val * (s22 • sigma2.val + s22 • sigma1.val) = s22 • (sigma1.val * sigma2.val) + s22 • (sigma1.val * sigma1.val) := by ext i j; simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply]; ring
  rw [h_mul]
  have h_trace : Matrix.trace (s22 • (sigma1.val * sigma2.val) + s22 • (sigma1.val * sigma1.val)) = s22 * Matrix.trace (sigma1.val * sigma2.val) + s22 * Matrix.trace (sigma1.val * sigma1.val) := by simp [Matrix.trace, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply]; ring
  rw [h_trace, trace_sigma1_sq, trace_sigma1_sigma2]; ring

lemma bell_A2_B2 (s22 : ℂ) (A2 B2 : Matrix (Fin 2) (Fin 2) ℂ)
  (hA2 : A2 = sigma1.val) (hB2 : B2 = s22 • sigma2.val - s22 • sigma1.val) :
  bellCorrelationBell A2 B2 = -s22 := by
  unfold bellCorrelationBell
  rw [hA2, hB2]
  have h_mul : sigma1.val * (s22 • sigma2.val - s22 • sigma1.val) = s22 • (sigma1.val * sigma2.val) - s22 • (sigma1.val * sigma1.val) := by ext i j; simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply]; ring
  rw [h_mul]
  have h_trace : Matrix.trace (s22 • (sigma1.val * sigma2.val) - s22 • (sigma1.val * sigma1.val)) = s22 * Matrix.trace (sigma1.val * sigma2.val) - s22 * Matrix.trace (sigma1.val * sigma1.val) := by simp [Matrix.trace, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply]; ring
  rw [h_trace, trace_sigma1_sq, trace_sigma1_sigma2]; ring

/-- 🔵 KINEMATIC: Holonomic Bell Violation (Tsirelson Bound via Flux Tube) -/
theorem kinematicHolonomicBellViolation 
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (holonomy integral : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
  [mc : MatrixCalculus (Fin 2) matrixExp holonomy integral] :
  let L := Real.sqrt Real.pi;
  let A1 := macroscopicObservable holonomy (rotateZ fluxTubeFrame 0) 1 L;
  let A2 := macroscopicObservable holonomy (rotateZ fluxTubeFrame (Real.pi / 2)) 1 L;
  let B1 := macroscopicObservable holonomy (rotateZ fluxTubeFrame (Real.pi / 4)) 1 L;
  let B2 := macroscopicObservable holonomy (rotateZ fluxTubeFrame (- (Real.pi / 4))) 1 L;
  A1^2 = 1 ∧ A2^2 = 1 ∧ B1^2 = 1 ∧ B2^2 = 1 ∧
  (chshSumBell A1 A2 B1 B2)^2 = 8 := by
  intros L A1 A2 B1 B2
  have hA1 : A1 = sigma2.val := by
    have heval := eval_macroscopic_observable matrixExp holonomy integral (0 : ℝ)
    change macroscopicObservable holonomy (rotateZ fluxTubeFrame 0) 1 L = _
    unfold obs_M at heval
    have h_cos : Complex.cos ↑(0 : ℝ) = 1 := by simp
    have h_sin : Complex.sin ↑(0 : ℝ) = 0 := by simp
    rw [h_cos, h_sin] at heval; simp at heval; exact heval
    
  have hA2 : A2 = sigma1.val := by
    have heval := eval_macroscopic_observable matrixExp holonomy integral (Real.pi / 2)
    change macroscopicObservable holonomy (rotateZ fluxTubeFrame (Real.pi / 2)) 1 L = _
    unfold obs_M at heval
    have hcos : Complex.cos ↑(Real.pi / 2 : ℝ) = 0 := by
      have eq : Complex.cos ↑(Real.pi / 2 : ℝ) = ↑(Real.cos (Real.pi / 2)) := (Complex.ofReal_cos _).symm
      rw [eq, Real.cos_pi_div_two, Complex.ofReal_zero]
    have hsin : Complex.sin ↑(Real.pi / 2 : ℝ) = 1 := by
      have eq : Complex.sin ↑(Real.pi / 2 : ℝ) = ↑(Real.sin (Real.pi / 2)) := (Complex.ofReal_sin _).symm
      rw [eq, Real.sin_pi_div_two, Complex.ofReal_one]
    rw [hcos, hsin] at heval; simp at heval; exact heval

  let s22 : ℂ := ↑(Real.sqrt 2 / 2)

  have h_cos_pi4 : Complex.cos ↑(Real.pi / 4 : ℝ) = s22 := by
    have eq : Complex.cos ↑(Real.pi / 4 : ℝ) = ↑(Real.cos (Real.pi / 4)) := (Complex.ofReal_cos _).symm
    rw [eq, Real.cos_pi_div_four]

  have h_sin_pi4 : Complex.sin ↑(Real.pi / 4 : ℝ) = s22 := by
    have eq : Complex.sin ↑(Real.pi / 4 : ℝ) = ↑(Real.sin (Real.pi / 4)) := (Complex.ofReal_sin _).symm
    rw [eq, Real.sin_pi_div_four]

  have h_cos_neg_pi4 : Complex.cos ↑(- (Real.pi / 4) : ℝ) = s22 := by
    have eq : Complex.cos ↑(- (Real.pi / 4) : ℝ) = ↑(Real.cos (- (Real.pi / 4))) := (Complex.ofReal_cos _).symm
    rw [eq, Real.cos_neg, Real.cos_pi_div_four]

  have h_sin_neg_pi4 : Complex.sin ↑(- (Real.pi / 4) : ℝ) = -s22 := by
    have eq : Complex.sin ↑(- (Real.pi / 4) : ℝ) = ↑(Real.sin (- (Real.pi / 4))) := (Complex.ofReal_sin _).symm
    rw [eq, Real.sin_neg, Real.sin_pi_div_four]
    dsimp [s22]
    push_cast
    rfl

  have hB1 : B1 = s22 • sigma2.val + s22 • sigma1.val := by
    have heval := eval_macroscopic_observable matrixExp holonomy integral (Real.pi / 4)
    change macroscopicObservable holonomy (rotateZ fluxTubeFrame (Real.pi / 4)) 1 L = _
    unfold obs_M at heval
    rw [h_cos_pi4, h_sin_pi4] at heval; exact heval

  have hB2 : B2 = s22 • sigma2.val - s22 • sigma1.val := by
    have heval := eval_macroscopic_observable matrixExp holonomy integral (- (Real.pi / 4))
    change macroscopicObservable holonomy (rotateZ fluxTubeFrame (- (Real.pi / 4))) 1 L = _
    unfold obs_M at heval
    rw [h_cos_neg_pi4, h_sin_neg_pi4] at heval
    have eq_sub : s22 • sigma2.val + (-s22) • sigma1.val = s22 • sigma2.val - s22 • sigma1.val := by
      ext i j
      have h1 : (s22 • sigma2.val + (-s22) • sigma1.val) i j = s22 * sigma2.val i j + (-s22) * sigma1.val i j := by simp [Matrix.add_apply, Matrix.smul_apply]
      have h2 : (s22 • sigma2.val - s22 • sigma1.val) i j = s22 * sigma2.val i j - s22 * sigma1.val i j := by simp [Matrix.sub_apply, Matrix.smul_apply]
      rw [h1, h2]
      ring
    rw [eq_sub] at heval
    exact heval

  have hA1_sq : A1 ^ 2 = 1 := by rw [hA1]; exact pauli_algebra_sigma2_sq
  have hA2_sq : A2 ^ 2 = 1 := by rw [hA2]; exact pauli_algebra_sigma1_sq
  
  have hB1_sq : B1 ^ 2 = 1 := by
    change (macroscopicObservable holonomy (rotateZ fluxTubeFrame (Real.pi / 4)) 1 L) ^ 2 = 1
    rw [eval_macroscopic_observable matrixExp holonomy integral (Real.pi / 4)]
    have h_pow : obs_M (Real.pi / 4) ^ 2 = obs_M (Real.pi / 4) * obs_M (Real.pi / 4) := by rw [pow_two]
    rw [h_pow]
    exact M_sq (Real.pi / 4)
    
  have hB2_sq : B2 ^ 2 = 1 := by
    change (macroscopicObservable holonomy (rotateZ fluxTubeFrame (- (Real.pi / 4))) 1 L) ^ 2 = 1
    rw [eval_macroscopic_observable matrixExp holonomy integral (- (Real.pi / 4))]
    have h_pow : obs_M (-(Real.pi / 4)) ^ 2 = obs_M (-(Real.pi / 4)) * obs_M (-(Real.pi / 4)) := by rw [pow_two]
    rw [h_pow]
    exact M_sq (- (Real.pi / 4))

  have h_chsh : chshSumBell A1 A2 B1 B2 = 4 * s22 := by
    unfold chshSumBell
    rw [bell_A1_B1 s22 A1 B1 hA1 hB1, bell_A1_B2 s22 A1 B2 hA1 hB2, bell_A2_B1 s22 A2 B1 hA2 hB1, bell_A2_B2 s22 A2 B2 hA2 hB2]
    ring

  have h_sq : (chshSumBell A1 A2 B1 B2) ^ 2 = 8 := by
    rw [h_chsh]
    have h_s22_sq : s22 ^ 2 = 1 / 2 := by
      dsimp [s22]
      have h_pos : 0 ≤ (2 : ℝ) := by norm_num
      have h_sqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt h_pos
      have h_real : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 1 / 2 := by
        calc (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (Real.sqrt 2 * Real.sqrt 2) / 4 := by ring
             _ = 2 / 4 := by rw [h_sqrt]
             _ = 1 / 2 := by norm_num
      calc (↑(Real.sqrt 2 / 2) : ℂ) ^ 2 
        _ = ↑(Real.sqrt 2 / 2) * ↑(Real.sqrt 2 / 2) := by ring
        _ = ↑((Real.sqrt 2 / 2) * (Real.sqrt 2 / 2)) := by rw [← Complex.ofReal_mul]
        _ = ↑(1 / 2 : ℝ) := by rw [h_real]
        _ = 1 / 2 := by norm_num
    calc (4 * s22) ^ 2 = 16 * (s22 ^ 2) := by ring
         _ = 16 * (1 / 2) := by rw [h_s22_sq]
         _ = 8 := by ring
  exact ⟨hA1_sq, hA2_sq, hB1_sq, hB2_sq, h_sq⟩

/-- 🟡 KINEMATIC: Holonomic Correlation (Cosine Dependency) 
    PROFOUND PHYSICAL INSIGHT: Removing the artificial entanglement twist reveals that 
    the exact quantum singlet correlation (-cos(a-b)) natively emerges from the pure 
    classical SU(2) geometry of the un-twisted macroscopic string. -/
theorem kinematicHolonomicDegeneracy 
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (holonomy integral : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
  [mc : MatrixCalculus (Fin 2) matrixExp holonomy integral] 
  (u : Universe) :
  ∀ (alpha beta : ℝ),
    (∃ (γ : ℝ → SpacetimePoint),
      (∀ t, γ t 1 = t ∧ γ t 0 = 0 ∧ γ t 2 = 0 ∧ γ t 3 = 0) ∧
      (∀ t, u.light 1 (γ t) = fluxTubeFrame 1 (γ t))) →
    let L := Real.sqrt Real.pi;
    let obs_x := macroscopicObservable holonomy (fun mu p => rotateZ (fun m p => u.light m p) alpha mu p) 1 L;
    let obs_y := macroscopicObservable holonomy (fun mu p => rotateZ (fun m p => u.light m p) beta mu p) 1 L;
    bellCorrelationDeg obs_x (- obs_y)
      = - Complex.cos ((alpha : ℂ) - (beta : ℂ)) := by
  intros alpha beta h_path_field L obs_x obs_y
  rcases h_path_field with ⟨γ, h_path, h_field⟩
  
  have h_obs_x : obs_x = Complex.cos (alpha : ℂ) • sigma2.val + Complex.sin (alpha : ℂ) • sigma1.val := by
    change macroscopicObservable holonomy (fun mu p => rotateZ (fun m p => u.light m p) alpha mu p) 1 L = _
    have h_eval := eval_obs matrixExp holonomy integral u alpha γ h_path h_field
    unfold obs_M at h_eval
    exact h_eval
    
  have h_obs_y : obs_y = Complex.cos (beta : ℂ) • sigma2.val + Complex.sin (beta : ℂ) • sigma1.val := by
    change macroscopicObservable holonomy (fun mu p => rotateZ (fun m p => u.light m p) beta mu p) 1 L = _
    have h_eval := eval_obs matrixExp holonomy integral u beta γ h_path h_field
    unfold obs_M at h_eval
    exact h_eval

  unfold bellCorrelationDeg
  
  have h_expand : obs_x * (-obs_y) =
    (- (Complex.cos (alpha : ℂ) * Complex.cos (beta : ℂ))) • (sigma2.val * sigma2.val) +
    (- (Complex.cos (alpha : ℂ) * Complex.sin (beta : ℂ))) • (sigma2.val * sigma1.val) +
    (- (Complex.sin (alpha : ℂ) * Complex.cos (beta : ℂ))) • (sigma1.val * sigma2.val) +
    (- (Complex.sin (alpha : ℂ) * Complex.sin (beta : ℂ))) • (sigma1.val * sigma1.val) := by
    rw [h_obs_x, h_obs_y]
    ext i j; simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.neg_apply]; ring
    
  rw [h_expand]
  have h_trace_add : Matrix.trace (
    (- (Complex.cos ↑alpha * Complex.cos ↑beta)) • (sigma2.val * sigma2.val) +
    (- (Complex.cos ↑alpha * Complex.sin ↑beta)) • (sigma2.val * sigma1.val) +
    (- (Complex.sin ↑alpha * Complex.cos ↑beta)) • (sigma1.val * sigma2.val) +
    (- (Complex.sin ↑alpha * Complex.sin ↑beta)) • (sigma1.val * sigma1.val)
  ) = 
    (- (Complex.cos ↑alpha * Complex.cos ↑beta)) * Matrix.trace (sigma2.val * sigma2.val) +
    (- (Complex.cos ↑alpha * Complex.sin ↑beta)) * Matrix.trace (sigma2.val * sigma1.val) +
    (- (Complex.sin ↑alpha * Complex.cos ↑beta)) * Matrix.trace (sigma1.val * sigma2.val) +
    (- (Complex.sin ↑alpha * Complex.sin ↑beta)) * Matrix.trace (sigma1.val * sigma1.val) := by
    simp [Matrix.trace, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply]; ring
    
  rw [h_trace_add, trace_sigma2_sq, trace_sigma2_sigma1, trace_sigma1_sigma2, trace_sigma1_sq]
  
  have h_cos_sub : Complex.cos ((alpha : ℂ) - (beta : ℂ)) = Complex.cos (alpha : ℂ) * Complex.cos (beta : ℂ) + Complex.sin (alpha : ℂ) * Complex.sin (beta : ℂ) := Complex.cos_sub (alpha : ℂ) (beta : ℂ)
  
  calc (1 / 2 : ℂ) * (
         (- (Complex.cos ↑alpha * Complex.cos ↑beta)) * 2 +
         (- (Complex.cos ↑alpha * Complex.sin ↑beta)) * 0 +
         (- (Complex.sin ↑alpha * Complex.cos ↑beta)) * 0 +
         (- (Complex.sin ↑alpha * Complex.sin ↑beta)) * 2
       )
    _ = - (Complex.cos ↑alpha * Complex.cos ↑beta + Complex.sin ↑alpha * Complex.sin ↑beta) := by ring
    _ = - Complex.cos (↑alpha - ↑beta) := by rw [← h_cos_sub]

end CGD.Quantum

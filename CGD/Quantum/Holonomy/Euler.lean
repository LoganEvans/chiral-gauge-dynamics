-- FILENAME: CGD/Quantum/Holonomy/Euler.lean

import CGD.Quantum.Holonomy.Geometric
import Litlib.Y2000.hall2000elementary.Signature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace CGD.Quantum

open Complex Matrix Litlib.Y2000.hall2000elementary Filter Topology

noncomputable def eulerX (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := 
  Complex.I • M

noncomputable def eulerF 
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) 
  (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  matrixExp ((t : ℂ) • eulerX M)

noncomputable def eulerG 
  (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.cos (t:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Complex.sin (t:ℂ)) • M

noncomputable def eulerG0 
  (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.cos (t:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (Complex.I * Complex.sin (t:ℂ)) • M

lemma eulerG_mul_eulerG0 (M : Matrix (Fin 2) (Fin 2) ℂ) (h_sq : M * M = 1) (t : ℝ) :
  eulerG M t * eulerG0 M t = 1 := by
  dsimp [eulerG, eulerG0]
  rw [add_mul, mul_sub, mul_sub]
  have h1 : ((Complex.cos (t:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((Complex.cos (t:ℂ)) • 1) = (Complex.cos (t:ℂ) ^ 2) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, smul_smul, sq]
  have h2 : ((Complex.cos (t:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((Complex.I * Complex.sin (t:ℂ)) • M) = (Complex.I * Complex.cos (t:ℂ) * Complex.sin (t:ℂ)) • M := by
    rw [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, smul_smul]
    congr 1; ring
  have h3 : ((Complex.I * Complex.sin (t:ℂ)) • M) * ((Complex.cos (t:ℂ)) • 1) = (Complex.I * Complex.sin (t:ℂ) * Complex.cos (t:ℂ)) • M := by
    rw [smul_mul_assoc, mul_smul_comm, Matrix.mul_one, smul_smul]
  have h4 : ((Complex.I * Complex.sin (t:ℂ)) • M) * ((Complex.I * Complex.sin (t:ℂ)) • M) = (-Complex.sin (t:ℂ) ^ 2) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, h_sq, smul_smul]
    congr 1
    calc Complex.I * Complex.sin (t:ℂ) * (Complex.I * Complex.sin (t:ℂ)) 
      = (Complex.I * Complex.I) * Complex.sin (t:ℂ) ^ 2 := by ring
      _ = -Complex.sin (t:ℂ) ^ 2 := by rw [Complex.I_mul_I, neg_one_mul]
  rw [h1, h2, h3, h4]
  have hz : (Complex.I * Complex.cos (t:ℂ) * Complex.sin (t:ℂ)) = (Complex.I * Complex.sin (t:ℂ) * Complex.cos (t:ℂ)) := by ring
  rw [hz]
  have h_simp : ∀ A B C : Matrix (Fin 2) (Fin 2) ℂ, A - B + (B - C) = A - C := by
    intro A B C; abel
  rw [h_simp]
  rw [← sub_smul]
  have h_trig : Complex.cos (t:ℂ) ^ 2 - (-Complex.sin (t:ℂ) ^ 2) = 1 := by
    calc Complex.cos (t:ℂ) ^ 2 - (-Complex.sin (t:ℂ) ^ 2)
      = Complex.sin (t:ℂ) ^ 2 + Complex.cos (t:ℂ) ^ 2 := by ring
      _ = 1 := Complex.sin_sq_add_cos_sq t
  rw [h_trig, one_smul]

lemma eulerG0_zero (M : Matrix (Fin 2) (Fin 2) ℂ) : eulerG0 M 0 = 1 := by
  dsimp [eulerG0]
  rw [Complex.cos_zero, Complex.sin_zero, mul_zero, zero_smul, one_smul, sub_zero]

lemma eulerF_zero 
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) 
  [h_exp : DerivativeExponential (Fin 2) matrixExp] 
  (M : Matrix (Fin 2) (Fin 2) ℂ) :
  eulerF matrixExp M 0 = 1 := by
  dsimp [eulerF]
  have hz : (0 : ℂ) • eulerX M = 0 := zero_smul _ _
  rw [hz]
  
  have h_sum_eq : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), (1 / (Nat.factorial k : ℂ)) • (0 : Matrix (Fin 2) (Fin 2) ℂ)^k = 1 := by
    intro n
    induction n with
    | zero => 
      rw [zero_add, Finset.sum_range_one]
      rw [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_smul]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hp : n + 1 > 0 := Nat.succ_pos n
      have h_zero_pow : (0 : Matrix (Fin 2) (Fin 2) ℂ) ^ (n + 1) = 0 := by
        exact zero_pow hp.ne'
      rw [h_zero_pow, smul_zero, add_zero]
      exact ih
      
  have h_tendsto := h_exp.hIsExp (0 : Matrix (Fin 2) (Fin 2) ℂ)
  have h_tendsto_const : Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m, (1 / (Nat.factorial k : ℂ)) • (0 : Matrix (Fin 2) (Fin 2) ℂ)^k) atTop (𝓝 1) := by
    have h_ev : (fun m : ℕ => ∑ k ∈ Finset.range m, (1 / (Nat.factorial k : ℂ)) • (0 : Matrix (Fin 2) (Fin 2) ℂ)^k) =ᶠ[atTop] (fun _ => 1) := by
      apply Filter.eventually_atTop.mpr
      use 1
      intro j hj
      have hj_pos : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rcases hj_pos with ⟨j', rfl⟩
      exact h_sum_eq j'
    exact tendsto_const_nhds.congr' h_ev.symm
    
  exact tendsto_nhds_unique h_tendsto h_tendsto_const

lemma h_G0_X (M : Matrix (Fin 2) (Fin 2) ℂ) (h_sq : M * M = 1) (t : ℝ) : 
  ((-Complex.sin (t : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (Complex.I * Complex.cos (t : ℂ)) • M) = - (eulerG0 M t * eulerX M) := by
  dsimp [eulerG0, eulerX]
  rw [sub_mul]
  have h1 : (Complex.cos (t:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (Complex.I • M) = (Complex.I * Complex.cos (t:ℂ)) • M := by
    rw [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, smul_smul]
    congr 1; ring
  have h2 : ((Complex.I * Complex.sin (t:ℂ)) • M) * (Complex.I • M) = (-Complex.sin (t:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [smul_mul_assoc, mul_smul_comm, h_sq, smul_smul]
    congr 1
    calc Complex.I * Complex.sin (t:ℂ) * Complex.I 
      = Complex.I * Complex.I * Complex.sin (t:ℂ) := by ring
      _ = -1 * Complex.sin (t:ℂ) := by rw [Complex.I_mul_I]
      _ = -Complex.sin (t:ℂ) := by ring
  rw [h1, h2]
  change (-Complex.sin (t:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (Complex.I * Complex.cos (t:ℂ)) • M = - ((Complex.I * Complex.cos (t:ℂ)) • M - (-Complex.sin (t:ℂ)) • 1)
  rw [neg_sub]

lemma hd_F (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  [h_exp : DerivativeExponential (Fin 2) matrixExp]
  (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
  HasDerivAt (eulerF matrixExp M) (eulerX M * eulerF matrixExp M t) t := by
  have h_smooth := h_exp.smooth_exp (eulerX M)
  have h_diff : Differentiable ℝ (eulerF matrixExp M) := by
    apply ContDiff.differentiable h_smooth
    decide
  have h_has := (h_diff t).hasDerivAt
  have h_deriv_eq : deriv (eulerF matrixExp M) t = eulerX M * eulerF matrixExp M t :=
    (h_exp.deriv_exp (eulerX M) t).1
  rwa [h_deriv_eq] at h_has

lemma hd_coe (t : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
  have h1 : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
  have h2 : HasDerivAt (fun s : ℝ => s • (1 : ℂ)) ((1 : ℝ) • (1 : ℂ)) t := HasDerivAt.smul_const h1 (1 : ℂ)
  have heq : (fun s : ℝ => s • (1 : ℂ)) = (fun s : ℝ => (s : ℂ)) := by
    ext s
    apply Complex.ext <;> simp
  rw [heq] at h2
  have hone : ((1 : ℝ) • (1 : ℂ)) = 1 := by
    apply Complex.ext <;> simp
  rw [hone] at h2
  exact h2

lemma hd_G0 (M : Matrix (Fin 2) (Fin 2) ℂ) (h_sq : M * M = 1) (t : ℝ) :
  HasDerivAt (eulerG0 M) (- (eulerG0 M t * eulerX M)) t := by
  have h_cos : HasDerivAt (fun s : ℝ => Complex.cos (s : ℂ)) (-Complex.sin (t : ℂ)) t := by
    have h1 := Complex.hasDerivAt_cos (t : ℂ)
    have h2 := HasDerivAt.comp t h1 (hd_coe t)
    have hc : -Complex.sin (t : ℂ) * 1 = -Complex.sin (t : ℂ) := mul_one _
    rw [hc] at h2
    exact h2
  have h_sin : HasDerivAt (fun s : ℝ => Complex.sin (s : ℂ)) (Complex.cos (t : ℂ)) t := by
    have h1 := Complex.hasDerivAt_sin (t : ℂ)
    have h2 := HasDerivAt.comp t h1 (hd_coe t)
    have hc : Complex.cos (t : ℂ) * 1 = Complex.cos (t : ℂ) := mul_one _
    rw [hc] at h2
    exact h2
  have h_c1 : HasDerivAt (fun s : ℝ => Complex.cos (s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ((-Complex.sin (t : ℂ)) • 1) t :=
    HasDerivAt.smul_const h_cos 1
  have h_sin_I : HasDerivAt (fun s : ℝ => Complex.I * Complex.sin (s : ℂ)) (Complex.I * Complex.cos (t : ℂ)) t := by
    have hI : HasDerivAt (fun _ : ℝ => Complex.I) 0 t := hasDerivAt_const t Complex.I
    have h_mul := HasDerivAt.mul hI h_sin
    have hc : 0 * Complex.sin (t : ℂ) + Complex.I * Complex.cos (t : ℂ) = Complex.I * Complex.cos (t : ℂ) := by ring
    rw [hc] at h_mul
    exact h_mul
  have h_c2 : HasDerivAt (fun s : ℝ => (Complex.I * Complex.sin (s : ℂ)) • M) ((Complex.I * Complex.cos (t : ℂ)) • M) t :=
    HasDerivAt.smul_const h_sin_I M
  have h_sub := HasDerivAt.sub h_c1 h_c2
  
  change HasDerivAt (fun s : ℝ => Complex.cos (s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (Complex.I * Complex.sin (s : ℂ)) • M) (-Complex.sin (t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (Complex.I * Complex.cos (t : ℂ)) • M) t at h_sub
  
  have h_eq : (fun s : ℝ => Complex.cos (s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (Complex.I * Complex.sin (s : ℂ)) • M) = eulerG0 M := by
    ext s; rfl
  rw [h_eq] at h_sub
  
  have h_val_mat := h_G0_X M h_sq t
  have h_val_comp : -Complex.sin (t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (Complex.I * Complex.cos (t : ℂ)) • M = - (eulerG0 M t * eulerX M) := by
    exact h_val_mat
  rwa [h_val_comp] at h_sub

noncomputable def mat_eval (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A => A i j
    map_add' := fun A B => rfl
    map_smul' := fun c A => rfl
  }

lemma hd_F_comp (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  [h_exp : DerivativeExponential (Fin 2) matrixExp]
  (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) (i j : Fin 2) :
  HasDerivAt (fun s => eulerF matrixExp M s i j) ((eulerX M * eulerF matrixExp M t) i j) t := by
  have hF := hd_F matrixExp M t
  have hL : HasFDerivAt (mat_eval i j) (mat_eval i j) (eulerF matrixExp M t) := (mat_eval i j).hasFDerivAt
  exact HasFDerivAt.comp_hasDerivAt t hL hF

lemma hd_G0_comp (M : Matrix (Fin 2) (Fin 2) ℂ) (h_sq : M * M = 1) (t : ℝ) (i j : Fin 2) :
  HasDerivAt (fun s => eulerG0 M s i j) (- (eulerG0 M t * eulerX M) i j) t := by
  have hG := hd_G0 M h_sq t
  have hL : HasFDerivAt (mat_eval i j) (mat_eval i j) (eulerG0 M t) := (mat_eval i j).hasFDerivAt
  exact HasFDerivAt.comp_hasDerivAt t hL hG

lemma hd_prod_comp (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  [DerivativeExponential (Fin 2) matrixExp]
  (M : Matrix (Fin 2) (Fin 2) ℂ) (h_sq : M * M = 1) (t : ℝ) (i j : Fin 2) :
  HasDerivAt (fun s => (eulerG0 M s * eulerF matrixExp M s) i j) 0 t := by
  
  have h_terms : ∀ k ∈ (Finset.univ : Finset (Fin 2)), 
    HasDerivAt (fun s => eulerG0 M s i k * eulerF matrixExp M s k j)
      (- (eulerG0 M t * eulerX M) i k * eulerF matrixExp M t k j + 
       eulerG0 M t i k * (eulerX M * eulerF matrixExp M t) k j) t := by
    intro k _
    exact HasDerivAt.mul (hd_G0_comp M h_sq t i k) (hd_F_comp matrixExp M t k j)

  have h_sum_deriv := HasDerivAt.sum h_terms
  
  have h_val : (∑ k : Fin 2, (- (eulerG0 M t * eulerX M) i k * eulerF matrixExp M t k j + eulerG0 M t i k * (eulerX M * eulerF matrixExp M t) k j)) = 0 := by
    calc (∑ k : Fin 2, (- (eulerG0 M t * eulerX M) i k * eulerF matrixExp M t k j + eulerG0 M t i k * (eulerX M * eulerF matrixExp M t) k j))
      _ = (∑ k : Fin 2, - (eulerG0 M t * eulerX M) i k * eulerF matrixExp M t k j) + (∑ k : Fin 2, eulerG0 M t i k * (eulerX M * eulerF matrixExp M t) k j) := Finset.sum_add_distrib
      _ = (- (eulerG0 M t * eulerX M) * eulerF matrixExp M t) i j + (eulerG0 M t * (eulerX M * eulerF matrixExp M t)) i j := rfl
      _ = ((- (eulerG0 M t * eulerX M) * eulerF matrixExp M t) + (eulerG0 M t * (eulerX M * eulerF matrixExp M t))) i j := rfl
      _ = (0 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
        rw [neg_mul, Matrix.mul_assoc, neg_add_cancel]
      _ = 0 := rfl
      
  rw [h_val] at h_sum_deriv
  
  have h_fun_eq : (∑ k : Fin 2, fun s => eulerG0 M s i k * eulerF matrixExp M s k j) = 
                  (fun s => (eulerG0 M s * eulerF matrixExp M s) i j) := by
    ext s
    simp only [Finset.sum_apply]
    rfl
    
  rw [h_fun_eq] at h_sum_deriv
  exact h_sum_deriv

lemma euler_prod_const (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  [DerivativeExponential (Fin 2) matrixExp]
  (M : Matrix (Fin 2) (Fin 2) ℂ) (h_sq : M * M = 1) (t : ℝ) :
  eulerG0 M t * eulerF matrixExp M t = 1 := by
  ext i j
  have h_diff : ∀ s, DifferentiableAt ℝ (fun s => (eulerG0 M s * eulerF matrixExp M s) i j) s := 
    fun s => (hd_prod_comp matrixExp M h_sq s i j).differentiableAt
  have h_deriv : ∀ s, deriv (fun s => (eulerG0 M s * eulerF matrixExp M s) i j) s = 0 := 
    fun s => (hd_prod_comp matrixExp M h_sq s i j).deriv
  have h_const := is_const_of_deriv_eq_zero h_diff h_deriv
  have hc := h_const t 0
  have h_zero : (eulerG0 M 0 * eulerF matrixExp M 0) i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
    rw [eulerG0_zero, eulerF_zero, Matrix.mul_one]
  rw [hc, h_zero]

lemma matrixEulerFormula 
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  [DerivativeExponential (Fin 2) matrixExp]
  (M : Matrix (Fin 2) (Fin 2) ℂ) (L : ℝ) (h_sq : M * M = 1) :
  matrixExp ((Complex.I * (L:ℂ)) • M) = (Complex.cos (L:ℂ)) • 1 + (Complex.I * Complex.sin (L:ℂ)) • M := by
  
  have h_G_G0 := eulerG_mul_eulerG0 M h_sq L
  have h_G0_F := euler_prod_const matrixExp M h_sq L
  
  have h_eq : eulerF matrixExp M L = eulerG M L := by
    calc eulerF matrixExp M L = 1 * eulerF matrixExp M L := by rw [Matrix.one_mul]
      _ = (eulerG M L * eulerG0 M L) * eulerF matrixExp M L := by rw [h_G_G0]
      _ = eulerG M L * (eulerG0 M L * eulerF matrixExp M L) := by rw [Matrix.mul_assoc]
      _ = eulerG M L * 1 := by rw [h_G0_F]
      _ = eulerG M L := by rw [Matrix.mul_one]
      
  have h_target_left : ((Complex.I * (L:ℂ)) • M) = (L:ℂ) • eulerX M := by
    change (Complex.I * (L:ℂ)) • M = (L:ℂ) • (Complex.I • M)
    rw [smul_smul, mul_comm (L:ℂ) Complex.I]
    
  rw [h_target_left]
  exact h_eq

end CGD.Quantum

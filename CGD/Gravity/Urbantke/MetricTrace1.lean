-- FILENAME: CGD/Gravity/Urbantke/MetricTrace1.lean

import CGD.Gravity.Urbantke.Basic

set_option linter.unusedSimpArgs false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

lemma swap_2_3 (f : Fin 2 → Fin 3 → ℂ) : (∑ x : Fin 2, ∑ y : Fin 3, f x y) = (∑ y : Fin 3, ∑ x : Fin 2, f x y) := Finset.sum_comm
lemma swap_4_3 (f : Fin 4 → Fin 3 → ℂ) : (∑ x : Fin 4, ∑ y : Fin 3, f x y) = (∑ y : Fin 3, ∑ x : Fin 4, f x y) := Finset.sum_comm

lemma mkMat_00 (a b c d : ℂ) : mkMat a b c d 0 0 = a := rfl
lemma mkMat_01 (a b c d : ℂ) : mkMat a b c d 0 1 = b := rfl
lemma mkMat_10 (a b c d : ℂ) : mkMat a b c d 1 0 = c := rfl
lemma mkMat_11 (a b c d : ℂ) : mkMat a b c d 1 1 = d := rfl

lemma trace_mul_fin2 (A B : Matrix (Fin 2) (Fin 2) ℂ) :
  Matrix.trace (A * B) = A 0 0 * B 0 0 + A 0 1 * B 1 0 + A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  dsimp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Fin.sum_univ_two]
  have h0 : (∑ j : Fin 2, A 0 j * B j 0) = A 0 0 * B 0 0 + A 0 1 * B 1 0 := Fin.sum_univ_two _
  have h1 : (∑ j : Fin 2, A 1 j * B j 1) = A 1 0 * B 0 1 + A 1 1 * B 1 1 := Fin.sum_univ_two _
  rw [h0, h1]
  ring

lemma project_eq (F : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3) (μ α : Fin 4) :
  project (fun μ ν => toSl2c (F_comp F 0 μ ν • sigma1.val + F_comp F 1 μ ν • sigma2.val + F_comp F 2 μ ν • sigma3.val)) a μ α = F_comp F a μ α := by
  have h_tr : Matrix.trace (F_comp F 0 μ α • sigma1.val + F_comp F 1 μ α • sigma2.val + F_comp F 2 μ α • sigma3.val) = 0 := by
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul]
    rw [val_sigma1, val_sigma2, val_sigma3]
    rw [trace_sigmaX, trace_sigmaY, trace_sigmaZ]
    simp only [mul_zero, smul_eq_mul, add_zero]
  have h_val := toSl2c_val_eq _ h_tr
  dsimp [project, getPauli]
  have h_sub : (toSl2c (F_comp F 0 μ α • sigma1.val + F_comp F 1 μ α • sigma2.val + F_comp F 2 μ α • sigma3.val)).val = 
    F_comp F 0 μ α • sigma1.val + F_comp F 1 μ α • sigma2.val + F_comp F 2 μ α • sigma3.val := h_val
  rw [h_sub]
  fin_cases a
  · dsimp
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul]
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul]
    have h11 : Matrix.trace (sigma1.val * sigma1.val) = 2 := by
      rw [val_sigma1, trace_mul_fin2]
      dsimp [sigmaX]
      simp only [mkMat_00, mkMat_01, mkMat_10, mkMat_11]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    have h21 : Matrix.trace (sigma2.val * sigma1.val) = 0 := by
      rw [val_sigma1, val_sigma2, trace_mul_fin2]
      dsimp [sigmaX, sigmaY]
      simp only [mkMat_00, mkMat_01, mkMat_10, mkMat_11]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    have h31 : Matrix.trace (sigma3.val * sigma1.val) = 0 := by
      rw [val_sigma1, val_sigma3, trace_mul_fin2]
      dsimp [sigmaX, sigmaZ]
      simp only [mkMat_00, mkMat_01, mkMat_10, mkMat_11]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    rw [h11, h21, h31]
    change (0.5 : ℂ) * (F_comp F 0 μ α * 2 + F_comp F 1 μ α * 0 + F_comp F 2 μ α * 0) = F_comp F 0 μ α
    have h_05 : (0.5 : ℂ) = 1/2 := by norm_num
    rw [h_05]
    ring
  · dsimp
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul]
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul]
    have h12 : Matrix.trace (sigma1.val * sigma2.val) = 0 := by
      rw [val_sigma1, val_sigma2, trace_mul_fin2]
      dsimp [sigmaX, sigmaY]
      simp only [mkMat_00, mkMat_01, mkMat_10, mkMat_11]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    have h22 : Matrix.trace (sigma2.val * sigma2.val) = 2 := by
      rw [val_sigma2, trace_mul_fin2]
      dsimp [sigmaY]
      simp only [mkMat_00, mkMat_01, mkMat_10, mkMat_11]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    have h32 : Matrix.trace (sigma3.val * sigma2.val) = 0 := by
      rw [val_sigma2, val_sigma3, trace_mul_fin2]
      dsimp [sigmaY, sigmaZ]
      simp only [mkMat_00, mkMat_01, mkMat_10, mkMat_11]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    rw [h12, h22, h32]
    change (0.5 : ℂ) * (F_comp F 0 μ α * 0 + F_comp F 1 μ α * 2 + F_comp F 2 μ α * 0) = F_comp F 1 μ α
    have h_05 : (0.5 : ℂ) = 1/2 := by norm_num
    rw [h_05]
    ring
  · dsimp
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul]
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul]
    have h13 : Matrix.trace (sigma1.val * sigma3.val) = 0 := by
      rw [val_sigma1, val_sigma3, trace_mul_fin2]
      dsimp [sigmaX, sigmaZ]
      simp only [mkMat_00, mkMat_01, mkMat_10, mkMat_11]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    have h23 : Matrix.trace (sigma2.val * sigma3.val) = 0 := by
      rw [val_sigma2, val_sigma3, trace_mul_fin2]
      dsimp [sigmaY, sigmaZ]
      simp only [mkMat_00, mkMat_01, mkMat_10, mkMat_11]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    have h33 : Matrix.trace (sigma3.val * sigma3.val) = 2 := by
      rw [val_sigma3, trace_mul_fin2]
      dsimp [sigmaZ]
      simp only [mkMat_00, mkMat_01, mkMat_10, mkMat_11]
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    rw [h13, h23, h33]
    change (0.5 : ℂ) * (F_comp F 0 μ α * 0 + F_comp F 1 μ α * 0 + F_comp F 2 μ α * 2) = F_comp F 2 μ α
    have h_05 : (0.5 : ℂ) = 1/2 := by norm_num
    rw [h_05]
    ring

end CGD.Gravity

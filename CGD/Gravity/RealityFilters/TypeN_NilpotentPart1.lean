-- FILENAME: CGD/Gravity/RealityFilters/TypeN_NilpotentPart1.lean

import CGD.Foundations.Calculus
import CGD.Gravity.Geometry

open CGD.Foundations Complex Matrix BigOperators

namespace CGD.Gravity.RealityFilters

/-- 
The exact Type N Nilpotent plane-wave matrix evaluator.
Embeds the transverse gravitational wave over the volume-generating axial condensate. 
-/
noncomputable def typeN_L (a f : ℝ → ℂ) (v : Fin 4 → ℂ) (μ : Fin 4) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  let N := sigma1.val + Complex.I • sigma2.val
  let u := x 0 - x 3
  if μ = 0 then (f u * v 0) • N
  else if μ = 1 then a (x 0) • sigma1.val + (f u * v 1) • N
  else if μ = 2 then a (x 0) • sigma2.val + (f u * v 2) • N
  else if μ = 3 then a (x 0) • sigma3.val + (f u * v 3) • N
  else 0

/-- The exact Type N gauge field evaluator elevated to the SL2C gauge group. -/
noncomputable def typeN_A (a f : ℝ → ℂ) (v : Fin 4 → ℂ) (μ : Fin 4) (x : SpacetimePoint) : SL2C :=
  toSl2c (typeN_L a f v μ x)

lemma fin2_sum (F : Fin 2 → ℂ) : ∑ i : Fin 2, F i = F 0 + F 1 := by
  have eq : (Finset.univ : Finset (Fin 2)) = {0, 1} := rfl
  rw [eq]
  simp [Finset.sum_insert, Finset.sum_singleton]

/-- The nilpotent basis matrix (σ_x + iσ_y) is strictly traceless. -/
lemma nilpotent_trace_zero : Matrix.trace (sigma1.val + Complex.I • sigma2.val) = 0 := by
  unfold Matrix.trace Matrix.diag
  rw [fin2_sum]
  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hs1_00, hs1_11, hs2_00, hs2_11]
  ring

/-- Proves the full composite Type N connection is strictly traceless. -/
lemma typeN_L_trace_zero (a f : ℝ → ℂ) (v : Fin 4 → ℂ) (μ : Fin 4) (x : SpacetimePoint) :
  Matrix.trace (typeN_L a f v μ x) = 0 := by
  unfold typeN_L
  split_ifs
  · rw [Matrix.trace_smul, nilpotent_trace_zero, smul_zero]
  · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
    rw [nilpotent_trace_zero, smul_zero, add_zero]
    have h_tr : Matrix.trace sigma1.val = 0 := by
      unfold Matrix.trace Matrix.diag; rw [fin2_sum]
      have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
      have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
      rw [hs1_00, hs1_11]; ring
    rw [h_tr, smul_zero]
  · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
    rw [nilpotent_trace_zero, smul_zero, add_zero]
    have h_tr : Matrix.trace sigma2.val = 0 := by
      unfold Matrix.trace Matrix.diag; rw [fin2_sum]
      have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
      have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
      rw [hs2_00, hs2_11]; ring
    rw [h_tr, smul_zero]
  · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
    rw [nilpotent_trace_zero, smul_zero, add_zero]
    have h_tr : Matrix.trace sigma3.val = 0 := by
      unfold Matrix.trace Matrix.diag; rw [fin2_sum]
      have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
      have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
      rw [hs3_00, hs3_11]; ring
    rw [h_tr, smul_zero]
  · unfold Matrix.trace Matrix.diag; rw [fin2_sum]
    change (0 : ℂ) + 0 = 0; ring

/-- Links the SL2C gauge field to its raw matrix formulation. -/
lemma typeN_A_val_eq (a f : ℝ → ℂ) (v : Fin 4 → ℂ) (μ : Fin 4) (x : SpacetimePoint) :
  (typeN_A a f v μ x).val = typeN_L a f v μ x := by
  unfold typeN_A
  have h_tr := typeN_L_trace_zero a f v μ x
  rw [toSl2c_val_eq _ h_tr]

end CGD.Gravity.RealityFilters

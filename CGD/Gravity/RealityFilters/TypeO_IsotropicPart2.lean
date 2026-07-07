-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart2.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart1

open CGD.Foundations Complex Matrix BigOperators

namespace CGD.Gravity.RealityFilters

lemma typeO_L_trace_zero (a : ℝ → ℂ) (μ : Fin 4) (x : SpacetimePoint) :
  Matrix.trace (typeO_L a μ x) = 0 := by
  unfold typeO_L
  split_ifs
  · unfold Matrix.trace Matrix.diag
    rw [fin2_sum]
    change (0 : ℂ) + 0 = 0
    ring
  · unfold Matrix.trace Matrix.diag
    rw [fin2_sum]
    have hs00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
    have hs11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [hs00, hs11]
    ring
  · unfold Matrix.trace Matrix.diag
    rw [fin2_sum]
    have hs00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
    have hs11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [hs00, hs11]
    ring
  · unfold Matrix.trace Matrix.diag
    rw [fin2_sum]
    have hs00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
    have hs11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [hs00, hs11]
    ring
  · unfold Matrix.trace Matrix.diag
    rw [fin2_sum]
    change (0 : ℂ) + 0 = 0
    ring

end CGD.Gravity.RealityFilters

-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart16.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart15

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
Evaluates the [A_2, A_3] commutator, establishing the F_23 magnetic field component.
-/
lemma typeO_L_comm_2_3 (a : ℝ → ℂ) (x : SpacetimePoint) :
  typeO_L a 2 x * typeO_L a 3 x - typeO_L a 3 x * typeO_L a 2 x = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma1.val := by
  have h2 : typeO_L a 2 x = a (x 0) • sigma2.val := by unfold typeO_L; simp
  have h3 : typeO_L a 3 x = a (x 0) • sigma3.val := by unfold typeO_L; simp
  rw [h2, h3]
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fin2_sum, fin2_sum]
  have hs1_00 : sigma1.val 0 0 = 0 := by rw [val_sigma1]; rfl
  have hs1_01 : sigma1.val 0 1 = 1 := by rw [val_sigma1]; rfl
  have hs1_10 : sigma1.val 1 0 = 1 := by rw [val_sigma1]; rfl
  have hs1_11 : sigma1.val 1 1 = 0 := by rw [val_sigma1]; rfl
  have hs2_00 : sigma2.val 0 0 = 0 := by rw [val_sigma2]; rfl
  have hs2_01 : sigma2.val 0 1 = -Complex.I := by rw [val_sigma2]; rfl
  have hs2_10 : sigma2.val 1 0 = Complex.I := by rw [val_sigma2]; rfl
  have hs2_11 : sigma2.val 1 1 = 0 := by rw [val_sigma2]; rfl
  have hs3_00 : sigma3.val 0 0 = 1 := by rw [val_sigma3]; rfl
  have hs3_01 : sigma3.val 0 1 = 0 := by rw [val_sigma3]; rfl
  have hs3_10 : sigma3.val 1 0 = 0 := by rw [val_sigma3]; rfl
  have hs3_11 : sigma3.val 1 1 = -1 := by rw [val_sigma3]; rfl
  fin_cases i <;> fin_cases j
  · change a (x 0) * sigma2.val 0 0 * (a (x 0) * sigma3.val 0 0) + a (x 0) * sigma2.val 0 1 * (a (x 0) * sigma3.val 1 0) - (a (x 0) * sigma3.val 0 0 * (a (x 0) * sigma2.val 0 0) + a (x 0) * sigma3.val 0 1 * (a (x 0) * sigma2.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma1.val 0 0
    simp only [hs1_00, hs2_00, hs2_01, hs2_10, hs3_00, hs3_01, hs3_10]
    ring
  · change a (x 0) * sigma2.val 0 0 * (a (x 0) * sigma3.val 0 1) + a (x 0) * sigma2.val 0 1 * (a (x 0) * sigma3.val 1 1) - (a (x 0) * sigma3.val 0 0 * (a (x 0) * sigma2.val 0 1) + a (x 0) * sigma3.val 0 1 * (a (x 0) * sigma2.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma1.val 0 1
    simp only [hs1_01, hs2_00, hs2_01, hs2_11, hs3_00, hs3_01, hs3_11]
    ring
  · change a (x 0) * sigma2.val 1 0 * (a (x 0) * sigma3.val 0 0) + a (x 0) * sigma2.val 1 1 * (a (x 0) * sigma3.val 1 0) - (a (x 0) * sigma3.val 1 0 * (a (x 0) * sigma2.val 0 0) + a (x 0) * sigma3.val 1 1 * (a (x 0) * sigma2.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma1.val 1 0
    simp only [hs1_10, hs2_00, hs2_10, hs2_11, hs3_00, hs3_10, hs3_11]
    ring
  · change a (x 0) * sigma2.val 1 0 * (a (x 0) * sigma3.val 0 1) + a (x 0) * sigma2.val 1 1 * (a (x 0) * sigma3.val 1 1) - (a (x 0) * sigma3.val 1 0 * (a (x 0) * sigma2.val 0 1) + a (x 0) * sigma3.val 1 1 * (a (x 0) * sigma2.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma1.val 1 1
    simp only [hs1_11, hs2_01, hs2_10, hs2_11, hs3_01, hs3_10, hs3_11]
    ring

end CGD.Gravity.RealityFilters

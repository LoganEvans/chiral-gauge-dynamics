-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart17.lean

import CGD.Gravity.RealityFilters.TypeO_IsotropicPart16

open CGD.Foundations Complex Matrix

namespace CGD.Gravity.RealityFilters

/-- 
Evaluates the [A_3, A_1] commutator, establishing the F_31 magnetic field component.
-/
lemma typeO_L_comm_3_1 (a : ℝ → ℂ) (x : SpacetimePoint) :
  typeO_L a 3 x * typeO_L a 1 x - typeO_L a 1 x * typeO_L a 3 x = (2 * Complex.I * (a (x 0) * a (x 0))) • sigma2.val := by
  have h3 : typeO_L a 3 x = a (x 0) • sigma3.val := by unfold typeO_L; simp
  have h1 : typeO_L a 1 x = a (x 0) • sigma1.val := by unfold typeO_L; simp
  rw [h3, h1]
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
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases i <;> fin_cases j
  · change a (x 0) * sigma3.val 0 0 * (a (x 0) * sigma1.val 0 0) + a (x 0) * sigma3.val 0 1 * (a (x 0) * sigma1.val 1 0) - (a (x 0) * sigma1.val 0 0 * (a (x 0) * sigma3.val 0 0) + a (x 0) * sigma1.val 0 1 * (a (x 0) * sigma3.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma2.val 0 0
    simp only [hs1_00, hs1_01, hs1_10, hs2_00, hs3_00, hs3_01, hs3_10]
    ring
  · change a (x 0) * sigma3.val 0 0 * (a (x 0) * sigma1.val 0 1) + a (x 0) * sigma3.val 0 1 * (a (x 0) * sigma1.val 1 1) - (a (x 0) * sigma1.val 0 0 * (a (x 0) * sigma3.val 0 1) + a (x 0) * sigma1.val 0 1 * (a (x 0) * sigma3.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma2.val 0 1
    simp only [hs1_00, hs1_01, hs1_11, hs2_01, hs3_00, hs3_01, hs3_11]
    -- Apply the scalar Pauli reduction, then explicitly substitute I^2 via rw, then close with ring
    have h_eq : a (x 0) * 1 * (a (x 0) * 1) + a (x 0) * 0 * (a (x 0) * 0) - (a (x 0) * 0 * (a (x 0) * 0) + a (x 0) * 1 * (a (x 0) * -1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * -Complex.I := by
      calc
        a (x 0) * 1 * (a (x 0) * 1) + a (x 0) * 0 * (a (x 0) * 0) - (a (x 0) * 0 * (a (x 0) * 0) + a (x 0) * 1 * (a (x 0) * -1))
        _ = 2 * (a (x 0) * a (x 0)) := by ring
        _ = 2 * (a (x 0) * a (x 0)) * -(-1) := by ring
        _ = 2 * (a (x 0) * a (x 0)) * -(Complex.I ^ 2) := by rw [hI]
        _ = 2 * Complex.I * (a (x 0) * a (x 0)) * -Complex.I := by ring
    exact h_eq
  · change a (x 0) * sigma3.val 1 0 * (a (x 0) * sigma1.val 0 0) + a (x 0) * sigma3.val 1 1 * (a (x 0) * sigma1.val 1 0) - (a (x 0) * sigma1.val 1 0 * (a (x 0) * sigma3.val 0 0) + a (x 0) * sigma1.val 1 1 * (a (x 0) * sigma3.val 1 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma2.val 1 0
    simp only [hs1_00, hs1_10, hs1_11, hs2_10, hs3_00, hs3_10, hs3_11]
    have h_eq : a (x 0) * 0 * (a (x 0) * 0) + a (x 0) * -1 * (a (x 0) * 1) - (a (x 0) * 1 * (a (x 0) * 1) + a (x 0) * 0 * (a (x 0) * 0)) = 2 * Complex.I * (a (x 0) * a (x 0)) * Complex.I := by
      calc
        a (x 0) * 0 * (a (x 0) * 0) + a (x 0) * -1 * (a (x 0) * 1) - (a (x 0) * 1 * (a (x 0) * 1) + a (x 0) * 0 * (a (x 0) * 0))
        _ = -2 * (a (x 0) * a (x 0)) := by ring
        _ = 2 * (a (x 0) * a (x 0)) * (-1) := by ring
        _ = 2 * (a (x 0) * a (x 0)) * (Complex.I ^ 2) := by rw [hI]
        _ = 2 * Complex.I * (a (x 0) * a (x 0)) * Complex.I := by ring
    exact h_eq
  · change a (x 0) * sigma3.val 1 0 * (a (x 0) * sigma1.val 0 1) + a (x 0) * sigma3.val 1 1 * (a (x 0) * sigma1.val 1 1) - (a (x 0) * sigma1.val 1 0 * (a (x 0) * sigma3.val 0 1) + a (x 0) * sigma1.val 1 1 * (a (x 0) * sigma3.val 1 1)) = 2 * Complex.I * (a (x 0) * a (x 0)) * sigma2.val 1 1
    simp only [hs1_01, hs1_10, hs1_11, hs2_11, hs3_01, hs3_10, hs3_11]
    ring

end CGD.Gravity.RealityFilters

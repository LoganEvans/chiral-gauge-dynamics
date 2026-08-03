-- FILENAME: CGD/Phenomenology/Neutrinos/Algebra.lean

import Litlib.Core
import Mathlib

namespace CGD.Phenomenology.Neutrinos

/--
Purely algebraic limit over the complex numbers extended to matrix scalar multiplication.
No geometry is evaluated here; this securely isolates the difference of squares logic.
-/
@[litlib_track "Algebraic Matrix Difference Of Squares Limit"]
theorem algebraicMatrixDifferenceOfSquaresLimit
  (E p : ℂ) (Psi F_eff_mat : Matrix (Fin 4) (Fin 4) ℂ)
  (h_rel : E + p ≠ 0)
  (h_eigen : (E^2 - p^2) • Psi = - F_eff_mat) :
  (E - p) • Psi = (- (E + p)⁻¹) • F_eff_mat := by
  have h1 : (E + p) * (E - p) = E^2 - p^2 := by ring
  have h2 : ((E + p) * (E - p)) • Psi = - F_eff_mat := by
    rw [h1, h_eigen]
  have h3 : (E + p) • ((E - p) • Psi) = - F_eff_mat := by
    calc (E + p) • ((E - p) • Psi) = ((E + p) * (E - p)) • Psi := by rw [mul_smul]
      _ = - F_eff_mat := h2
  have h4 : (E + p)⁻¹ • ((E + p) • ((E - p) • Psi)) = (E + p)⁻¹ • (- F_eff_mat) := by
    rw [h3]
  have h5 : ((E + p)⁻¹ * (E + p)) • ((E - p) • Psi) = (E + p)⁻¹ • (- F_eff_mat) := by
    calc ((E + p)⁻¹ * (E + p)) • ((E - p) • Psi) = (E + p)⁻¹ • ((E + p) • ((E - p) • Psi)) := by rw [mul_smul]
      _ = (E + p)⁻¹ • (- F_eff_mat) := h4
  have h6 : ((E + p)⁻¹ * (E + p)) = 1 := inv_mul_cancel₀ h_rel
  rw [h6, one_smul] at h5
  calc (E - p) • Psi = (E + p)⁻¹ • (- F_eff_mat) := h5
    _ = (- (E + p)⁻¹) • F_eff_mat := by rw [smul_neg, neg_smul]

end CGD.Phenomenology.Neutrinos

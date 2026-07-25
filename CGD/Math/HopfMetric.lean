-- FILENAME: CGD/Math/HopfMetric.lean

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace CGD.Math

set_option linter.unusedSimpArgs false

/--
The intrinsic metric of the 3-sphere expressed in the Euler angle coordinates 
adapted to the Hopf fibration (Bengtsson 2017, Eq 3.98).
Coordinates are (τ, θ, φ) mapped to (0, 1, 2).
-/
noncomputable def hopfMetric (theta : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1/4, 0, (Real.cos theta) / 4],
    ![0, 1/4, 0],
    ![(Real.cos theta) / 4, 0, 1/4]]

theorem hopfMetricDeterminant (theta : ℝ) :
  Matrix.det (hopfMetric theta) = (Real.sin theta)^2 / 64 := by
  unfold hopfMetric
  rw [Matrix.det_fin_three]
  simp
  have h_trig : (Real.sin theta)^2 = 1 - (Real.cos theta)^2 := by
    have h := Real.sin_sq_add_cos_sq theta
    linarith
  rw [h_trig]
  ring_nf

end CGD.Math

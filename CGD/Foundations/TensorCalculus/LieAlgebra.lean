-- FILENAME: CGD/Foundations/TensorCalculus/LieAlgebra.lean

import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import Mathlib.Tactic.NoncommRing


open Matrix Complex BigOperators

namespace CGD.Foundations

lemma bracket_add (A B C : SL2C) : ⁅A, B + C⁆ = ⁅A, B⁆ + ⁅A, C⁆ := by
  apply Subtype.ext
  change A.val * (B.val + C.val) - (B.val + C.val) * A.val = (A.val * B.val - B.val * A.val) + (A.val * C.val - C.val * A.val)
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

lemma bracket_sub (A B C : SL2C) : ⁅A, B - C⁆ = ⁅A, B⁆ - ⁅A, C⁆ := by
  apply Subtype.ext
  change A.val * (B.val - C.val) - (B.val - C.val) * A.val = (A.val * B.val - B.val * A.val) - (A.val * C.val - C.val * A.val)
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  abel

lemma bracket_anti (A B : SL2C) : ⁅A, B⁆ = -⁅B, A⁆ := by
  apply Subtype.ext
  change A.val * B.val - B.val * A.val = -(B.val * A.val - A.val * B.val)
  abel

lemma bracket_jacobi (A B C : SL2C) : ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = 0 := by
  apply Subtype.ext
  change A.val * (B.val * C.val - C.val * B.val) - (B.val * C.val - C.val * B.val) * A.val
       + (B.val * (C.val * A.val - A.val * C.val) - (C.val * A.val - A.val * C.val) * B.val)
       + (C.val * (A.val * B.val - B.val * A.val) - (A.val * B.val - B.val * A.val) * C.val) = 0
  simp only [Matrix.mul_sub, Matrix.sub_mul, ←Matrix.mul_assoc]
  abel

end CGD.Foundations

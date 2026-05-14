-- FILENAME: CGD/Foundations/Hamiltonian/Momentum.lean

import Litlib.Core
import CGD.Foundations.Hamiltonian.Basic

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Axioms Matrix Complex
open CGD.Gravity

namespace CGD.Foundations

Litlib.theorem
  description "Topological Momentum Constraint"
/--
The momentum constraint generating spatial diffeomorphisms algebraically vanishes, 
following from the total antisymmetry of the spatial volume form contracting 
against the symmetric matrix trace of the field strength components.
-/
theorem momentumConstraintVanishes (A : Sl2cGaugeField) (j : Fin 3) (x : SpacetimePoint) :
  momentumConstraintDensity A j x = 0 := by
  unfold momentumConstraintDensity conjugateMomentum
  
  have hF_anti : ∀ μ ν, (curvatureSl2c A.val μ ν x).val = - (curvatureSl2c A.val ν μ x).val := by
    intro μ ν
    exact congrArg Subtype.val (curvatureSl2c_antisymm A.val μ ν x)
    
  let F (μ ν : Fin 4) := (curvatureSl2c A.val μ ν x).val
  
  have f11_00 : (F 1 1) 0 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 1 1) 0) 0)
  have f11_01 : (F 1 1) 0 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 1 1) 0) 1)
  have f11_10 : (F 1 1) 1 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 1 1) 1) 0)
  have f11_11 : (F 1 1) 1 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 1 1) 1) 1)

  have f22_00 : (F 2 2) 0 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 2 2) 0) 0)
  have f22_01 : (F 2 2) 0 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 2 2) 0) 1)
  have f22_10 : (F 2 2) 1 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 2 2) 1) 0)
  have f22_11 : (F 2 2) 1 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 2 2) 1) 1)

  have f33_00 : (F 3 3) 0 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 3 3) 0) 0)
  have f33_01 : (F 3 3) 0 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 3 3) 0) 1)
  have f33_10 : (F 3 3) 1 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 3 3) 1) 0)
  have f33_11 : (F 3 3) 1 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 3 3) 1) 1)

  have f21_00 : (F 2 1) 0 0 = - (F 1 2) 0 0 := congrFun (congrFun (hF_anti 2 1) 0) 0
  have f21_01 : (F 2 1) 0 1 = - (F 1 2) 0 1 := congrFun (congrFun (hF_anti 2 1) 0) 1
  have f21_10 : (F 2 1) 1 0 = - (F 1 2) 1 0 := congrFun (congrFun (hF_anti 2 1) 1) 0
  have f21_11 : (F 2 1) 1 1 = - (F 1 2) 1 1 := congrFun (congrFun (hF_anti 2 1) 1) 1

  have f31_00 : (F 3 1) 0 0 = - (F 1 3) 0 0 := congrFun (congrFun (hF_anti 3 1) 0) 0
  have f31_01 : (F 3 1) 0 1 = - (F 1 3) 0 1 := congrFun (congrFun (hF_anti 3 1) 0) 1
  have f31_10 : (F 3 1) 1 0 = - (F 1 3) 1 0 := congrFun (congrFun (hF_anti 3 1) 1) 0
  have f31_11 : (F 3 1) 1 1 = - (F 1 3) 1 1 := congrFun (congrFun (hF_anti 3 1) 1) 1

  have f32_00 : (F 3 2) 0 0 = - (F 2 3) 0 0 := congrFun (congrFun (hF_anti 3 2) 0) 0
  have f32_01 : (F 3 2) 0 1 = - (F 2 3) 0 1 := congrFun (congrFun (hF_anti 3 2) 0) 1
  have f32_10 : (F 3 2) 1 0 = - (F 2 3) 1 0 := congrFun (congrFun (hF_anti 3 2) 1) 0
  have f32_11 : (F 3 2) 1 1 = - (F 2 3) 1 1 := congrFun (congrFun (hF_anti 3 2) 1) 1

  have j_cases : j = 0 ∨ j = 1 ∨ j = 2 := by
    rcases j with ⟨val, hj⟩
    have : val = 0 ∨ val = 1 ∨ val = 2 := by omega
    rcases this with rfl | rfl | rfl
    · left; rfl
    · right; left; rfl
    · right; right; rfl

  have sp0 : spatialIdx 0 = 1 := rfl
  have sp1 : spatialIdx 1 = 2 := rfl
  have sp2 : spatialIdx 2 = 3 := rfl

  change ∑ i : Fin 3, Matrix.trace (((4 : ℂ) • ∑ a : Fin 3, ∑ b : Fin 3, (epsilon3 i a b) • F (spatialIdx a) (spatialIdx b)) * F (spatialIdx i) (spatialIdx j)) = 0
  
  rcases j_cases with rfl | rfl | rfl
  · simp only [sum_fin_3_expand, Matrix.add_apply, Matrix.smul_apply, trace_mul_2x2, smul_eq_mul,
               epsilon3, epsilon3_int, Int.cast_zero, Int.cast_one, Int.cast_neg, sp0, sp1, sp2,
               f11_00, f11_01, f11_10, f11_11,
               f22_00, f22_01, f22_10, f22_11,
               f33_00, f33_01, f33_10, f33_11,
               f21_00, f21_01, f21_10, f21_11,
               f31_00, f31_01, f31_10, f31_11,
               f32_00, f32_01, f32_10, f32_11]
    ring
  · simp only [sum_fin_3_expand, Matrix.add_apply, Matrix.smul_apply, trace_mul_2x2, smul_eq_mul,
               epsilon3, epsilon3_int, Int.cast_zero, Int.cast_one, Int.cast_neg, sp0, sp1, sp2,
               f11_00, f11_01, f11_10, f11_11,
               f22_00, f22_01, f22_10, f22_11,
               f33_00, f33_01, f33_10, f33_11,
               f21_00, f21_01, f21_10, f21_11,
               f31_00, f31_01, f31_10, f31_11,
               f32_00, f32_01, f32_10, f32_11]
    ring
  · simp only [sum_fin_3_expand, Matrix.add_apply, Matrix.smul_apply, trace_mul_2x2, smul_eq_mul,
               epsilon3, epsilon3_int, Int.cast_zero, Int.cast_one, Int.cast_neg, sp0, sp1, sp2,
               f11_00, f11_01, f11_10, f11_11,
               f22_00, f22_01, f22_10, f22_11,
               f33_00, f33_01, f33_10, f33_11,
               f21_00, f21_01, f21_10, f21_11,
               f31_00, f31_01, f31_10, f31_11,
               f32_00, f32_01, f32_10, f32_11]
    ring

end CGD.Foundations

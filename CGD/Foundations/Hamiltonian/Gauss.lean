-- FILENAME: CGD/Foundations/Hamiltonian/Gauss.lean

import Litlib.Core
import CGD.Foundations.Hamiltonian.Basic
import CGD.Foundations.TensorCalculus.BianchiIdentity

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Axioms Matrix Complex
open CGD.Gravity

namespace CGD.Foundations

Litlib.theorem
  description "Topological Gauss Constraint"
/--
The Gauss constraint algebraically vanishes as an exact identity. 
The spatial divergence of the conjugate momentum reduces to the spatial Bianchi identity.
-/
theorem gaussConstraintVanishes (A : Sl2cGaugeField) (x : SpacetimePoint) :
  gaussConstraintDensity A x = 0 := by
  unfold gaussConstraintDensity
  have sp0 : spatialIdx 0 = 1 := rfl
  have sp1 : spatialIdx 1 = 2 := rfl
  have sp2 : spatialIdx 2 = 3 := rfl
  simp only [sum_fin_3_expand,
             Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
             epsilon3, epsilon3_int, sp0, sp1, sp2,
             Int.cast_zero, Int.cast_one, Int.cast_neg,
             zero_smul, one_smul, neg_smul, add_zero, zero_add]
             
  have b1 := bianchiIdentity A 1 2 3 x
  have b2 := bianchiIdentity A 1 3 2 x
  
  have b1_eq : (covariantDeriv A.val 1 2 3 x).val + (covariantDeriv A.val 2 3 1 x).val + (covariantDeriv A.val 3 1 2 x).val = 0 := by
    calc (covariantDeriv A.val 1 2 3 x).val + (covariantDeriv A.val 2 3 1 x).val + (covariantDeriv A.val 3 1 2 x).val
      _ = (covariantDeriv A.val 1 2 3 x + covariantDeriv A.val 2 3 1 x + covariantDeriv A.val 3 1 2 x).val := rfl
      _ = (0 : SL2C).val := congrArg Subtype.val b1
      _ = 0 := rfl
      
  have b2_eq : (covariantDeriv A.val 1 3 2 x).val + (covariantDeriv A.val 3 2 1 x).val + (covariantDeriv A.val 2 1 3 x).val = 0 := by
    calc (covariantDeriv A.val 1 3 2 x).val + (covariantDeriv A.val 3 2 1 x).val + (covariantDeriv A.val 2 1 3 x).val
      _ = (covariantDeriv A.val 1 3 2 x + covariantDeriv A.val 3 2 1 x + covariantDeriv A.val 2 1 3 x).val := rfl
      _ = (0 : SL2C).val := congrArg Subtype.val b2
      _ = 0 := rfl

  ext i j
  simp only [Matrix.smul_apply, Matrix.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  have h1 := congrFun (congrFun b1_eq i) j
  have h2 := congrFun (congrFun b2_eq i) j
  simp only [Matrix.add_apply, Matrix.zero_apply, Pi.add_apply, Pi.zero_apply] at h1 h2
  
  calc _ = (4 : ℂ) * (
        ((covariantDeriv A.val 1 2 3 x).val i j + (covariantDeriv A.val 2 3 1 x).val i j + (covariantDeriv A.val 3 1 2 x).val i j) -
        ((covariantDeriv A.val 1 3 2 x).val i j + (covariantDeriv A.val 3 2 1 x).val i j + (covariantDeriv A.val 2 1 3 x).val i j) ) := by ring
    _ = (4 : ℂ) * (0 - 0) := by rw [h1, h2]
    _ = 0 := by ring

end CGD.Foundations

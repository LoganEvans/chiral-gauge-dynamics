-- FILENAME: CGD/Foundations/Hamiltonian/Canonical.lean

import Litlib.Core
import CGD.Foundations.Hamiltonian.Basic

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Axioms Matrix Complex
open CGD.Gravity

namespace CGD.Foundations

/-- Expands the trace constraint to evaluate over individual components. -/
lemma topological_action_identity_matrix (F : Fin 4 → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
  (hF_anti : ∀ μ ν, F μ ν = - F ν μ) :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
    epsilon4 μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ)) =
  ∑ i : Fin 3, Matrix.trace (((4 : ℂ) • ∑ j : Fin 3, ∑ k : Fin 3, (epsilon3 i j k) • F (spatialIdx j) (spatialIdx k)) * F 0 (spatialIdx i)) := by
  have f00_00 : F 0 0 0 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 0 0) 0) 0)
  have f00_01 : F 0 0 0 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 0 0) 0) 1)
  have f00_10 : F 0 0 1 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 0 0) 1) 0)
  have f00_11 : F 0 0 1 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 0 0) 1) 1)

  have f11_00 : F 1 1 0 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 1 1) 0) 0)
  have f11_01 : F 1 1 0 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 1 1) 0) 1)
  have f11_10 : F 1 1 1 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 1 1) 1) 0)
  have f11_11 : F 1 1 1 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 1 1) 1) 1)

  have f22_00 : F 2 2 0 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 2 2) 0) 0)
  have f22_01 : F 2 2 0 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 2 2) 0) 1)
  have f22_10 : F 2 2 1 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 2 2) 1) 0)
  have f22_11 : F 2 2 1 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 2 2) 1) 1)

  have f33_00 : F 3 3 0 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 3 3) 0) 0)
  have f33_01 : F 3 3 0 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 3 3) 0) 1)
  have f33_10 : F 3 3 1 0 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 3 3) 1) 0)
  have f33_11 : F 3 3 1 1 = 0 := skew_zero _ (congrFun (congrFun (hF_anti 3 3) 1) 1)

  have f10_00 : F 1 0 0 0 = - F 0 1 0 0 := congrFun (congrFun (hF_anti 1 0) 0) 0
  have f10_01 : F 1 0 0 1 = - F 0 1 0 1 := congrFun (congrFun (hF_anti 1 0) 0) 1
  have f10_10 : F 1 0 1 0 = - F 0 1 1 0 := congrFun (congrFun (hF_anti 1 0) 1) 0
  have f10_11 : F 1 0 1 1 = - F 0 1 1 1 := congrFun (congrFun (hF_anti 1 0) 1) 1

  have f20_00 : F 2 0 0 0 = - F 0 2 0 0 := congrFun (congrFun (hF_anti 2 0) 0) 0
  have f20_01 : F 2 0 0 1 = - F 0 2 0 1 := congrFun (congrFun (hF_anti 2 0) 0) 1
  have f20_10 : F 2 0 1 0 = - F 0 2 1 0 := congrFun (congrFun (hF_anti 2 0) 1) 0
  have f20_11 : F 2 0 1 1 = - F 0 2 1 1 := congrFun (congrFun (hF_anti 2 0) 1) 1

  have f30_00 : F 3 0 0 0 = - F 0 3 0 0 := congrFun (congrFun (hF_anti 3 0) 0) 0
  have f30_01 : F 3 0 0 1 = - F 0 3 0 1 := congrFun (congrFun (hF_anti 3 0) 0) 1
  have f30_10 : F 3 0 1 0 = - F 0 3 1 0 := congrFun (congrFun (hF_anti 3 0) 1) 0
  have f30_11 : F 3 0 1 1 = - F 0 3 1 1 := congrFun (congrFun (hF_anti 3 0) 1) 1

  have f21_00 : F 2 1 0 0 = - F 1 2 0 0 := congrFun (congrFun (hF_anti 2 1) 0) 0
  have f21_01 : F 2 1 0 1 = - F 1 2 0 1 := congrFun (congrFun (hF_anti 2 1) 0) 1
  have f21_10 : F 2 1 1 0 = - F 1 2 1 0 := congrFun (congrFun (hF_anti 2 1) 1) 0
  have f21_11 : F 2 1 1 1 = - F 1 2 1 1 := congrFun (congrFun (hF_anti 2 1) 1) 1

  have f31_00 : F 3 1 0 0 = - F 1 3 0 0 := congrFun (congrFun (hF_anti 3 1) 0) 0
  have f31_01 : F 3 1 0 1 = - F 1 3 0 1 := congrFun (congrFun (hF_anti 3 1) 0) 1
  have f31_10 : F 3 1 1 0 = - F 1 3 1 0 := congrFun (congrFun (hF_anti 3 1) 1) 0
  have f31_11 : F 3 1 1 1 = - F 1 3 1 1 := congrFun (congrFun (hF_anti 3 1) 1) 1

  have f32_00 : F 3 2 0 0 = - F 2 3 0 0 := congrFun (congrFun (hF_anti 3 2) 0) 0
  have f32_01 : F 3 2 0 1 = - F 2 3 0 1 := congrFun (congrFun (hF_anti 3 2) 0) 1
  have f32_10 : F 3 2 1 0 = - F 2 3 1 0 := congrFun (congrFun (hF_anti 3 2) 1) 0
  have f32_11 : F 3 2 1 1 = - F 2 3 1 1 := congrFun (congrFun (hF_anti 3 2) 1) 1

  have sp0 : spatialIdx 0 = 1 := rfl
  have sp1 : spatialIdx 1 = 2 := rfl
  have sp2 : spatialIdx 2 = 3 := rfl

  simp only [sum_fin_4_expand, sum_fin_3_expand,
             trace_mul_2x2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
             epsilon4, epsilon4_int, sp0, sp1, sp2, epsilon3, epsilon3_int,
             Int.cast_zero, Int.cast_one, Int.cast_neg,
             f00_00, f00_01, f00_10, f00_11,
             f11_00, f11_01, f11_10, f11_11,
             f22_00, f22_01, f22_10, f22_11,
             f33_00, f33_01, f33_10, f33_11,
             f10_00, f10_01, f10_10, f10_11,
             f20_00, f20_01, f20_10, f20_11,
             f30_00, f30_01, f30_10, f30_11,
             f21_00, f21_01, f21_10, f21_11,
             f31_00, f31_01, f31_10, f31_11,
             f32_00, f32_01, f32_10, f32_11]
  ring

Litlib.theorem
  description "Spatial Expansion of Topological Action"
/-- 
The 4D topological action reduces to Tr(Π^i F_{0i}) on the spatial slice.
This isolates the permutations that contain a temporal electric field component.
-/
theorem topologicalActionSpatialExpansion (A : Sl2cGaugeField) (x : SpacetimePoint) :
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
    epsilon4 μ ν ρ σ * Matrix.trace ((curvatureSl2c A.val μ ν x).val * (curvatureSl2c A.val ρ σ x).val)) =
  ∑ i : Fin 3, Matrix.trace (conjugateMomentum A i x * (curvatureSl2c A.val 0 (spatialIdx i) x).val) := by
  have hF_anti : ∀ μ ν, (curvatureSl2c A.val μ ν x).val = - (curvatureSl2c A.val ν μ x).val := by
    intro μ ν
    have h := curvatureSl2c_antisymm A.val μ ν x
    exact congrArg Subtype.val h
    
  have h_rhs : (∑ i : Fin 3, Matrix.trace (conjugateMomentum A i x * (curvatureSl2c A.val 0 (spatialIdx i) x).val)) = 
               (∑ i : Fin 3, Matrix.trace (((4 : ℂ) • ∑ j : Fin 3, ∑ k : Fin 3, (epsilon3 i j k) • (curvatureSl2c A.val (spatialIdx j) (spatialIdx k) x).val) * (curvatureSl2c A.val 0 (spatialIdx i) x).val)) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold conjugateMomentum
    rfl
    
  rw [h_rhs]
  exact topological_action_identity_matrix (fun μ ν => (curvatureSl2c A.val μ ν x).val) hF_anti

Litlib.theorem
  description "Electric Field Decomposition"
/-- 
Decomposition of the temporal electric field F_{0i} into the time derivative 
of A_i minus the spatial covariant derivative of A_0.
-/
theorem electricFieldDecomposition (A : Sl2cGaugeField) (x : SpacetimePoint) (i : Fin 3) :
  (curvatureSl2c A.val 0 (spatialIdx i) x).val =
  (partialDerivSl2c 0 (A.val (spatialIdx i)) x).val -
  ((partialDerivSl2c (spatialIdx i) (A.val 0) x).val - 
   ((A.val 0 x).val * (A.val (spatialIdx i) x).val - (A.val (spatialIdx i) x).val * (A.val 0 x).val)) := by
  have h := curvatureSl2c_def A.val 0 (spatialIdx i) x
  have h_val := congrArg Subtype.val h
  rw [h_val]
  change (partialDerivSl2c 0 (A.val (spatialIdx i)) x).val - (partialDerivSl2c (spatialIdx i) (A.val 0) x).val + ((A.val 0 x).val * (A.val (spatialIdx i) x).val - (A.val (spatialIdx i) x).val * (A.val 0 x).val) = _
  ext m n
  simp only [Matrix.sub_apply, Matrix.add_apply]
  ring

Litlib.theorem
  description "Topological Hamiltonian Constraint"
/--
The canonical Hamiltonian density of the pure connection sector
algebraically reduces to the temporal gauge field A_0 acting as a Lagrange 
multiplier for the spatial covariant derivative of the conjugate momentum.
Since there are no local dynamical energy terms, this establishes that 
the bulk geometry is purely topological (H ≈ 0 on the constraint surface).
-/
theorem canonicalHamiltonianVanishes (A : Sl2cGaugeField) (x : SpacetimePoint) :
  canonicalHamiltonianDensity A x =
  ∑ i : Fin 3, Matrix.trace (conjugateMomentum A i x *
    ((partialDerivSl2c (spatialIdx i) (A.val 0) x).val - 
     ((A.val 0 x).val * (A.val (spatialIdx i) x).val - (A.val (spatialIdx i) x).val * (A.val 0 x).val))) := by
  rw [canonicalHamiltonianDensity, topologicalActionSpatialExpansion A x]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := electricFieldDecomposition A x i
  rw [h]
  apply ext_trace_mul_sub_fin_2

end CGD.Foundations

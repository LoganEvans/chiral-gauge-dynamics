-- FILENAME: CGD/Foundations/Hamiltonian.lean

import Litlib.Core
import CGD.Foundations.Math
import CGD.Foundations.Calculus
import CGD.Foundations.Action
import CGD.Gravity.Geometry
import CGD.Foundations.TensorCalculus.DifferentialRules
import CGD.Foundations.TensorCalculus.BianchiIdentity
import CGD.Axioms.Ontology

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Axioms Matrix Complex
open CGD.Gravity

namespace CGD.Foundations

/-- Maps a 3D spatial index (Fin 3) to the corresponding spacetime index (Fin 4), shifting by 1. 
    Using Nat.succ_lt_succ guarantees the bounds are mathematically rigorous without heavy tactics. -/
def spatialIdx (i : Fin 3) : Fin 4 := 
  ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

/-- 
The momentum conjugate to the spatial gauge field A_i. 
Extracted from the Pontryagin topological density: Π^i = 4 * ε^{ijk} F_{jk}
Defined as a pure Matrix to bypass subtype coercion limits.
Explicitly scaled by (4 : ℂ) to align with complex polynomial rings.
-/
noncomputable def conjugateMomentum (A : Sl2cGaugeField) (i : Fin 3) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  (4 : ℂ) • ∑ j : Fin 3, ∑ k : Fin 3, (epsilon3 i j k) • (curvatureSl2c A.val (spatialIdx j) (spatialIdx k) x).val

/-- 
The canonical Hamiltonian density: 
H = Π^i ˙A_i - L_{topological} 
-/
noncomputable def canonicalHamiltonianDensity (A : Sl2cGaugeField) (x : SpacetimePoint) : ℂ :=
  (∑ i : Fin 3, Matrix.trace (conjugateMomentum A i x * (partialDerivSl2c 0 (A.val (spatialIdx i)) x).val)) -
  (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, 
    epsilon4 μ ν ρ σ * Matrix.trace ((curvatureSl2c A.val μ ν x).val * (curvatureSl2c A.val ρ σ x).val))

/-- 
The Gauss Constraint: Generates spatial SU(2) gauge transformations.
Formally: G = D_i Π^i.
By leveraging the linearity of the covariant derivative over the Lie algebra, 
this is strictly equivalent to the fully contracted spatial covariant 
divergence of the magnetic field tensor.
-/
noncomputable def gaussConstraintDensity (A : Sl2cGaugeField) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  (4 : ℂ) • ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (epsilon3 i j k) • (covariantDeriv A.val (spatialIdx i) (spatialIdx j) (spatialIdx k) x).val

/--
The Momentum (Diffeomorphism) Constraint: Generates spatial diffeomorphisms.
Formally: V_j = Tr(Π^i F_{ij}).
-/
noncomputable def momentumConstraintDensity (A : Sl2cGaugeField) (j : Fin 3) (x : SpacetimePoint) : ℂ :=
  ∑ i : Fin 3, Matrix.trace (conjugateMomentum A i x * (curvatureSl2c A.val (spatialIdx i) (spatialIdx j) x).val)

-- ==============================================================================
-- Algebraic & Combinatorial Helpers for 4D -> 3D Reduction
-- ==============================================================================

lemma skew_zero (x : ℂ) (h : x = -x) : x = 0 := by
  have h_sub : x - (-x) = 0 := sub_eq_zero.mpr h
  have h2 : x + x = 0 := by
    calc x + x = x - (-x) := by ring
         _ = 0 := h_sub
  have h3 : (2 : ℂ) * x = 0 := by
    calc (2 : ℂ) * x = x + x := by ring
         _ = 0 := h2
  have h4 : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h3).resolve_left h4

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

-- ==============================================================================
-- Physical Equivalences
-- ==============================================================================

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

lemma ext_trace_mul_sub_fin_2 (M X Y : Matrix (Fin 2) (Fin 2) ℂ) :
  Matrix.trace (M * X) - Matrix.trace (M * (X - Y)) = Matrix.trace (M * Y) := by
  have sub_00 : (X - Y) 0 0 = X 0 0 - Y 0 0 := rfl
  have sub_01 : (X - Y) 0 1 = X 0 1 - Y 0 1 := rfl
  have sub_10 : (X - Y) 1 0 = X 1 0 - Y 1 0 := rfl
  have sub_11 : (X - Y) 1 1 = X 1 1 - Y 1 1 := rfl
  simp only [trace_mul_2x2, sub_00, sub_01, sub_10, sub_11]
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

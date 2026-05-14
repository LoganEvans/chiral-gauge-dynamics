-- FILENAME: CGD/Foundations/Hamiltonian/Basic.lean

import Litlib.Core
import CGD.Foundations.Math
import CGD.Foundations.Calculus
import CGD.Foundations.Action
import CGD.Gravity.Geometry
import CGD.Foundations.TensorCalculus.DifferentialRules
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
-- Algebraic Helpers
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

lemma ext_trace_mul_sub_fin_2 (M X Y : Matrix (Fin 2) (Fin 2) ℂ) :
  Matrix.trace (M * X) - Matrix.trace (M * (X - Y)) = Matrix.trace (M * Y) := by
  have sub_00 : (X - Y) 0 0 = X 0 0 - Y 0 0 := rfl
  have sub_01 : (X - Y) 0 1 = X 0 1 - Y 0 1 := rfl
  have sub_10 : (X - Y) 1 0 = X 1 0 - Y 1 0 := rfl
  have sub_11 : (X - Y) 1 1 = X 1 1 - Y 1 1 := rfl
  simp only [trace_mul_2x2, sub_00, sub_01, sub_10, sub_11]
  ring

end CGD.Foundations

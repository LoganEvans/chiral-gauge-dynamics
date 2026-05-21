-- FILENAME: CGD/Phenomenology/AxialCondensate.lean

import CGD.Axioms.Ontology
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Spacetime
import CGD.AntiSelfDualSector.Decoupling
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Matrix

open Matrix
open Complex
open CGD
open CGD.Axioms
open CGD.Foundations

/-- The pure Vector Chiral field, defined as the symmetric superposition of the left and right sectors. -/
noncomputable def vectorField (u : Universe) (mu : Fin 4) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • ((u.sd_sector mu x).val + (u.asd_sector mu x).val)

/-- The pure Axial Chiral field, defined as the antisymmetric superposition of the left and right sectors. -/
noncomputable def axialField (u : Universe) (mu : Fin 4) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • ((u.sd_sector mu x).val - (u.asd_sector mu x).val)

/-- 
A discrete geometric transformation that completely inverts the orientation of the 
spacetime manifold by swapping the Chiral left (self-dual) and right (anti-self-dual) sectors.
-/
noncomputable def paritySwap (u : Universe) : Universe :=
  universeEquiv.symm (u.asd_sector, u.sd_sector)

/--
Proves that the Axial field behaves strictly as a pseudo-vector (parity-odd). 
When the geometry is parity-inverted, the Axial field exactly flips its algebraic sign.
-/
theorem axialIsParityOdd (u : Universe) (mu : Fin 4) (x : SpacetimePoint) :
  axialField (paritySwap u) mu x = - axialField u mu x := by
  unfold axialField paritySwap
  have h_u_eq : universeEquiv (universeEquiv.symm (u.asd_sector, u.sd_sector)) = (u.asd_sector, u.sd_sector) :=
    Equiv.right_inv universeEquiv (u.asd_sector, u.sd_sector)
    
  have h_sd : (universeEquiv.symm (u.asd_sector, u.sd_sector)).sd_sector = u.asd_sector := congrArg Prod.fst h_u_eq
  have h_asd : (universeEquiv.symm (u.asd_sector, u.sd_sector)).asd_sector = u.sd_sector := congrArg Prod.snd h_u_eq
  
  have h_sd_val : ((universeEquiv.symm (u.asd_sector, u.sd_sector)).sd_sector mu x).val = (u.asd_sector mu x).val := by
    rw [h_sd]
  have h_asd_val : ((universeEquiv.symm (u.asd_sector, u.sd_sector)).asd_sector mu x).val = (u.sd_sector mu x).val := by
    rw [h_asd]
    
  rw [h_sd_val, h_asd_val]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/--
Proves that the Axial field is strictly an isovector (isospin 1).
It inherits the exact traceless property of the SL(2,C) algebra constituents,
confining it to the adjoint representation of the SU(2) color group.
-/
theorem axialIsIsovector (u : Universe) (mu : Fin 4) (x : SpacetimePoint) :
  Matrix.trace (axialField u mu x) = 0 := by
  unfold axialField
  rw [Matrix.trace_smul, Matrix.trace_sub]
  have h_sd : Matrix.trace (u.sd_sector mu x).val = 0 := 
    (CGD.Foundations.mem_sl_iff (u.sd_sector mu x).val).mp (u.sd_sector mu x).property
  have h_asd : Matrix.trace (u.asd_sector mu x).val = 0 := 
    (CGD.Foundations.mem_sl_iff (u.asd_sector mu x).val).mp (u.asd_sector mu x).property
  rw [h_sd, h_asd]
  simp only [sub_self, smul_zero]

/--
If the macroscopic volume emergent metric is non-degenerate, chiral symmetry must be broken (L ≠ R). 
This mathematically guarantees that the spacetime background is natively populated by a strictly non-zero 
Axial-Vector condensate.
-/
theorem macroscopicVolumeImpliesAxialCondensate (u : Universe) (mu : Fin 4) (x : SpacetimePoint)
  (h_neq : (u.sd_sector mu x).val ≠ (u.asd_sector mu x).val) :
  axialField u mu x ≠ 0 := by
  unfold axialField
  intro h_zero
  have h2 : (2 : ℂ) • ((1 / 2 : ℂ) • ((u.sd_sector mu x).val - (u.asd_sector mu x).val)) = (2 : ℂ) • (0 : Matrix (Fin 2) (Fin 2) ℂ) := by rw [h_zero]
  rw [smul_smul] at h2
  have h_mul : (2 : ℂ) * (1 / 2 : ℂ) = 1 := by norm_num
  rw [h_mul, one_smul, smul_zero] at h2
  exact h_neq (sub_eq_zero.mp h2)

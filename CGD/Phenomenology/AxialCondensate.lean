-- FILENAME: CGD/Phenomenology/AxialCondensate.lean

import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Spacetime
import CGD.AntiSelfDualSector.Decoupling
import CGD.Phenomenology.Chirality
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Tactic

open Matrix
open Complex
open CGD
open CGD.Axioms
open CGD.Foundations

namespace CGD.Phenomenology

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

Litlib.theorem
  description "Axial Is Parity Odd"
/--
Proves that the Axial field behaves strictly as a pseudo-vector (parity-odd). 
When the geometry is parity-inverted, the Axial field exactly flips its algebraic sign.
-/
theorem axialIsParityOdd (pu : PhysicalUniverse) (mu : Fin 4) (x : SpacetimePoint) :
  axialField (paritySwap pu.toUniverse) mu x = - axialField pu.toUniverse mu x := by
  unfold axialField paritySwap
  have h_u_eq : universeEquiv (universeEquiv.symm (pu.toUniverse.asd_sector, pu.toUniverse.sd_sector)) = (pu.toUniverse.asd_sector, pu.toUniverse.sd_sector) :=
    Equiv.right_inv universeEquiv (pu.toUniverse.asd_sector, pu.toUniverse.sd_sector)
    
  have h_sd : (universeEquiv.symm (pu.toUniverse.asd_sector, pu.toUniverse.sd_sector)).sd_sector = pu.toUniverse.asd_sector := congrArg Prod.fst h_u_eq
  have h_asd : (universeEquiv.symm (pu.toUniverse.asd_sector, pu.toUniverse.sd_sector)).asd_sector = pu.toUniverse.sd_sector := congrArg Prod.snd h_u_eq
  
  have h_sd_val : ((universeEquiv.symm (pu.toUniverse.asd_sector, pu.toUniverse.sd_sector)).sd_sector mu x).val = (pu.toUniverse.asd_sector mu x).val := by
    rw [h_sd]
  have h_asd_val : ((universeEquiv.symm (pu.toUniverse.asd_sector, pu.toUniverse.sd_sector)).asd_sector mu x).val = (pu.toUniverse.sd_sector mu x).val := by
    rw [h_asd]
    
  rw [h_sd_val, h_asd_val]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  ring

Litlib.theorem
  description "Axial Is Isovector"
/--
Proves that the Axial field is strictly an isovector (isospin 1).
It inherits the exact traceless property of the SL(2,C) algebra constituents,
confining it to the adjoint representation of the SU(2) color group.
-/
theorem axialIsIsovector (pu : PhysicalUniverse) (mu : Fin 4) (x : SpacetimePoint) :
  Matrix.trace (axialField pu.toUniverse mu x) = 0 := by
  unfold axialField
  rw [Matrix.trace_smul, Matrix.trace_sub]
  have h_sd : Matrix.trace (pu.toUniverse.sd_sector mu x).val = 0 := 
    (CGD.Foundations.mem_sl_iff (pu.toUniverse.sd_sector mu x).val).mp (pu.toUniverse.sd_sector mu x).property
  have h_asd : Matrix.trace (pu.toUniverse.asd_sector mu x).val = 0 := 
    (CGD.Foundations.mem_sl_iff (pu.toUniverse.asd_sector mu x).val).mp (pu.toUniverse.asd_sector mu x).property
  rw [h_sd, h_asd]
  simp only [sub_self, smul_zero]

Litlib.theorem
  description "Macroscopic Volume Implies Axial Condensate"
/--
Because the macroscopic volume emergent metric strictly forbids global chiral symmetry 
(via `macroscopicVolumeImpliesChirality`), this mathematically guarantees that the spacetime 
background is natively populated by a strictly non-zero Axial-Vector condensate. Empty 
space spontaneously generates the axial field to preserve its volume.
-/
theorem macroscopicVolumeImpliesAxialCondensate 
  (pu : PhysicalUniverse) (x : SpacetimePoint) (hx : x ∈ pu.bulk)
  (h_vacuum : ∀ μ ν, curvatureSl2c pu.toUniverse.asd_sector.val μ ν x = 0) :
  ∃ y mu, axialField pu.toUniverse mu y ≠ 0 := by
  
  -- 1. Obtain the global chiral collapse theorem
  have h_chiral := CGD.Phenomenology.macroscopicVolumeImpliesChirality pu x hx h_vacuum
  
  -- 2. Assume by contradiction that the axial field is strictly zero everywhere
  by_contra h_not_exists
  push_neg at h_not_exists
  
  -- 3. If the axial field is zero everywhere, the Universe is globally symmetric
  have h_eq : pu.toUniverse.sd_sector.val = pu.toUniverse.asd_sector.val := by
    funext mu y
    apply Subtype.ext
    have h_ax := h_not_exists y mu
    unfold axialField at h_ax
    have h2 : (2 : ℂ) • ((1 / 2 : ℂ) • ((pu.toUniverse.sd_sector mu y).val - (pu.toUniverse.asd_sector mu y).val)) = (2 : ℂ) • (0 : Matrix (Fin 2) (Fin 2) ℂ) := by rw [h_ax]
    rw [smul_smul] at h2
    have h_mul : (2 : ℂ) * (1 / 2 : ℂ) = 1 := by norm_num
    rw [h_mul, one_smul, smul_zero] at h2
    exact sub_eq_zero.mp h2
    
  -- 4. A globally symmetric universe contradicts the macroscopic volume constraint
  exact h_chiral h_eq

end CGD.Phenomenology

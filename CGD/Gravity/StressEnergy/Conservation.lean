-- FILENAME: CGD/Gravity/StressEnergy/Conservation.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Foundations.Calculus
import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Litlib.Y2003.nakahara2003geometry.Signature
import Litlib.Y1984.urbantke1984integrability.Signature

open Complex Matrix CGD.Foundations BigOperators Classical
open CGD.Axioms

namespace CGD.Gravity

instance : Nonempty SpacetimePoint := ⟨fun _ => 0⟩

/-- The physical axiom of macroscopic volume strictly implies the bulk subspace is nonempty -/
instance instPhysicalUniverseBulkNonempty (pu : PhysicalUniverse) : Nonempty pu.bulk :=
  let ⟨x, hx⟩ := pu.has_volume.h_bulk_nonempty
  ⟨⟨x, hx⟩⟩

noncomputable def emergentStressEnergy (F : Fin 4 → Fin 4 → SpacetimePoint → SL2C) (mu nu : Fin 4) (x : SpacetimePoint) : ℂ :=
  let g := fun m n p => CGD.Gravity.urbantkeMetric (fun a b => F a b p) m n
  let g_inv := CGD.Gravity.matrixInv4x4 (fun m n => g m n x)
  let R_mu_nu := CGD.Gravity.ricciTensor g mu nu x
  let R_scalar := ∑ alpha : Fin 4, ∑ beta : Fin 4, g_inv alpha beta * CGD.Gravity.ricciTensor g alpha beta x
  R_mu_nu - (1/2 : ℂ) * g mu nu x * R_scalar

lemma metric_inv_prop (g : Matrix (Fin 4) (Fin 4) ℂ) (hDet : g.det ≠ 0) :
  ∀ i j, ∑ k : Fin 4, g i k * matrixInv4x4 g k j = if i = j then 1 else 0 := by
  intro i j
  have h_adj : g * g.adjugate = g.det • (1 : Matrix (Fin 4) (Fin 4) ℂ) := Matrix.mul_adjugate g
  have h_eval : (g * g.adjugate) i j = (g.det • (1 : Matrix (Fin 4) (Fin 4) ℂ)) i j := by rw [h_adj]
  change ∑ k : Fin 4, g i k * ((1 / g.det) * g.adjugate k j) = if i = j then 1 else 0
  have h_pull : ∑ k : Fin 4, g i k * ((1 / g.det) * g.adjugate k j) = (1 / g.det) * ∑ k : Fin 4, g i k * g.adjugate k j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h_pull]
  have h_sum_adj : ∑ k : Fin 4, g i k * g.adjugate k j = (g * g.adjugate) i j := rfl
  rw [h_sum_adj, h_eval]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs with h_eq
  · rw [mul_one]; exact div_mul_cancel₀ 1 hDet
  · rw [mul_zero]; ring

lemma metric_inv_symm (g : Matrix (Fin 4) (Fin 4) ℂ) (hSymm : ∀ i j, g i j = g j i) :
  ∀ i j, matrixInv4x4 g i j = matrixInv4x4 g j i := by
  intro i j
  unfold matrixInv4x4
  have h_g_trans : gᵀ = g := by ext a b; exact hSymm b a
  have h_adj_trans : g.adjugateᵀ = g.adjugate := by
    rw [Matrix.adjugate_transpose]
    rw [h_g_trans]
  have h_eval : g.adjugate i j = g.adjugate j i := by
    change g.adjugateᵀ j i = g.adjugate j i
    rw [h_adj_trans]
  change (1 / g.det) * g.adjugate i j = (1 / g.det) * g.adjugate j i
  rw [h_eval]

/-- Project bulk derivatives into the spacetime coordinate system -/
noncomputable def bulkDeriv (pu : PhysicalUniverse) (mu : Fin 4) (f : pu.bulk → ℂ) (x : pu.bulk) : ℂ :=
  partialDeriv mu (fun p => if h : p ∈ pu.bulk then f ⟨p, h⟩ else 0) x.val

/--
The emergent Stress-Energy tensor (defined as the Einstein tensor of the dynamically emergent Urbantke metric) is covariantly conserved with respect to its own Levi-Civita connection.
This fundamentally restricts the conservation to the macroscopic bulk where det g ≠ 0.
-/
@[litlib_track "Emergent Stress-Energy Conservation"]
theorem emergentStressEnergyConservation
  (pu : PhysicalUniverse)
  (isSmooth : (pu.bulk → ℂ) → Prop)
  [general_bianchi : Litlib.Y2003.nakahara2003geometry.Theorem_ContractedBianchi pu.bulk (Fin 4) isSmooth (bulkDeriv pu)]
  [symm_metric : Litlib.Y1984.urbantke1984integrability.Eq10_Symmetry]
  (h_metric_eq10 : ∀ x : pu.bulk, ∃ (F F_dual : Fin 3 → Fin 4 → Fin 4 → ℂ) (epsilon3 : Fin 3 → Fin 3 → Fin 3 → ℂ),
    (∀ a mu nu, F a mu nu = - F a nu mu) ∧
    (∀ a mu nu, F_dual a mu nu = - F_dual a nu mu) ∧
    (∀ a b c, epsilon3 a b c = - epsilon3 b a c ∧ epsilon3 a b c = - epsilon3 a c b) ∧
    (∀ mu nu, CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b x.val) mu nu =
      (-1 / 6 : ℂ) * Finset.sum Finset.univ (fun a => Finset.sum Finset.univ (fun b => Finset.sum Finset.univ (fun c => Finset.sum Finset.univ (fun alpha => Finset.sum Finset.univ (fun beta => epsilon3 a c b * F a mu alpha * F_dual c alpha beta * F b beta nu)))))))
  (h_smooth_g : ∀ i j, isSmooth (fun p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p.val) i j))
  (h_smooth_g_inv : ∀ i j, isSmooth (fun p => CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p.val) m n) i j))
  (h_smooth_chris : ∀ rho mu nu, isSmooth (fun p => CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) rho mu nu p.val))
  (h_chris_eq : ∀ p : pu.bulk, ∀ rho mu nu, CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) rho mu nu p.val =
    (1/2 : ℂ) * ∑ sigma : Fin 4, CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p.val) m n) rho sigma * (
      bulkDeriv pu mu (fun p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p'.val) sigma nu) p +
      bulkDeriv pu nu (fun p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p'.val) mu sigma) p -
      bulkDeriv pu sigma (fun p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p'.val) mu nu) p))
  (h_ricci_eq : ∀ p : pu.bulk, ∀ mu nu, CGD.Gravity.ricciTensor (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) mu nu p.val =
    ∑ rho : Fin 4, (bulkDeriv pu rho (fun p' => CGD.Gravity.christoffel (fun m n p'' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p'') m n) rho mu nu p'.val) p -
          bulkDeriv pu nu (fun p' => CGD.Gravity.christoffel (fun m n p'' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p'') m n) rho mu rho p'.val) p +
          ∑ lambda : Fin 4, (CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) rho lambda rho p.val * CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) lambda mu nu p.val -
                CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) rho lambda nu p.val * CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) lambda mu rho p.val))) :
  ∀ nu (x : pu.bulk),
    let g_urb := fun m n (p : pu.bulk) => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p.val) m n
    let g_inv := fun m n (p : pu.bulk) => CGD.Gravity.matrixInv4x4 (fun a b => g_urb a b p) m n
    let chris := fun rho mu nu (p : pu.bulk) => CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) rho mu nu p.val
    let T := fun m n (p : pu.bulk) => emergentStressEnergy (fun a b p' => curvatureSl2c pu.toUniverse.sd_sector a b p') m n p.val
    ∑ mu : Fin 4, ∑ alpha : Fin 4, g_inv mu alpha x * (
      bulkDeriv pu alpha (fun p => T mu nu p) x -
      ∑ lambda : Fin 4, (chris lambda alpha mu x * T lambda nu x +
                         chris lambda alpha nu x * T mu lambda x)
    ) = 0 := by
  intro nu x
  let g := fun i j (p : pu.bulk) => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p.val) i j
  let g_inv := fun i j (p : pu.bulk) => CGD.Gravity.matrixInv4x4 (fun m n => g m n p) i j
  let chris := fun rho mu nu (p : pu.bulk) => CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) rho mu nu p.val
  let ricci := fun mu nu (p : pu.bulk) => CGD.Gravity.ricciTensor (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) mu nu p.val
  let scalar := fun (p : pu.bulk) => ∑ alpha : Fin 4, ∑ beta : Fin 4, g_inv alpha beta p * ricci alpha beta p
  let G := fun mu nu (p : pu.bulk) => emergentStressEnergy (fun a b p' => curvatureSl2c pu.toUniverse.sd_sector a b p') mu nu p.val

  have h_symm : ∀ p i j, g i j p = g j i p := by
    intro p i j
    rcases h_metric_eq10 p with ⟨F, F_dual, eps3, hF_anti, hF_dual_anti, heps3_anti, hg_def⟩
    exact symm_metric.symmetricQuasimetric F F_dual eps3 (fun a b => g a b p) hF_anti hF_dual_anti heps3_anti hg_def i j

  have h_inv_symm : ∀ p i j, g_inv i j p = g_inv j i p := by
    intro p i j
    exact metric_inv_symm (Matrix.of (fun a b => g a b p)) (fun a b => h_symm p a b) i j

  have h_inv_prop : ∀ p : pu.bulk, ∀ i j, ∑ k : Fin 4, g i k p * g_inv k j p = if i = j then 1 else 0 := by
    intro p i j
    have hDet : (Matrix.of (fun m n => g m n p)).det ≠ 0 := pu.has_volume.volume_exists p.val p.property
    exact metric_inv_prop (Matrix.of (fun m n => g m n p)) hDet i j

  have h_scalar_eq : ∀ p, scalar p = ∑ alpha : Fin 4, ∑ beta : Fin 4, g_inv alpha beta p * ricci alpha beta p := fun _ => rfl
  have h_G_eq : ∀ p mu nu', G mu nu' p = ricci mu nu' p - (1/2:ℂ) * g mu nu' p * scalar p := fun _ _ _ => rfl

  exact general_bianchi.all_metrics_satisfy_bianchi g g_inv chris ricci scalar G h_symm h_inv_symm h_inv_prop h_chris_eq h_ricci_eq h_scalar_eq h_G_eq h_smooth_g h_smooth_g_inv h_smooth_chris nu x

end CGD.Gravity

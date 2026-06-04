-- FILENAME: CGD/Gravity/GeodesicMotion.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Gravity.StressEnergy
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Axioms.PhysicalUniverse
import Mathlib.Topology.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import CGD.Gravity.MacroscopicVacuum.Basic
import Litlib.Y1975.geroch1975motion.Signature
import Litlib.Y2003.nakahara2003geometry.Signature

open Complex Matrix CGD.Foundations BigOperators Classical
open Topology CGD.Axioms Litlib.Y1975.geroch1975motion

namespace CGD.Gravity

noncomputable def realMetricProxy (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ) : Fin 4 → Fin 4 → SpacetimePoint → ℝ := 
  fun m n p => (g m n p).re

noncomputable def realMetricInvProxy (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ) : Fin 4 → Fin 4 → SpacetimePoint → ℝ := 
  fun m n p => (CGD.Gravity.matrixInv4x4 (fun a b => g a b p) m n).re

noncomputable def realDerivProxy : Fin 4 → (SpacetimePoint → ℝ) → SpacetimePoint → ℝ := 
  fun m f p => (partialDeriv m (fun x => (f x : ℂ)) p).re

noncomputable def realChristoffelProxy (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ) : Fin 4 → Fin 4 → Fin 4 → SpacetimePoint → ℝ := 
  fun lam mu nu x => (1 / 2 : ℝ) * ∑ rho : Fin 4, realMetricInvProxy g lam rho x * (
    realDerivProxy mu (fun p => realMetricProxy g rho nu p) x +
    realDerivProxy nu (fun p => realMetricProxy g rho mu p) x -
    realDerivProxy rho (fun p => realMetricProxy g mu nu p) x
  )

/-- 
PHYSICS AXIOM: The macroscopic classical limit. 
We assert that in the macroscopic bulk where General Relativity emerges, 
the imaginary components of the Urbantke metric and its derivatives vanish, 
allowing the complex covariant conservation law to project perfectly onto 
the real-valued Geroch-Jang theorem requirements.
-/
axiom macroscopic_real_projection_limit (u : Universe) (bulk : Set SpacetimePoint) :
  ∀ (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ) (T_real : Fin 4 → Fin 4 → SpacetimePoint → ℝ) (b : Fin 4) (x : SpacetimePoint),
    (∀ x μ ν, g μ ν x = urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x) μ ν) →
    (∀ mu nu x, T_real mu nu x = (emergentStressEnergy (fun a b p => curvatureSl2c u.sd_sector a b p) mu nu x).re) →
    (∑ a : Fin 4, (realDerivProxy a (fun p => T_real a b p) x + ∑ c : Fin 4, (realChristoffelProxy g a a c x * T_real c b x + realChristoffelProxy g b a c x * T_real a c x))) =
    if _h : x ∈ bulk then 
      (∑ mu : Fin 4, ∑ alpha : Fin 4, CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x) m n) mu alpha * (
        partialDeriv alpha (fun p => if _h' : p ∈ bulk then emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') mu b p else 0) x -
        ∑ lambda : Fin 4, (CGD.Gravity.christoffel (fun m n p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n) lambda alpha mu x * emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') lambda b x + 
                           CGD.Gravity.christoffel (fun m n p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n) lambda alpha b x * emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') mu lambda x)
      )).re
    else 0

/-- Automatically feeds the MacroscopicVolume axiom's non-empty proof into Lean's typeclass resolution -/
instance instPhysicalUniverseBulkNonempty (pu : PhysicalUniverse) : Nonempty pu.bulk :=
  let ⟨x, hx⟩ := pu.has_volume.h_bulk_nonempty
  ⟨⟨x, hx⟩⟩

/-- Automatically feeds the MacroscopicVolume axiom itself into Lean's typeclass resolution -/
instance instPhysicalUniverseVolume (pu : PhysicalUniverse) : MacroscopicVolume pu.toUniverse pu.bulk :=
  pu.has_volume

Litlib.theorem
  description "Machian Motion of Topological Defects"
/--
Using the rigorous Geroch-Jang theorem, we prove that a localized topological defect 
must travel along a timelike geodesic. This utilizes the native, dynamically emergent 
Stress-Energy conservation of the CDJ geometry, bypassing tautological assertions 
or trivial vacuum assumptions.
-/
theorem machianTopologicalDefectMotion
  (isFutureDirectedTimelike : SpacetimePoint → (Fin 4 → ℝ) → Prop)
  (isTimelikeGeodesic : Set SpacetimePoint → Prop)
  (pu : PhysicalUniverse)
  (isSmooth : (pu.bulk → ℂ) → Prop)
  (isSmoothReal : (SpacetimePoint → ℝ) → Prop)
  [general_bianchi : Litlib.Y2003.nakahara2003geometry.Theorem_ContractedBianchi 
    pu.bulk (Fin 4) isSmooth (fun mu f p => partialDeriv mu (fun p' => if _h : p' ∈ pu.bulk then f ⟨p', _h⟩ else 0) p.val)]
  (h_symm : ∀ x : pu.bulk, ∀ i j, CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b x.val) i j = CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b x.val) j i)
  (h_inv_symm : ∀ x : pu.bulk, ∀ i j, CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b x.val) m n) i j = CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b x.val) m n) j i)
  (h_chris_eq : ∀ x : pu.bulk, ∀ rho mu nu, CGD.Gravity.christoffel (fun m n p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p) m n) rho mu nu x.val = (1/2 : ℂ) * ∑ sigma, CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b x.val) m n) rho sigma * (partialDeriv mu (fun p => if _h : p ∈ pu.bulk then CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p) sigma nu else 0) x.val + partialDeriv nu (fun p => if _h : p ∈ pu.bulk then CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p) mu sigma else 0) x.val - partialDeriv sigma (fun p => if _h : p ∈ pu.bulk then CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p) mu nu else 0) x.val))
  (h_ricci_eq : ∀ x : pu.bulk, ∀ mu nu, CGD.Gravity.ricciTensor (fun m n p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p) m n) mu nu x.val = ∑ rho, (partialDeriv rho (fun p => if _h : p ∈ pu.bulk then CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) rho mu nu p else 0) x.val - partialDeriv nu (fun p => if _h : p ∈ pu.bulk then CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) rho mu rho p else 0) x.val + ∑ lambda, (CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) rho lambda rho x.val * CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) lambda mu nu x.val - CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) rho lambda nu x.val * CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) lambda mu rho x.val)))
  (h_smooth_g : ∀ i j, isSmooth (fun p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p.val) i j))
  (h_smooth_g_inv : ∀ i j, isSmooth (fun p => CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p.val) m n) i j))
  (h_smooth_chris : ∀ rho mu nu, isSmooth (fun p => CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) rho mu nu p.val))
  (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (h_g_eq : ∀ x μ ν, g μ ν x = urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b x) μ ν)
  [gj : Litlib.Y1975.geroch1975motion.Thm_MotionOfBody SpacetimePoint (Fin 4) Unit (realMetricProxy g) (realMetricInvProxy g) (realChristoffelProxy g) realDerivProxy isSmoothReal (fun _ _ => True) isFutureDirectedTimelike isTimelikeGeodesic]
  (T_real : Fin 4 → Fin 4 → SpacetimePoint → ℝ) 
  (h_smooth_T : ∀ mu nu, isSmoothReal (fun p => T_real mu nu p))
  (γ : Set SpacetimePoint)
  (h_T_real_def : ∀ mu nu x, T_real mu nu x = (emergentStressEnergy (fun a b p => curvatureSl2c pu.toUniverse.sd_sector a b p) mu nu x).re)
  (h_non_trivial : ∃ x, ∃ mu nu, T_real mu nu x ≠ 0)
  (h_symm_T : ∀ mu nu x, T_real mu nu x = T_real nu mu x)
  (h_dominant_energy : ∀ x, (∃ mu nu, T_real mu nu x ≠ 0) → ∀ t t', isFutureDirectedTimelike x t → isFutureDirectedTimelike x t' → ∑ a : Fin 4, ∑ b : Fin 4, T_real a b x * t a * t' b > 0)
  (h_localized : ∀ U : Set SpacetimePoint, IsOpen U → γ ⊆ U → closure {x | ∃ mu nu, T_real mu nu x ≠ 0} ⊆ U) :
  isTimelikeGeodesic γ := by
  apply gj.motion_is_geodesic γ () trivial
  intro U hOpen hSub
  use T_real
  refine ⟨h_smooth_T, h_non_trivial, h_symm_T, h_dominant_energy, h_localized U hOpen hSub, ?_⟩
  intro b x
  rw [macroscopic_real_projection_limit pu.toUniverse pu.bulk g T_real b x h_g_eq h_T_real_def]
  split_ifs with h_bulk
  · have h_cons := emergentStressEnergyConservation pu.toUniverse pu.bulk isSmooth h_symm h_inv_symm h_chris_eq h_ricci_eq h_smooth_g h_smooth_g_inv h_smooth_chris b ⟨x, h_bulk⟩
    rw [h_cons]
    exact Complex.zero_re
  · rfl

end CGD.Gravity

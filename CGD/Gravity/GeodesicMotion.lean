-- FILENAME: CGD/Gravity/GeodesicMotion.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Gravity.StressEnergy.Conservation
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Axioms.PhysicalUniverse
import Mathlib.Topology.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Litlib.Y2003.nakahara2003geometry.Signature
import Litlib.Y1984.urbantke1984integrability.Signature
import Litlib.Y1951.papapetrou1951spinning.Signature

open Complex Matrix CGD.Foundations BigOperators Classical
open Topology CGD.Axioms Litlib.Y1951.papapetrou1951spinning

namespace CGD.Gravity

Litlib.theorem
  description "Machian Motion of Topological Defects"
/--
Using the rigorous Papapetrou (1951) theorem, we prove that a localized topological defect 
(a single-pole singularity in the gauge curvature) must travel along a complex geodesic of the 
dynamically emergent Urbantke geometry. This natively utilizes the exact complex covariant 
conservation of the emergent Stress-Energy tensor, evaluating strictly inside the macroscopic bulk.
-/
theorem machianTopologicalDefectMotion
  (pu : PhysicalUniverse)
  (isSmooth : (pu.bulk → ℂ) → Prop)
  (γ : ℂ → pu.bulk)
  (u : ℂ → (Fin 4 → ℂ))
  (du : ℂ → (Fin 4 → ℂ))
  (isSinglePole : (Fin 4 → Fin 4 → pu.bulk → ℂ) → (ℂ → pu.bulk) → Prop)
  [general_bianchi : Litlib.Y2003.nakahara2003geometry.Theorem_ContractedBianchi pu.bulk (Fin 4) isSmooth (bulkDeriv pu)]
  [symm_metric : Litlib.Y1984.urbantke1984integrability.Eq10_Symmetry]
  [papa : Litlib.Y1951.papapetrou1951spinning.Eq2_12 pu.bulk ℂ 
    (fun p => Matrix.of (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p.val) m n))
    (fun p => Matrix.of (fun m n => CGD.Gravity.matrixInv4x4 (fun a b => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p.val) a b) m n))
    (fun p rho mu nu => CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) rho mu nu p.val)
    (fun m n p => emergentStressEnergy (fun a b p' => curvatureSl2c pu.toUniverse.sd_sector a b p') m n p.val)
    (bulkDeriv pu) γ u du isSinglePole]
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
                CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) rho lambda nu p.val * CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p') m n) lambda mu rho p.val)))
  (h_single_pole : isSinglePole (fun m n p => emergentStressEnergy (fun a b p' => curvatureSl2c pu.toUniverse.sd_sector a b p') m n p.val) γ) :
  ∀ s alpha, du s alpha + ∑ mu : Fin 4, ∑ nu : Fin 4, CGD.Gravity.christoffel (fun m n p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p) m n) alpha mu nu (γ s).val * u s mu * u s nu = 0 := by
  intro s alpha
  apply papa.single_pole_eom
  · intro x b
    exact emergentStressEnergyConservation pu isSmooth h_metric_eq10 h_smooth_g h_smooth_g_inv h_smooth_chris h_chris_eq h_ricci_eq b x
  · exact h_single_pole

end CGD.Gravity

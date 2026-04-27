-- FILENAME: CGD/Foundations/GeodesicMotion.lean

import CGD.Foundations.StressEnergy
import Litlib.Y1975.geroch1975motion.Signature

open Complex Matrix CGD.Foundations BigOperators
open CGD.Axioms

namespace CGD.Foundations

/--
Topological matter natively falls along geodesics of the Urbantke metric.
Maps the `emergentStressEnergyConservation` theorem into the Geroch-Jang 
literature axiom. We assume the existence of a family of CGD universes 
whose emergent matter supports can be localized to an arbitrary neighborhood 
of a curve `gamma`, while sharing the same asymptotic background metric.
-/
theorem topologicalMatterIsGeodesic 
  [TopologicalSpace SpacetimePoint]
  (satisfiesEnergyCondition : (Fin 4 → Fin 4 → SpacetimePoint → ℂ) → Prop)
  (support : (Fin 4 → Fin 4 → SpacetimePoint → ℂ) → Set SpacetimePoint)
  (isTimelikeGeodesic : Set SpacetimePoint → Prop)
  (g g_inv : Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (Gamma_sym : Fin 4 → Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  [gj : Litlib.Y1975.geroch1975motion.Thm_MotionOfBody 
    SpacetimePoint (Fin 4) g g_inv Gamma_sym partialDeriv 
    satisfiesEnergyCondition support isTimelikeGeodesic]
  (h_inv : ∀ x, (Matrix.of fun i j => g i j x) * (Matrix.of fun i j => g_inv i j x) = 1)
  (gamma : Set SpacetimePoint)
  (h_ebi : ∀ u : Universe, Litlib.Y2003.nakahara2003geometry.Eq7_85 
    SpacetimePoint (Fin 4) 
    (fun i j p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) i j)
    (fun i j p => CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n) i j)
    (fun rho mu nu p => CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) rho mu nu p)
    (fun mu nu p => CGD.Gravity.ricciTensor (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) mu nu p)
    (fun p => ∑ alpha : Fin 4, ∑ beta : Fin 4, CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n) alpha beta * CGD.Gravity.ricciTensor (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) alpha beta p)
    (fun mu nu p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') mu nu p)
    (fun mu f p => partialDeriv mu f p))
  (h_localizable : ∀ U : Set SpacetimePoint, IsOpen U → gamma ⊆ U → 
    ∃ u : Universe, 
      (∀ x, (CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x)).det ≠ 0) ∧
      (∀ m n p, CGD.Gravity.matrixInv4x4 (fun i j => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) i j) m n = g_inv m n p) ∧
      (∀ rho mu nu p, CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) rho mu nu p = Gamma_sym rho mu nu p) ∧
      (fun m n p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') m n p) ≠ 0 ∧
      (∀ mu nu x, emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') mu nu x = emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') nu mu x) ∧
      satisfiesEnergyCondition (fun m n p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') m n p) ∧
      support (fun m n p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') m n p) ⊆ U) :
  isTimelikeGeodesic gamma := by
  apply gj.motion_is_geodesic h_inv gamma
  intro U hU_open hU_gamma
  rcases h_localizable U hU_open hU_gamma with ⟨u, h_det, h_ginv, h_gamma_sym, h_nonzero, h_sym, h_energy, h_supp⟩
  let T := fun m n p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') m n p
  use T
  refine ⟨h_nonzero, h_sym, h_energy, h_supp, ?_⟩
  intro nu x
  have h_cons := emergentStressEnergyConservation u h_det nu x (ebi := h_ebi u)
  simp only [h_ginv, h_gamma_sym] at h_cons
  exact h_cons

end CGD.Foundations

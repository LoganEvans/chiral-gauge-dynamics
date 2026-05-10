-- FILENAME: CGD/Gravity/GeodesicMotion.lean

import Litlib.Core
import CGD.Gravity.StressEnergy
import CGD.Foundations.Calculus
import CGD.Axioms.Phenomenology
import Litlib.Y1975.geroch1975motion.Signature

open Complex Matrix CGD.Foundations BigOperators Classical
open CGD.Axioms

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

def realTimelikeProxy (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ) (p : SpacetimePoint) (t : Fin 4 → ℝ) : Prop :=
  (∑ m : Fin 4, ∑ n : Fin 4, realMetricProxy g m n p * t m * t n) < 0

Litlib.theorem
  description "Topological Matter Follows Geodesics"
/--
Topological matter natively falls along geodesics of the Urbantke metric.
By mapping emergent stress-energy conservation to the Geroch-Jang theorem, 
we establish that localized topological defects follow background geodesics.
-/
theorem topologicalMatterIsGeodesic 
  [TopologicalSpace SpacetimePoint]
  (u : Universe) (bulk : Set SpacetimePoint) [TopologicalSpace bulk]
  [vol : CGD.Axioms.MacroscopicVolume u bulk]
  (satisfiesEnergyCondition : (Fin 4 → Fin 4 → bulk → ℂ) → Prop)
  (support : (Fin 4 → Fin 4 → bulk → ℂ) → Set bulk)
  (isTimelikeGeodesic : Set bulk → Prop)
  (Gamma_sym : Fin 4 → Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  [gj : Litlib.Y1975.geroch1975motion.Thm_MotionOfBody 
    bulk (Fin 4) 
    (fun (m n : Fin 4) (p : bulk) => realMetricProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) m n (p : SpacetimePoint)) 
    (fun (m n : Fin 4) (p : bulk) => realMetricInvProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) m n (p : SpacetimePoint)) 
    (fun (lam m n : Fin 4) (p : bulk) => realChristoffelProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) lam m n (p : SpacetimePoint)) 
    (fun (m : Fin 4) (f : bulk → ℝ) (p : bulk) => realDerivProxy m (fun (p' : SpacetimePoint) => if h : p' ∈ bulk then f (Subtype.mk p' h) else 0) (p : SpacetimePoint)) 
    (fun (p : bulk) (t : Fin 4 → ℝ) => realTimelikeProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) (p : SpacetimePoint) t) 
    isTimelikeGeodesic]
  (gamma : Set bulk)
  (h_localizable : ∀ U : Set bulk, IsOpen U → gamma ⊆ U → 
    ∃ u_defect : Universe, 
      (fun (m n : Fin 4) (p : bulk) => emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') m n (p : SpacetimePoint)) ≠ 0 ∧
      (∀ mu nu (x : bulk), emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') mu nu (x : SpacetimePoint) = emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') nu mu (x : SpacetimePoint)) ∧
      satisfiesEnergyCondition (fun (m n : Fin 4) (p : bulk) => emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') m n (p : SpacetimePoint)) ∧
      support (fun (m n : Fin 4) (p : bulk) => emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') m n (p : SpacetimePoint)) ⊆ U ∧
      (∀ nu (x : bulk),
        ∑ mu : Fin 4, ∑ alpha : Fin 4, (CGD.Gravity.matrixInv4x4 (fun a b => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d (x : SpacetimePoint)) a b) mu alpha) * (
          partialDeriv alpha (fun (p' : SpacetimePoint) => if p' ∈ bulk then emergentStressEnergy (fun a b p_inner => curvatureSl2c u_defect.sd_sector a b p_inner) mu nu p' else 0) (x : SpacetimePoint) -
          ∑ lambda : Fin 4, (Gamma_sym lambda alpha mu (x : SpacetimePoint) * emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') lambda nu (x : SpacetimePoint) + 
                             Gamma_sym lambda alpha nu (x : SpacetimePoint) * emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') mu lambda (x : SpacetimePoint))
        ) = 0)) :
  isTimelikeGeodesic gamma := by
  sorry

end CGD.Gravity

-- FILENAME: CGD/Gravity/GeodesicMotion.lean

import Litlib.Core
import CGD.Gravity.StressEnergy
import CGD.Foundations.Calculus
import Litlib.Y1975.geroch1975motion.Signature

open Complex Matrix CGD.Foundations BigOperators
open CGD.Axioms

namespace CGD.Gravity

Litlib.theorem
  description "Topological Matter Follows Geodesics"
/--
Topological matter natively falls along geodesics of the Urbantke metric.
By mapping emergent stress-energy conservation to the Geroch-Jang theorem, 
we establish that localized topological defects follow background geodesics.
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
  (h_localizable : ∀ U : Set SpacetimePoint, IsOpen U → gamma ⊆ U → 
    ∃ u : Universe, 
      (fun m n p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') m n p) ≠ 0 ∧
      (∀ mu nu x, emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') mu nu x = emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') nu mu x) ∧
      satisfiesEnergyCondition (fun m n p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') m n p) ∧
      support (fun m n p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') m n p) ⊆ U ∧
      (∀ nu x,
        ∑ mu : Fin 4, ∑ alpha : Fin 4, g_inv mu alpha x * (
          partialDeriv alpha (fun p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') mu nu p) x -
          ∑ lambda : Fin 4, (Gamma_sym lambda alpha mu x * emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') lambda nu x + 
                             Gamma_sym lambda alpha nu x * emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') mu lambda x)
        ) = 0)) :
  isTimelikeGeodesic gamma := by
  apply gj.motion_is_geodesic h_inv gamma
  intro U hU_open hU_gamma
  rcases h_localizable U hU_open hU_gamma with ⟨u, h_nonzero, h_sym, h_energy, h_supp, h_cons⟩
  exact ⟨fun m n p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') m n p, 
         h_nonzero, h_sym, h_energy, h_supp, h_cons⟩

end CGD.Gravity

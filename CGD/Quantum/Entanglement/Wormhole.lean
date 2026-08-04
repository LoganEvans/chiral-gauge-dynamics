-- FILENAME: CGD/Quantum/Entanglement/Wormhole.lean

import Litlib.Core
import CGD.Quantum.Entanglement.Geometry
import CGD.Quantum.Definitions
import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse

set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Math CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Quantum

section DegenerateFluxTube

variable (pu : PhysicalUniverse)
variable (x y : SpacetimePoint) (theta : ℝ)

@[litlib_track "Degenerate Flux Tube Metric - X Endpoint"]
theorem degenerateFluxTubeMetricX
  (h_linked : isTopologicallyLinked pu.toUniverse.sd_sector x y theta) :
  (urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.sd_sector m n x)).det = 0 := by
  unfold isTopologicallyLinked at h_linked
  rcases h_linked with ⟨γ, θ, h_γ_0, _h_γ_1, h_θ_0, _h_θ_1, h_path⟩
  have h_x_val : ∀ mu, pu.toUniverse.sd_sector mu x = rotateYAxis fluxTubeFrame (θ 0) mu x := by
    intro mu
    have h_t := (h_path 0) (by linarith) (by linarith)
    have h_eval := h_t.1 mu
    rw [h_γ_0] at h_eval
    exact h_eval
  have h_x_deriv : ∀ mu nu, partialDerivSl2c nu (pu.toUniverse.sd_sector mu) x = partialDerivSl2c nu (rotateYAxis fluxTubeFrame (θ 0) mu) x := by
    intro mu nu
    have h_t := (h_path 0) (by linarith) (by linarith)
    have h_eval := h_t.2 mu nu
    rw [h_γ_0] at h_eval
    exact h_eval
  have h_curv_x : ∀ mu nu, curvatureSl2c pu.toUniverse.sd_sector mu nu x = curvatureSl2c (rotateYAxis fluxTubeFrame (θ 0)) mu nu x :=
    entang_curvature_congruence pu.toUniverse.sd_sector (rotateYAxis fluxTubeFrame (θ 0)) x h_x_val h_x_deriv
  have h_F_x : (fun m n => curvatureSl2c pu.toUniverse.sd_sector m n x) = (fun m n => curvatureSl2c (rotateYAxis fluxTubeFrame (θ 0)) m n x) := by funext m n; exact h_curv_x m n
  rw [h_F_x]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  exact rotateYAxis_metric_electric_zero_at (θ 0) j x

@[litlib_track "Degenerate Flux Tube Metric - Y Endpoint"]
theorem degenerateFluxTubeMetricY
  (h_linked : isTopologicallyLinked pu.toUniverse.sd_sector x y theta) :
  (urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.sd_sector m n y)).det = 0 := by
  unfold isTopologicallyLinked at h_linked
  rcases h_linked with ⟨γ, θ, _h_γ_0, h_γ_1, _h_θ_0, h_θ_1, h_path⟩
  have h_y_val : ∀ mu, pu.toUniverse.sd_sector mu y = rotateYAxis fluxTubeFrame (θ 1) mu y := by
    intro mu
    have h_t := (h_path 1) (by linarith) (by linarith)
    have h_eval := h_t.1 mu
    rw [h_γ_1] at h_eval
    exact h_eval
  have h_y_deriv : ∀ mu nu, partialDerivSl2c nu (pu.toUniverse.sd_sector mu) y = partialDerivSl2c nu (rotateYAxis fluxTubeFrame (θ 1) mu) y := by
    intro mu nu
    have h_t := (h_path 1) (by linarith) (by linarith)
    have h_eval := h_t.2 mu nu
    rw [h_γ_1] at h_eval
    exact h_eval
  have h_curv_y : ∀ mu nu, curvatureSl2c pu.toUniverse.sd_sector mu nu y = curvatureSl2c (rotateYAxis fluxTubeFrame (θ 1)) mu nu y :=
    entang_curvature_congruence pu.toUniverse.sd_sector (rotateYAxis fluxTubeFrame (θ 1)) y h_y_val h_y_deriv
  have h_F_y : (fun m n => curvatureSl2c pu.toUniverse.sd_sector m n y) = (fun m n => curvatureSl2c (rotateYAxis fluxTubeFrame (θ 1)) m n y) := by funext m n; exact h_curv_y m n
  rw [h_F_y]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  exact rotateYAxis_metric_electric_zero_at (θ 1) j y

end DegenerateFluxTube

end CGD.Quantum

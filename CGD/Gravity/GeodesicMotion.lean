-- FILENAME: CGD/Gravity/GeodesicMotion.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Gravity.StressEnergy
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Axioms.Phenomenology
import Mathlib.Topology.Basic
import CGD.Gravity.MacroscopicVacuum.Basic
import CGD.Gravity.MacroscopicVacuum.GR
import Litlib.Y1949.infeld1949motion.Signature
import Litlib.Y1991.capovilla1991pure.Signature

set_option linter.unusedVariables false

open Complex Matrix CGD.Foundations BigOperators Classical
open CGD.Axioms Litlib.Y1991.capovilla1991pure

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

def realFutureTimelikeProxy (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ) (p : SpacetimePoint) (t : Fin 4 → ℝ) : Prop :=
  realTimelikeProxy g p t ∧ t 0 > 0

Litlib.theorem
  description "Machian Motion of Topological Defects"
/--
If the bulk satisfies the CDJ state (instantiated by `dynamicExactAbelianSolution` to avoid vacuous truths), 
then the new Infeld-Schild `Litlib` theorem applies, constraining defects to geodesics.
The metric is strictly defined as the emergent Urbantke metric of the topological background.
-/
theorem machianTopologicalDefectMotion
  (isLorentzian : (Fin 4 → Fin 4 → SpacetimePoint → ℂ) → Prop)
  (isSmoothCurve : (ℝ → SpacetimePoint) → Prop)
  (hasNonZeroTangent : (ℝ → SpacetimePoint) → Prop)
  (isTimelike : (Fin 4 → Fin 4 → SpacetimePoint → ℂ) → (ℝ → SpacetimePoint) → Prop)
  (isTestParticleWorldline : (Fin 4 → Fin 4 → SpacetimePoint → ℂ) → (ℝ → SpacetimePoint) → Prop)
  (isGeodesic : (Fin 4 → Fin 4 → SpacetimePoint → ℂ) → (ℝ → SpacetimePoint) → Prop)
  [is_thm : Litlib.Y1949.infeld1949motion.TestParticleGeodesic SpacetimePoint 
    (Fin 4 → Fin 4 → SpacetimePoint → ℂ) 
    isLorentzian 
    (fun g => ∀ x μ ν, ricciTensor g μ ν x = 0) 
    isSmoothCurve hasNonZeroTangent isTimelike isTestParticleWorldline isGeodesic]
  (c : ℂ) (hc : c ≠ 0)
  (u : Universe)
  (urbantke_tetrad : TetradField)
  (metric_compat : ∀ x μ ν, metricFromTetrad urbantke_tetrad μ ν x = 
                           CGD.Gravity.urbantkeMetric (fun m n => curvatureSl2c u.sd_sector m n x) μ ν)
  (Psi : SpacetimePoint → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ)
  [eq2_2b : Eq2_2b SpacetimePoint (cgd_dSigma urbantke_tetrad) (cgd_omega u) (cgd_Sigma urbantke_tetrad) cgd_eps2_up]
  [eq2_2c : Eq2_2c SpacetimePoint (cgd_R u) Psi (cgd_Sigma urbantke_tetrad)]
  [th_ricci : Theorem_Eq2_2c_RicciFlat 
    (Spacetime := SpacetimePoint)
    (theta := fun x => cgd_theta urbantke_tetrad x) 
    (g := fun x μ ν => metricFromTetrad urbantke_tetrad μ ν x) 
    (eps2_down := cgd_eps2_down) 
    (eps2_bar_down := cgd_eps2_bar_down) 
    (eps2_right := cgd_eps2_bar_down)
    (eps2_up := cgd_eps2_up)
    (R := cgd_R u) 
    (Psi := fun x => Psi x) 
    (Sigma := fun x => cgd_Sigma urbantke_tetrad x) 
    (dSigma := fun x => cgd_dSigma urbantke_tetrad x)
    (omega := fun x => cgd_omega u x)
    (isRicciFlat := fun g => ∀ x μ ν, ricciTensor (fun m n p => g p m n) μ ν x = 0)]
  (h_exact : CGD.Gravity.satisfiesPureCdjConstraint (fun p m n => CGD.Gravity.cgdAdjointCurvature u m n p) ∧ 
             (∀ x, curvatureSl2c u.sd_sector 1 2 x = c • toSl2c sigmaX) ∧
             (∃ x, curvatureSl2c u.sd_sector 1 2 x ≠ 0))
  (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (h_g_eq : ∀ x μ ν, g μ ν x = urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x) μ ν)
  (γ : ℝ → SpacetimePoint)
  (h_lorentzian : isLorentzian g)
  (h_test_particle : isTestParticleWorldline g γ) :
  isGeodesic g γ := by
  apply is_thm.test_particle_motion_is_geodesic g γ
  · exact h_lorentzian
  · intros x μ ν
    have h_g_eq_fun : g = fun m n p => urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n := by
      ext m n p
      exact h_g_eq p m n
    rw [h_g_eq_fun]
    exact macroscopicVacuumGR u urbantke_tetrad metric_compat Psi x μ ν
  · exact h_test_particle

end CGD.Gravity

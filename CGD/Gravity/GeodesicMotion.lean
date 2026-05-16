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
import Litlib.Y1989.capovilla1989general.Signature

set_option linter.unusedVariables false

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
  [eq2_2c : Litlib.Y1989.capovilla1989general.CDJImpliesRicciFlat 
    SpacetimePoint 
    (fun F x μ ν => urbantkeMetric (fun m n => toSl2c (F x 0 m n • sigma1.val + F x 1 m n • sigma2.val + F x 2 m n • sigma3.val)) μ ν) 
    (fun g x μ ν => ricciTensor (fun m n p => g p m n) μ ν x)]
  (c : ℂ) (hc : c ≠ 0)
  (u : Universe)
  (e : TetradField)
  (h_exact : CGD.Gravity.satisfiesPureCdjConstraint (fun p m n => CGD.Gravity.cgdAdjointCurvature u m n p) ∧ 
             (∀ x, curvatureSl2c u.sd_sector 1 2 x = c • toSl2c sigmaX) ∧
             (∃ x, curvatureSl2c u.sd_sector 1 2 x ≠ 0))
  (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (h_g_eq : ∀ x μ ν, g μ ν x = metricFromTetrad e μ ν x)
  (h_urbantke : ∀ x μ ν, metricFromTetrad e μ ν x = urbantkeMetric (fun m n => toSl2c (curvatureSl2c u.sd_sector m n x).val) μ ν)
  (h_nondeg : ∀ x, (urbantkeMetric (fun m n => toSl2c (curvatureSl2c u.sd_sector m n x).val)).det ≠ 0)
  (γ : ℝ → SpacetimePoint)
  (h_lorentzian : isLorentzian g)
  (h_test_particle : isTestParticleWorldline g γ) :
  isGeodesic g γ := by
  apply is_thm.test_particle_motion_is_geodesic g γ
  · exact h_lorentzian
  · intros x μ ν
    have h_cdj := h_exact.1
    have h_vac := macroscopicVacuumGR u e h_urbantke h_nondeg h_cdj
    have h_g_eq_fun : g = metricFromTetrad e := by
      ext m n p
      exact h_g_eq p m n
    rw [h_g_eq_fun]
    exact h_vac x μ ν
  · exact h_test_particle

end CGD.Gravity

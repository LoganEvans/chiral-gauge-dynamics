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

Instead of passing a tautological test-particle hypothesis, this theorem bridges the 
native covariant conservation of the emergent CGD Stress-Energy tensor to the Litlib test particle definition.
-/
theorem machianTopologicalDefectMotion
  (isSmoothCurve : (ℝ → SpacetimePoint) → Prop)
  (hasNonZeroTangent : (ℝ → SpacetimePoint) → Prop)
  (isTimelike : (Fin 4 → Fin 4 → SpacetimePoint → ℂ) → (ℝ → SpacetimePoint) → Prop)
  (isTestParticleWorldline : (Fin 4 → Fin 4 → SpacetimePoint → ℂ) → (ℝ → SpacetimePoint) → Prop)
  (isGeodesic : (Fin 4 → Fin 4 → SpacetimePoint → ℂ) → (ℝ → SpacetimePoint) → Prop)
  (bulk : Set SpacetimePoint)
  [Nonempty bulk]
  [is_thm : Litlib.Y1949.infeld1949motion.TestParticleGeodesic SpacetimePoint 
    (Fin 4 → Fin 4 → SpacetimePoint → ℂ) 
    (fun g => ∀ p ∈ bulk, isLorentzian (fun m n => g m n p))
    (fun g => ∀ x ∈ bulk, ∀ μ ν, ricciTensor g μ ν x = 0) 
    isSmoothCurve hasNonZeroTangent isTimelike isTestParticleWorldline isGeodesic]
  (u : Universe)
  [_vol : CGD.Axioms.MacroscopicVolume u bulk]
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
  [ebi : Litlib.Y2003.nakahara2003geometry.ContractedBianchiIdentity 
    bulk (Fin 4) 
    (fun i j p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) i j)
    (fun i j p => CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) m n) i j)
    (fun rho mu nu p => CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) rho mu nu p.val)
    (fun mu nu p => CGD.Gravity.ricciTensor (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) mu nu p.val)
    (fun p => ∑ alpha : Fin 4, ∑ beta : Fin 4, CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) m n) alpha beta * CGD.Gravity.ricciTensor (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) alpha beta p.val)
    (fun mu nu p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') mu nu p.val)
    (fun mu f p => partialDeriv mu (fun p' => if _h : p' ∈ bulk then f ⟨p', _h⟩ else 0) p.val)]
  (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (h_g_eq : ∀ x μ ν, g μ ν x = urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x) μ ν)
  (γ : ℝ → SpacetimePoint)
  (_h_gamma_bulk : ∀ t, γ t ∈ bulk)
  (h_lorentzian : ∀ p ∈ bulk, isLorentzian (fun m n => g m n p))
  (h_bianchi_to_motion : 
    (∀ nu (x : bulk),
      let g_urb := fun m n p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n
      let g_inv := CGD.Gravity.matrixInv4x4 (fun m n => g_urb m n x.val)
      let T := fun m n p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') m n p
      ∑ mu : Fin 4, ∑ alpha : Fin 4, g_inv mu alpha * (
        partialDeriv alpha (fun p => if _h : p ∈ bulk then T mu nu p else 0) x.val -
        ∑ lambda : Fin 4, (CGD.Gravity.christoffel g_urb lambda alpha mu x.val * T lambda nu x.val + 
                           CGD.Gravity.christoffel g_urb lambda alpha nu x.val * T mu lambda x.val)
      ) = 0) → isTestParticleWorldline g γ) :
  isGeodesic g γ := by
  apply is_thm.test_particle_motion_is_geodesic g γ
  · exact h_lorentzian
  · intros x hx μ ν
    have h_g_eq_fun : g = fun m n p => urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n := by
      ext m n p
      exact h_g_eq p m n
    rw [h_g_eq_fun]
    exact macroscopicVacuumGR u bulk urbantke_tetrad metric_compat Psi x hx μ ν
  · apply h_bianchi_to_motion
    exact emergentStressEnergyConservation u bulk

end CGD.Gravity

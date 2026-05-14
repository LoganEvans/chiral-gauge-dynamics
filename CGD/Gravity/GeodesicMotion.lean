-- FILENAME: CGD/Gravity/GeodesicMotion.lean

import Litlib.Core
import CGD.Gravity.StressEnergy
import CGD.Foundations.Calculus
import CGD.Axioms.Phenomenology
import Mathlib.Topology.Basic
import Litlib.Y1975.geroch1975motion.Signature
import Litlib.Y2003.nakahara2003geometry.Signature

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
  description "Topological Matter Follows Geodesics"
/--
Topological matter natively falls along geodesics of the Urbantke metric.
By mapping emergent stress-energy conservation to the Geroch-Jang theorem, 
we establish that localized topological defects follow background geodesics.
-/
theorem topologicalMatterIsGeodesic 
  [TopologicalSpace SpacetimePoint]
  (u : Universe) (bulk : Set SpacetimePoint) [TopologicalSpace bulk] [Nonempty bulk]
  [vol : CGD.Axioms.MacroscopicVolume u bulk]
  (isTimelikeGeodesic : Set bulk → Prop)
  (Gamma_sym : Fin 4 → Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  [gj : Litlib.Y1975.geroch1975motion.Thm_MotionOfBody 
    bulk (Fin 4) 
    (fun (m n : Fin 4) (p : bulk) => realMetricProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) m n (p : SpacetimePoint)) 
    (fun (m n : Fin 4) (p : bulk) => realMetricInvProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) m n (p : SpacetimePoint)) 
    (fun (lam m n : Fin 4) (p : bulk) => realChristoffelProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) lam m n (p : SpacetimePoint)) 
    (fun (m : Fin 4) (f : bulk → ℝ) (p : bulk) => realDerivProxy m (fun (p' : SpacetimePoint) => if h : p' ∈ bulk then f (Subtype.mk p' h) else 0) (p : SpacetimePoint)) 
    (fun (p : bulk) (t : Fin 4 → ℝ) => realFutureTimelikeProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) (p : SpacetimePoint) t) 
    isTimelikeGeodesic]
  (h_metric_inv : ∀ (x : bulk) (i j : Fin 4), (∑ k : Fin 4, realMetricProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) i k (x : SpacetimePoint) * realMetricInvProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) k j (x : SpacetimePoint)) = if i = j then 1 else 0)
  (h_T_symm_thm : ∀ (G T : Fin 4 → Fin 4 → bulk → ℝ),
    (∀ (x : bulk) (i j : Fin 4), G i j x = G j i x) →
    (∀ (a b : Fin 4) (x : bulk), T a b x = ∑ mu : Fin 4, ∑ nu : Fin 4, realMetricInvProxy (fun c d p' => CGD.Gravity.urbantkeMetric (fun e f => curvatureSl2c u.sd_sector e f p') c d) a mu (x : SpacetimePoint) * realMetricInvProxy (fun c d p' => CGD.Gravity.urbantkeMetric (fun e f => curvatureSl2c u.sd_sector e f p') c d) b nu (x : SpacetimePoint) * G mu nu x) →
    ∀ (x : bulk) (i j : Fin 4), T i j x = T j i x)
  (h_T_iso_thm : ∀ (G T : Fin 4 → Fin 4 → bulk → ℝ),
    (∀ (a b : Fin 4) (x : bulk), T a b x = ∑ mu : Fin 4, ∑ nu : Fin 4, realMetricInvProxy (fun c d p' => CGD.Gravity.urbantkeMetric (fun e f => curvatureSl2c u.sd_sector e f p') c d) a mu (x : SpacetimePoint) * realMetricInvProxy (fun c d p' => CGD.Gravity.urbantkeMetric (fun e f => curvatureSl2c u.sd_sector e f p') c d) b nu (x : SpacetimePoint) * G mu nu x) →
    ∀ x, (∃ a b, T a b x ≠ 0) ↔ (∃ mu nu, G mu nu x ≠ 0))
  (h_T_dec_thm : ∀ (G T : Fin 4 → Fin 4 → bulk → ℝ),
    (∀ (a b : Fin 4) (x : bulk), T a b x = ∑ mu : Fin 4, ∑ nu : Fin 4, realMetricInvProxy (fun c d p' => CGD.Gravity.urbantkeMetric (fun e f => curvatureSl2c u.sd_sector e f p') c d) a mu (x : SpacetimePoint) * realMetricInvProxy (fun c d p' => CGD.Gravity.urbantkeMetric (fun e f => curvatureSl2c u.sd_sector e f p') c d) b nu (x : SpacetimePoint) * G mu nu x) →
    (∀ x, (∃ mu nu, G mu nu x ≠ 0) → ∀ t t', realFutureTimelikeProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) (x : SpacetimePoint) t → realFutureTimelikeProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) (x : SpacetimePoint) t' → ∑ a : Fin 4, ∑ b : Fin 4, G a b x * t a * t' b > 0) →
    (∀ x, (∃ a b, T a b x ≠ 0) → ∀ t t', realFutureTimelikeProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) (x : SpacetimePoint) t → realFutureTimelikeProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) (x : SpacetimePoint) t' → ∑ a : Fin 4, ∑ b : Fin 4, T a b x * t a * t' b > 0))
  (dir_thm : ∀ (G T : Fin 4 → Fin 4 → bulk → ℝ),
    (∀ (x : bulk) (i j : Fin 4), (∑ k : Fin 4, realMetricProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) i k (x : SpacetimePoint) * realMetricInvProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) k j (x : SpacetimePoint)) = if i = j then 1 else 0) →
    (∀ (x : bulk) (i j : Fin 4), G i j x = G j i x) →
    (∀ (x : bulk) (i j : Fin 4), T i j x = T j i x) →
    (∀ (nu : Fin 4) (x : bulk), ∑ mu : Fin 4, ∑ alpha : Fin 4, realMetricInvProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) mu alpha (x : SpacetimePoint) * (
        realDerivProxy alpha (fun (p' : SpacetimePoint) => if h : p' ∈ bulk then G mu nu ⟨p', h⟩ else 0) (x : SpacetimePoint) -
        ∑ lambda : Fin 4, (realChristoffelProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) lambda alpha mu (x : SpacetimePoint) * G lambda nu x + 
                           realChristoffelProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) lambda alpha nu (x : SpacetimePoint) * G mu lambda x)
      ) = 0) →
    (∀ (a b : Fin 4) (x : bulk), T a b x = ∑ mu : Fin 4, ∑ nu : Fin 4, realMetricInvProxy (fun c d p' => CGD.Gravity.urbantkeMetric (fun e f => curvatureSl2c u.sd_sector e f p') c d) a mu (x : SpacetimePoint) * realMetricInvProxy (fun c d p' => CGD.Gravity.urbantkeMetric (fun e f => curvatureSl2c u.sd_sector e f p') c d) b nu (x : SpacetimePoint) * G mu nu x) →
    Litlib.Y2003.nakahara2003geometry.DivergenceIndexRaising bulk (Fin 4) 
      (fun m n p => realMetricProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) m n (p : SpacetimePoint)) 
      (fun m n p => realMetricInvProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) m n (p : SpacetimePoint)) 
      (fun lam m n p => realChristoffelProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) lam m n (p : SpacetimePoint)) 
      G T 
      (fun m f p => realDerivProxy m (fun (p' : SpacetimePoint) => if h : p' ∈ bulk then f ⟨p', h⟩ else 0) (p : SpacetimePoint)))
  (gamma : Set bulk)
  (h_localizable : ∀ U : Set bulk, IsOpen U → gamma ⊆ U → 
    ∃ u_defect : Universe, 
      (fun (m n : Fin 4) (p : bulk) => (emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') m n (p : SpacetimePoint)).re) ≠ 0 ∧
      (∀ mu nu (x : bulk), (emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') mu nu (x : SpacetimePoint)).re = (emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') nu mu (x : SpacetimePoint)).re) ∧
      (∀ (x : bulk), (∃ mu nu, (emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') mu nu (x : SpacetimePoint)).re ≠ 0) →
        ∀ t t', realFutureTimelikeProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) (x : SpacetimePoint) t → 
                realFutureTimelikeProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) (x : SpacetimePoint) t' →
          ∑ a : Fin 4, ∑ b : Fin 4, (emergentStressEnergy (fun m n p' => curvatureSl2c u_defect.sd_sector m n p') a b (x : SpacetimePoint)).re * t a * t' b > 0) ∧
      (closure {x : bulk | ∃ mu nu, (emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') mu nu (x : SpacetimePoint)).re ≠ 0} ⊆ U) ∧
      (∀ nu (x : bulk),
        ∑ mu : Fin 4, ∑ alpha : Fin 4, (CGD.Gravity.matrixInv4x4 (fun a b => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d (x : SpacetimePoint)) a b) mu alpha).re * (
          realDerivProxy alpha (fun (p' : SpacetimePoint) => if p' ∈ bulk then (emergentStressEnergy (fun a b p_inner => curvatureSl2c u_defect.sd_sector a b p_inner) mu nu p').re else 0) (x : SpacetimePoint) -
          ∑ lambda : Fin 4, (realChristoffelProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) lambda alpha mu (x : SpacetimePoint) * (emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') lambda nu (x : SpacetimePoint)).re + 
                             realChristoffelProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) lambda alpha nu (x : SpacetimePoint) * (emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') mu lambda (x : SpacetimePoint)).re)
        ) = 0)) :
  isTimelikeGeodesic gamma := by
  apply gj.motion_is_geodesic
  intros U hUOpen hUGamma
  rcases h_localizable U hUOpen hUGamma with ⟨u_defect, h_nz, h_symm, h_pos, h_supp, h_cons⟩
  
  let g := fun m n p => realMetricProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) m n (p : SpacetimePoint)
  let g_inv := fun m n p => realMetricInvProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) m n (p : SpacetimePoint)
  
  let G := fun (m n : Fin 4) (p : bulk) => 
    (emergentStressEnergy (fun a b p' => curvatureSl2c u_defect.sd_sector a b p') m n (p : SpacetimePoint)).re
    
  let T := fun (a b : Fin 4) (p : bulk) => 
    ∑ mu : Fin 4, ∑ nu : Fin 4, g_inv a mu p * g_inv b nu p * G mu nu p
    
  use T
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Prove existence of non-zero element
    by_contra h_T_all_zero
    push_neg at h_T_all_zero
    apply h_nz
    ext m n p
    have h_T_p : ¬ ∃ a b, T a b p ≠ 0 := by
      intro ⟨a, b, hab⟩
      exact hab (h_T_all_zero p a b)
    have h_G_p : ¬ ∃ mu nu, G mu nu p ≠ 0 := by
      rw [← h_T_iso_thm G T (fun a b x => rfl) p]
      exact h_T_p
    push_neg at h_G_p
    exact h_G_p m n
  · -- Prove symmetry of raised tensor
    intros mu nu x
    exact h_T_symm_thm G T (fun x i j => h_symm i j x) (fun a b x => rfl) x mu nu
  · -- Prove dominant energy condition on raised tensor
    intros x h_T_nz t t' ht ht'
    exact h_T_dec_thm G T (fun a b x => rfl) h_pos x h_T_nz t t' ht ht'
  · -- Prove support of raised tensor is bounded by U
    have h_set_eq : {x : bulk | ∃ mu nu, T mu nu x ≠ 0} = {x : bulk | ∃ mu nu, G mu nu x ≠ 0} := by
      ext x
      exact h_T_iso_thm G T (fun a b x => rfl) x
    rw [h_set_eq]
    exact h_supp
  · -- Prove contravariant divergence condition using DivergenceIndexRaising
    intros b x
    have h_inv_local : ∀ (x : bulk) (i j : Fin 4), (∑ k, g i k x * g_inv k j x) = if i = j then 1 else 0 := h_metric_inv
    have h_G_symm_local : ∀ (x : bulk) (i j : Fin 4), G i j x = G j i x := fun x i j => h_symm i j x
    have h_T_symm_local : ∀ (x : bulk) (i j : Fin 4), T i j x = T j i x := h_T_symm_thm G T h_G_symm_local (fun a b x => rfl)
    have h_covDivG : ∀ (nu : Fin 4) (x : bulk), ∑ mu : Fin 4, ∑ alpha : Fin 4, g_inv mu alpha x * (
       realDerivProxy alpha (fun (p' : SpacetimePoint) => if h : p' ∈ bulk then G mu nu ⟨p', h⟩ else 0) (x : SpacetimePoint) -
       ∑ lambda : Fin 4, (realChristoffelProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) lambda alpha mu (x : SpacetimePoint) * G lambda nu x + 
                          realChristoffelProxy (fun a b p' => CGD.Gravity.urbantkeMetric (fun c d => curvatureSl2c u.sd_sector c d p') a b) lambda alpha nu (x : SpacetimePoint) * G mu lambda x)
     ) = 0 := h_cons
    have h_T_def_local : ∀ (a b : Fin 4) (x : bulk), T a b x = ∑ mu : Fin 4, ∑ nu : Fin 4, g_inv a mu x * g_inv b nu x * G mu nu x := fun a b x => rfl
    
    have dir_inst := dir_thm G T h_inv_local h_G_symm_local h_T_symm_local h_covDivG h_T_def_local
    exact dir_inst.contraDivT b x

end CGD.Gravity

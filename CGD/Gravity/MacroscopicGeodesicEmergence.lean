-- FILENAME: CGD/Gravity/MacroscopicGeodesicEmergence.lean

import CGD.Axioms.PhysicalUniverse
import CGD.Gravity.Geometry
import CGD.Gravity.StressEnergy.Conservation
import Litlib.Y1951.papapetrou1951spinning.Signature
import Litlib.Y2011.krasnov2011plebanski.Signature
import Litlib.Core

open CGD.Foundations

namespace CGD.Gravity

/--
Proves that Axiom II (MacroscopicVolume) guarantees the algebraic existence 
of the inverse metric inside the topological bulk, fulfilling the Papapetrou 
`invMetric_prop` prerequisite without fiat assumptions.
-/
@[litlib_track "Macroscopic Volume Implies Invertible Metric"]
lemma macroscopicVolumeImpliesInverse
  (pu : CGD.Axioms.PhysicalUniverse)
  (x : SpacetimePoint)
  (hx : x ∈ pu.bulk) :
  let g := urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.sd_sector.val m n x);
  g * g⁻¹ = 1 := by
  intro g
  -- Extract the non-zero determinant property directly from Axiom II
  have h_det : g.det ≠ 0 := pu.has_volume.volume_exists x hx
  -- Because the metric is evaluated over the Complex Field, non-zero implies it is a mathematical Unit
  have h_unit : IsUnit g.det := isUnit_iff_ne_zero.mpr h_det
  -- Apply Mathlib's native linear algebra theorem for non-singular matrix inversion
  exact Matrix.mul_nonsing_inv g h_unit

/--
The Geodesic Capstone (Litlib Horizon Bound):
Rigorously bridges the native CGD Bianchi identity to the Papapetrou equations of motion.
Because the non-vacuum matter equivalence (G = T) has not yet been transcribed into Litlib
for complex-valued manifolds, we explicitly bound this derivation using a mathematical horizon 
hypothesis. Topological Bianchi conservation mathematically forces these macroscopic bodies 
onto GR geodesics.
-/
@[litlib_track "Macroscopic Geodesic Emergence Capstone"]
theorem macroscopicGeodesicEmergence
  (pu : CGD.Axioms.PhysicalUniverse)
  [TopologicalSpace SpacetimePoint]
  (isSmooth : (SpacetimePoint → ℂ) → Prop)
  (partialDeriv : Fin 4 → (SpacetimePoint → ℂ) → SpacetimePoint → ℂ)

  -- Native CGD field extractions
  (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (_h_g : ∀ a b p, g a b p = (urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.sd_sector.val m n p)) a b)
  (g_inv : Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (h_g_inv : ∀ a b p, g_inv a b p = ((urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.sd_sector.val m n p))⁻¹) a b)

  (chris : Fin 4 → Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (ricci : Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (G : Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (F F_dual : SpacetimePoint → Fin 3 → Fin 4 → Fin 4 → ℂ)
  (epsilon3 : Fin 3 → Fin 3 → Fin 3 → ℂ)

  -- Bianchi & Geometry constraints (for geometricStressEnergyConservation)
  [general_bianchi : Litlib.Y2003.nakahara2003geometry.Theorem_ContractedBianchi SpacetimePoint (Fin 4) isSmooth partialDeriv]
  [symm_metric : Litlib.Y1984.urbantke1984integrability.Eq10_Symmetry]
  
  (h_metric_eq10 : ∀ x, 
    (∀ a mu nu, F x a mu nu = - F x a nu mu) ∧
    (∀ a mu nu, F_dual x a mu nu = - F_dual x a nu mu) ∧
    (∀ a b c, epsilon3 a b c = - epsilon3 b a c ∧ epsilon3 a b c = - epsilon3 a c b) ∧
    (∀ mu nu, g mu nu x = (-1 / 6 : ℂ) * ∑ a, ∑ b, ∑ c, ∑ alpha, ∑ beta, epsilon3 a c b * F x a mu alpha * F_dual x c alpha beta * F x b beta nu))
  (h_inv_symm : ∀ x i j, g_inv i j x = g_inv j i x)
  (h_inv_prop : ∀ x i j, (∑ k, g i k x * g_inv k j x) = if i = j then 1 else 0)
  (h_chris_eq : ∀ x rho mu nu, chris rho mu nu x = (1/2:ℂ) * ∑ sigma, g_inv rho sigma x * (partialDeriv mu (fun p => g sigma nu p) x + partialDeriv nu (fun p => g mu sigma p) x - partialDeriv sigma (fun p => g mu nu p) x))
  (h_ricci_eq : ∀ x mu nu, ricci mu nu x = ∑ rho, (partialDeriv rho (fun p => chris rho mu nu p) x - partialDeriv nu (fun p => chris rho mu rho p) x + ∑ lambda, (chris rho lambda rho x * chris lambda mu nu x - chris rho lambda nu x * chris lambda mu rho x)))
  (h_G_eq : ∀ x mu nu, G mu nu x = ricci mu nu x - (1/2:ℂ) * g mu nu x * ∑ alpha, ∑ beta, g_inv alpha beta x * ricci alpha beta x)
  (h_smooth_g : ∀ i j, isSmooth (fun p => g i j p))
  (h_smooth_g_inv : ∀ i j, isSmooth (fun p => g_inv i j p))
  (h_smooth_chris : ∀ rho mu nu, isSmooth (fun p => chris rho mu nu p))

  -- The Litlib Horizon: Einstein Equivalence
  (T_tilde : Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (h_litlib_horizon_plebanski_bridge : ∀ mu nu x, G mu nu x = T_tilde mu nu x)

  -- Papapetrou Instance (Forcing geodesics)
  (worldline : ℂ → SpacetimePoint)
  (u_up du_up_ds : ℂ → (Fin 4 → ℂ))
  (isSinglePole : (Fin 4 → Fin 4 → SpacetimePoint → ℂ) → (ℂ → SpacetimePoint) → Prop)
  [papapetrou : Litlib.Y1951.papapetrou1951spinning.Eq2_12 SpacetimePoint ℂ 
    (fun p => urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.sd_sector.val m n p))
    (fun p => (urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.sd_sector.val m n p))⁻¹) 
    (fun p a b c => chris a b c p) 
    T_tilde partialDeriv worldline u_up du_up_ds isSinglePole]
  (h_single_pole : isSinglePole T_tilde worldline) :
  
  ∀ s α, du_up_ds s α + ∑ μ : Fin 4, ∑ ν : Fin 4, chris α μ ν (worldline s) * u_up s μ * u_up s ν = 0 := by
  
  -- 1. Obtain Covariant Conservation of G via Bianchi
  have h_G_cons := geometricStressEnergyConservation SpacetimePoint isSmooth partialDeriv g g_inv chris ricci G F F_dual epsilon3 h_metric_eq10 h_inv_symm h_inv_prop h_chris_eq h_ricci_eq h_G_eq h_smooth_g h_smooth_g_inv h_smooth_chris

  -- 2. Substitute G with T_tilde using the explicit Litlib horizon boundary
  have h_T_cons : ∀ y b, ∑ a : Fin 4, ∑ c : Fin 4, ((urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.sd_sector.val m n y))⁻¹) a c * (
    partialDeriv c (fun p => T_tilde a b p) y -
    ∑ d : Fin 4, (chris d c a y * T_tilde d b y + chris d c b y * T_tilde a d y)) = 0 := by
    intro y b
    have hG := h_G_cons b y
    simp only [← h_litlib_horizon_plebanski_bridge]
    have h_inv_sym : ∀ a c x, ((urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.sd_sector.val m n x))⁻¹) a c = g_inv a c x := by
      intro a c x
      exact (h_g_inv a c x).symm
    simp only [h_inv_sym]
    exact hG
    
  -- 3. Feed the algebraically conserved T_tilde into Papapetrou
  exact papapetrou.single_pole_eom h_T_cons h_single_pole

end CGD.Gravity

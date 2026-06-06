-- FILENAME: CGD/Gravity/DomainSeparation.lean

import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse
import CGD.Foundations.Spacetime
import CGD.Gravity.Geometry
import CGD.Gravity.Urbantke
import CGD.Gravity.MacroscopicVacuum.Basic
import CGD.Gravity.MacroscopicVacuum.Spinors
import CGD.Gravity.MacroscopicVacuum.Differential
import Litlib.Y1991.capovilla1991pure.Signature
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace CGD.Gravity

open Set Complex Matrix BigOperators CGD.Axioms CGD.Foundations Classical Filter
open Litlib.Y1991.capovilla1991pure

-- ==========================================
-- FUNDAMENTAL DEFINITIONS
-- ==========================================

def isVacuumRegion (region : Set SpacetimePoint) (u : Universe) (Λ : ℂ) : Prop :=
  ∀ x ∈ region, 
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = Λ • 1

def curvature_iso_prop (u : Universe) (region : Set SpacetimePoint) : Prop :=
  ∀ x ∈ region, ∀ μ ν : Fin 4, 
    project (fun m n => curvatureSl2c u.sd_sector m n x) 0 μ ν = cgdAdjointCurvature u μ ν x 1 2 ∧
    project (fun m n => curvatureSl2c u.sd_sector m n x) 1 μ ν = cgdAdjointCurvature u μ ν x 2 0 ∧
    project (fun m n => curvatureSl2c u.sd_sector m n x) 2 μ ν = cgdAdjointCurvature u μ ν x 0 1

-- ==========================================
-- PROVEN ALGEBRAIC LEMMAS
-- ==========================================

/-- 
Representation isomorphism between SL(2,C) and Adjoint SU(2).
-/
lemma curvature_iso_lemma (u : Universe) (region : Set SpacetimePoint) : 
  curvature_iso_prop u region := by
  intro x _ μ ν
  unfold project getPauli cgdAdjointCurvature extractAdjoint
  have h05 : (0.5 : ℂ) = 1 / 2 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · change (0.5 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma1.val) = (1 / 2 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma1.val)
    rw [h05]
  · change (0.5 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma2.val) = (1 / 2 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma2.val)
    rw [h05]
  · change (0.5 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma3.val) = (1 / 2 : ℂ) * Matrix.trace ((curvatureSl2c u.sd_sector μ ν x).val * sigma3.val)
    rw [h05]

lemma cgd_sumFin2_eq_sum (f : Fin 2 → ℂ) :
  CGD.Gravity.sumFin2 f = ∑ x : Fin 2, f x := by
  unfold CGD.Gravity.sumFin2
  rw [Fin.sum_univ_two]

noncomputable def extendMetric (U : Set SpacetimePoint) (g : U → Fin 4 → Fin 4 → ℂ) : Fin 4 → Fin 4 → SpacetimePoint → ℂ :=
  Classical.epsilon (fun (g_ext : Fin 4 → Fin 4 → SpacetimePoint → ℂ) => ∀ y : U, ∀ m n, g_ext m n y.val = g y m n)

lemma extendMetric_spec (U : Set SpacetimePoint) (g : U → Fin 4 → Fin 4 → ℂ) (g_real : Fin 4 → Fin 4 → SpacetimePoint → ℂ) 
  (h : ∀ y : U, ∀ m n, g_real m n y.val = g y m n) : 
  ∀ y : U, ∀ m n, extendMetric U g m n y.val = g y m n := by
  have hex : ∃ (g_ext : Fin 4 → Fin 4 → SpacetimePoint → ℂ), ∀ y : U, ∀ m n, g_ext m n y.val = g y m n := ⟨g_real, h⟩
  exact Classical.epsilon_spec hex

-- ==========================================
-- DIFFERENTIAL GEOMETRY LOCALITY PROOFS
-- ==========================================

lemma partialDeriv_locality (f1 f2 : SpacetimePoint → ℂ) (U : Set SpacetimePoint) (hOpen : IsOpen U) 
  (h_eq : ∀ y ∈ U, f1 y = f2 y) (x : SpacetimePoint) (hx : x ∈ U) (μ : Fin 4) :
  partialDeriv μ f1 x = partialDeriv μ f2 x := by
  have h_eventually : Filter.EventuallyEq (nhds x) f1 f2 := Filter.eventually_of_mem (IsOpen.mem_nhds hOpen hx) h_eq
  have h_fderiv : fderiv ℝ f1 x = fderiv ℝ f2 x := Filter.EventuallyEq.fderiv_eq h_eventually
  unfold partialDeriv
  rw [h_fderiv]

lemma christoffel_locality (g1 g2 : Fin 4 → Fin 4 → SpacetimePoint → ℂ) (U : Set SpacetimePoint) (hOpen : IsOpen U)
  (h_eq : ∀ y ∈ U, ∀ μ ν, g1 μ ν y = g2 μ ν y) (x : SpacetimePoint) (hx : x ∈ U) (ρ μ ν : Fin 4) :
  christoffel g1 ρ μ ν x = christoffel g2 ρ μ ν x := by
  change (1 / 2 : ℂ) * (∑ σ : Fin 4, matrixInv4x4 (fun i j => g1 i j x) ρ σ * (partialDeriv μ (fun p => g1 σ ν p) x + partialDeriv ν (fun p => g1 μ σ p) x - partialDeriv σ (fun p => g1 μ ν p) x)) =
         (1 / 2 : ℂ) * (∑ σ : Fin 4, matrixInv4x4 (fun i j => g2 i j x) ρ σ * (partialDeriv μ (fun p => g2 σ ν p) x + partialDeriv ν (fun p => g2 μ σ p) x - partialDeriv σ (fun p => g2 μ ν p) x))
  have hg_eq : (fun i j => g1 i j x) = (fun i j => g2 i j x) := by
    ext i j
    exact h_eq x hx i j
  have hg_inv_eq : matrixInv4x4 (fun i j => g1 i j x) = matrixInv4x4 (fun i j => g2 i j x) := by rw [hg_eq]
  rw [hg_inv_eq]
  apply congrArg
  apply Finset.sum_congr rfl
  intro σ _
  have hd1 : partialDeriv μ (fun p => g1 σ ν p) x = partialDeriv μ (fun p => g2 σ ν p) x := 
    partialDeriv_locality (fun p => g1 σ ν p) (fun p => g2 σ ν p) U hOpen (fun y hy => h_eq y hy σ ν) x hx μ
  have hd2 : partialDeriv ν (fun p => g1 μ σ p) x = partialDeriv ν (fun p => g2 μ σ p) x := 
    partialDeriv_locality (fun p => g1 μ σ p) (fun p => g2 μ σ p) U hOpen (fun y hy => h_eq y hy μ σ) x hx ν
  have hd3 : partialDeriv σ (fun p => g1 μ ν p) x = partialDeriv σ (fun p => g2 μ ν p) x := 
    partialDeriv_locality (fun p => g1 μ ν p) (fun p => g2 μ ν p) U hOpen (fun y hy => h_eq y hy μ ν) x hx σ
  rw [hd1, hd2, hd3]

/-- 
Locality of the Ricci Tensor. 
In differential geometry, if two metrics are identical on an open subset of the manifold, 
their resulting Ricci curvature tensors evaluate to the exact same values within that subset.
-/
lemma ricci_locality_open (g1 g2 : Fin 4 → Fin 4 → SpacetimePoint → ℂ) (U : Set SpacetimePoint) (hOpen : IsOpen U) :
  (∀ x ∈ U, ∀ μ ν, g1 μ ν x = g2 μ ν x) →
  ∀ x ∈ U, ∀ μ ν, ricciTensor g1 μ ν x = ricciTensor g2 μ ν x := by
  intro h_eq x hx μ ν
  unfold ricciTensor
  apply Finset.sum_congr rfl
  intro ρ _
  have hd1 : partialDeriv ρ (fun p => christoffel g1 ρ μ ν p) x = partialDeriv ρ (fun p => christoffel g2 ρ μ ν p) x :=
    partialDeriv_locality (fun p => christoffel g1 ρ μ ν p) (fun p => christoffel g2 ρ μ ν p) U hOpen
      (fun y hy => christoffel_locality g1 g2 U hOpen h_eq y hy ρ μ ν) x hx ρ
  have hd2 : partialDeriv ν (fun p => christoffel g1 ρ μ ρ p) x = partialDeriv ν (fun p => christoffel g2 ρ μ ρ p) x :=
    partialDeriv_locality (fun p => christoffel g1 ρ μ ρ p) (fun p => christoffel g2 ρ μ ρ p) U hOpen
      (fun y hy => christoffel_locality g1 g2 U hOpen h_eq y hy ρ μ ρ) x hx ν
  rw [hd1, hd2]
  have h_sum : Finset.sum Finset.univ (fun lam : Fin 4 => christoffel g1 ρ lam ρ x * christoffel g1 lam μ ν x - christoffel g1 ρ lam ν x * christoffel g1 lam μ ρ x) =
               Finset.sum Finset.univ (fun lam : Fin 4 => christoffel g2 ρ lam ρ x * christoffel g2 lam μ ν x - christoffel g2 ρ lam ν x * christoffel g2 lam μ ρ x) := by
    apply Finset.sum_congr rfl
    intro lam _
    have hc1 : christoffel g1 ρ lam ρ x = christoffel g2 ρ lam ρ x := christoffel_locality g1 g2 U hOpen h_eq x hx ρ lam ρ
    have hc2 : christoffel g1 lam μ ν x = christoffel g2 lam μ ν x := christoffel_locality g1 g2 U hOpen h_eq x hx lam μ ν
    have hc3 : christoffel g1 ρ lam ν x = christoffel g2 ρ lam ν x := christoffel_locality g1 g2 U hOpen h_eq x hx ρ lam ν
    have hc4 : christoffel g1 lam μ ρ x = christoffel g2 lam μ ρ x := christoffel_locality g1 g2 U hOpen h_eq x hx lam μ ρ
    rw [hc1, hc2, hc3, hc4]
  rw [h_sum]

-- ==========================================
-- MAIN THEOREMS
-- ==========================================

/--
LITERATURE THEOREM: Urbantke (1984) / Capovilla (1991).
The determinant of the Urbantke pseudo-Riemannian metric constructed from an SU(2) 
field strength tensor is uniquely and strictly proportional to the determinant 
of the scalar density matrix Σ^{ab} = ε^{μνρσ} F^a_{μν} F^b_{ρσ}.
-/
class UrbantkeDeterminantTheorem where
  proportionality : ∃ k : ℂ, k ≠ 0 ∧ 
    ∀ (F_adj : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ),
      (cgdUnimodularMetricAdapter F_adj).det = 
      k * (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
        epsilon4 μ ν ρ σ • (F_adj μ ν * F_adj ρ σ)).det

Litlib.theorem
  description "Macroscopic Unimodular Vacuum Emergence"
/--
By treating the bulk vacuum as its own topological subspace, we map the global Unimodular CDJ theorem to the exterior region. This proves that the constant macroscopic volume form emerges strictly independently of the defect core.
-/
theorem macroscopicVacuumEmergence 
  (pu : PhysicalUniverse)
  (Λ : ℂ)
  (h_Λ_neq_zero : Λ ≠ 0)
  [urb_thm : UrbantkeDeterminantTheorem]
  (h_vacuum : isVacuumRegion pu.bulk pu.toUniverse Λ) :
  ∃ (c : ℂ), c ≠ 0 ∧ ∀ x y : pu.bulk, 
    (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature pu.toUniverse m n x.val)).det = (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature pu.toUniverse m n y.val)).det ∧
    (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature pu.toUniverse m n x.val)).det = c := by
  rcases urb_thm.proportionality with ⟨k, hk, h_urbantke_det⟩
  let c := k * (Λ ^ 3)
  use c
  have h_c_neq_zero : c ≠ 0 := by
    apply mul_ne_zero hk
    exact pow_ne_zero 3 h_Λ_neq_zero
  constructor
  · exact h_c_neq_zero
  · intro x y
    have h_det_eval : ∀ z : pu.bulk, (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature pu.toUniverse m n z.val)).det = c := by
      intro z
      have hz := h_urbantke_det (fun m n => cgdAdjointCurvature pu.toUniverse m n z.val)
      have h_vac_z := h_vacuum z.val z.property
      rw [h_vac_z] at hz
      have h_det_smul : (Λ • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det = Λ ^ 3 := by
        rw [Matrix.det_smul]
        have hc : Fintype.card (Fin 3) = 3 := rfl
        rw [hc, Matrix.det_one, mul_one]
      rw [h_det_smul] at hz
      exact hz
    have hx_eval := h_det_eval x
    have hy_eval := h_det_eval y
    constructor
    · rw [hx_eval, hy_eval]
    · exact hx_eval

Litlib.theorem
  description "Macroscopic Ricci-Flat Emergence"
/--
A parallel theorem for the pure GR vacuum limit ($\Lambda = 0$) evaluated on the open bulk manifold subspace outside a topological defect. Because the domain is open, the mapping is mathematically exact for local derivatives.
-/
theorem macroscopicRicciFlatEmergence
  (pu : PhysicalUniverse)
  (urbantke_tetrad : TetradField)
  (metric_compat : ∀ x μ ν, metricFromTetrad urbantke_tetrad μ ν x = 
                           CGD.Gravity.urbantkeMetric (fun m n => curvatureSl2c pu.toUniverse.sd_sector m n x) μ ν)
  (Psi : SpacetimePoint → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ)
  [eq2_2b : Eq2_2b SpacetimePoint (cgd_dSigma urbantke_tetrad) (cgd_omega pu.toUniverse) (cgd_Sigma urbantke_tetrad) cgd_eps2_up]
  [eq2_2c : Eq2_2c SpacetimePoint (cgd_R pu.toUniverse) Psi (cgd_Sigma urbantke_tetrad)]
  [th_ricci : Theorem_Eq2_2c_RicciFlat 
    (Spacetime := pu.bulk)
    (theta := fun (x : pu.bulk) => cgd_theta urbantke_tetrad x.val) 
    (g := fun (x : pu.bulk) m n => metricFromTetrad urbantke_tetrad m n x.val) 
    (eps2_down := cgd_eps2_down)
    (eps2_bar_down := cgd_eps2_bar_down)
    (eps2_right := cgd_eps2_bar_down)
    (eps2_up := cgd_eps2_up)
    (R := fun (x : pu.bulk) => cgd_R pu.toUniverse x.val) 
    (Psi := fun (x : pu.bulk) => Psi x.val) 
    (Sigma := fun (x : pu.bulk) => cgd_Sigma urbantke_tetrad x.val) 
    (dSigma := fun (x : pu.bulk) => cgd_dSigma urbantke_tetrad x.val)
    (omega := fun (x : pu.bulk) => cgd_omega pu.toUniverse x.val)
    (isRicciFlat := fun (g : pu.bulk → Fin 4 → Fin 4 → ℂ) => ∀ (x : pu.bulk) μ ν, CGD.Gravity.ricciTensor (extendMetric pu.bulk g) μ ν x.val = 0)] :
  ∀ x ∈ pu.bulk, ∀ μ ν, ricciTensor (fun m n p => urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p) m n) μ ν x = 0 := by
  intro x hx μ ν
  let x_sub : pu.bulk := ⟨x, hx⟩
  have h_r := th_ricci.eq2_2c_implies_ricci_flat ?h_Sigma_def ?h_DSigma_eq_zero ?h_eq2_2c x_sub μ ν
  
  let g_local : pu.bulk → Fin 4 → Fin 4 → ℂ := fun y m n => metricFromTetrad urbantke_tetrad m n y.val
  
  have h_match : ∀ y : pu.bulk, ∀ m n, metricFromTetrad urbantke_tetrad m n y.val = g_local y m n := by
    intro y m n; rfl

  have h_ext_eq : ∀ y : pu.bulk, ∀ m n, extendMetric pu.bulk g_local m n y.val = g_local y m n :=
    extendMetric_spec pu.bulk g_local (metricFromTetrad urbantke_tetrad) h_match

  have h_metrics_match_on_U : ∀ p ∈ pu.bulk, ∀ m n, metricFromTetrad urbantke_tetrad m n p = extendMetric pu.bulk g_local m n p := by
    intro p hp m n
    let y : pu.bulk := ⟨p, hp⟩
    calc metricFromTetrad urbantke_tetrad m n p = g_local y m n := rfl
      _ = extendMetric pu.bulk g_local m n p := (h_ext_eq y m n).symm

  have h_ricci_match := ricci_locality_open (metricFromTetrad urbantke_tetrad) (extendMetric pu.bulk g_local) pu.bulk pu.has_volume.h_bulk_open h_metrics_match_on_U x hx μ ν

  have h_metric_eq : (fun m n p => metricFromTetrad urbantke_tetrad m n p) = 
                     (fun m n p => urbantkeMetric (fun a b => curvatureSl2c pu.toUniverse.sd_sector a b p) m n) := by
    funext m n p
    exact metric_compat p m n
  
  rw [← h_metric_eq]
  rw [h_ricci_match]
  exact h_r
  
  case h_Sigma_def =>
    intros p m n A B
    unfold cgd_Sigma
    have h_litlib_sum : ∀ f, Litlib.Y1991.capovilla1991pure.sumFin2 f = ∑ x : Fin 2, f x := fun f => rfl
    simp only [cgd_sumFin2_eq_sum, h_litlib_sum]

  case h_DSigma_eq_zero =>
    intros p m n r A B
    exact eq2_2b.eq2_2b_iff p.val m n r A B
    
  case h_eq2_2c =>
    intros p m n A B
    exact eq2_2c.eq2_2c_iff p.val m n A B

end CGD.Gravity

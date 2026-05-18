-- FILENAME: CGD/Gravity/DomainSeparation.lean

import CGD.Axioms.Ontology
import CGD.Foundations.Spacetime
import CGD.Gravity.Geometry
import CGD.Gravity.Urbantke
import CGD.Gravity.MacroscopicVacuum
import CGD.Gravity.MacroscopicVacuum.GR
import Litlib.Y1991.capovilla1991pure.Signature
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

set_option linter.unusedVariables false

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

Litlib.theorem
  description "Macroscopic Unimodular Vacuum Emergence"
/--
By treating the bulk vacuum as its own topological subspace, we map the global Unimodular CDJ theorem to the exterior region. This proves that the constant macroscopic volume form emerges strictly independently of the defect core.
-/
theorem macroscopicVacuumEmergence 
  (u : Universe)
  (Λ : ℂ)
  (bulkVacuum : Set SpacetimePoint)
  (hLambdaNz : Λ ≠ 0)
  (sqrt_g detPsi : SpacetimePoint → ℂ)
  (h_sqrt_g : ∀ x ∈ bulkVacuum, (sqrt_g x)^2 = (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x)).det)
  (h_detPsi : ∀ x ∈ bulkVacuum, detPsi x * ((3 * I / 2 : ℂ)^3 * ((1/2:ℂ) * Λ^3)) = 1)
  (h_eq2_21 : ∀ x ∈ bulkVacuum, (3 * I / 2 : ℂ) * sqrt_g x * detPsi x = 1)
  (h_vacuum : isVacuumRegion bulkVacuum u Λ) :
  ∃ (c : ℂ), c ≠ 0 ∧ ∀ x y : bulkVacuum, 
    (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det = (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n y.val)).det ∧
    (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det = c := by
  obtain ⟨det_val, h_det⟩ := urbantke_det_uniqueness Λ
  by_cases h_emp : Set.Nonempty bulkVacuum
  · rcases h_emp with ⟨x0_val, hx0_mem⟩
    let x0 : bulkVacuum := ⟨x0_val, hx0_mem⟩
    have h_antisymm := adjoint_curvature_antisymm u x0.val
    have h_su2 := adjoint_curvature_su2 u x0.val
    have h_pleb := h_vacuum x0.val x0.property
    have h_eval := h_det (fun m n => cgdAdjointCurvature u m n x0.val) 
      (sqrt_g x0.val) (detPsi x0.val)
      h_antisymm h_su2 h_pleb
      (h_sqrt_g x0.val x0.property)
      (h_detPsi x0.val x0.property)
      (h_eq2_21 x0.val x0.property)
    have h_nz := urbantke_nondeg_of_plebanski Λ (fun m n => cgdAdjointCurvature u m n x0.val) hLambdaNz 
      h_antisymm h_su2 h_pleb
      (sqrt_g x0.val) (detPsi x0.val)
      (h_sqrt_g x0.val x0.property)
      (h_detPsi x0.val x0.property)
      (h_eq2_21 x0.val x0.property)
    use det_val
    refine ⟨?_, ?_⟩
    · rw [← h_eval]
      exact h_nz
    · intro x y
      have hx := h_det (fun m n => cgdAdjointCurvature u m n x.val) 
        (sqrt_g x.val) (detPsi x.val)
        (adjoint_curvature_antisymm u x.val) (adjoint_curvature_su2 u x.val) (h_vacuum x.val x.property)
        (h_sqrt_g x.val x.property) (h_detPsi x.val x.property) (h_eq2_21 x.val x.property)
      have hy := h_det (fun m n => cgdAdjointCurvature u m n y.val) 
        (sqrt_g y.val) (detPsi y.val)
        (adjoint_curvature_antisymm u y.val) (adjoint_curvature_su2 u y.val) (h_vacuum y.val y.property)
        (h_sqrt_g y.val y.property) (h_detPsi y.val y.property) (h_eq2_21 y.val y.property)
      exact ⟨hx.trans hy.symm, hx⟩
  · use 1
    refine ⟨one_ne_zero, ?_⟩
    intro x y
    have h_absurd : x.val ∈ bulkVacuum := x.property
    exfalso
    exact h_emp ⟨x.val, h_absurd⟩

Litlib.theorem
  description "Macroscopic Ricci-Flat Emergence"
/--
A parallel theorem for the pure GR vacuum limit ($\Lambda = 0$) evaluated on the open bulk manifold subspace outside a topological defect. Because the domain is open, the mapping is mathematically exact for local derivatives.
-/
theorem macroscopicRicciFlatEmergence
  (u : Universe)
  (e : TetradField)
  (bulkVacuum : Set SpacetimePoint)
  (hOpen : IsOpen bulkVacuum)
  (theta : SpacetimePoint → Fin 4 → Fin 2 → Fin 2 → ℂ)
  (Sigma : SpacetimePoint → Fin 4 → Fin 4 → Fin 2 → Fin 2 → ℂ)
  (Psi : SpacetimePoint → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ)
  (eps2_down eps2_bar_down : Fin 2 → Fin 2 → ℂ)
  [th_ricci : Theorem_Eq2_2c_RicciFlat 
    bulkVacuum 
    (fun (x : bulkVacuum) => theta x.val) 
    (fun (x : bulkVacuum) m n => metricFromTetrad e m n x.val) 
    eps2_down eps2_bar_down 
    (fun (x : bulkVacuum) => cgd_R u x.val) 
    (fun (x : bulkVacuum) => Psi x.val) 
    (fun (x : bulkVacuum) => Sigma x.val) 
    (fun (g : bulkVacuum → Fin 4 → Fin 4 → ℂ) => ∀ (x : bulkVacuum) μ ν, CGD.Gravity.ricciTensor (extendMetric bulkVacuum g) μ ν x.val = 0)]
  (h_eq2_2c : ∀ x : bulkVacuum, ∀ μ ν A B, cgd_R u x.val μ ν A B = ∑ C, ∑ D, Psi x.val A B C D * Sigma x.val μ ν C D) :
  ∀ x ∈ bulkVacuum, ∀ μ ν, ricciTensor (metricFromTetrad e) μ ν x = 0 := by
  intro x hx μ ν
  let x_sub : bulkVacuum := ⟨x, hx⟩
  have h_r := th_ricci.eq2_2c_implies_ricci_flat h_eq2_2c x_sub μ ν
  
  let g_local : bulkVacuum → Fin 4 → Fin 4 → ℂ := fun y m n => metricFromTetrad e m n y.val
  
  have h_match : ∀ y : bulkVacuum, ∀ m n, metricFromTetrad e m n y.val = g_local y m n := by
    intro y m n; rfl

  have h_ext_eq : ∀ y : bulkVacuum, ∀ m n, extendMetric bulkVacuum g_local m n y.val = g_local y m n :=
    extendMetric_spec bulkVacuum g_local (metricFromTetrad e) h_match

  have h_metrics_match_on_U : ∀ p ∈ bulkVacuum, ∀ m n, metricFromTetrad e m n p = extendMetric bulkVacuum g_local m n p := by
    intro p hp m n
    let y : bulkVacuum := ⟨p, hp⟩
    calc metricFromTetrad e m n p = g_local y m n := rfl
      _ = extendMetric bulkVacuum g_local m n p := (h_ext_eq y m n).symm

  have h_ricci_match := ricci_locality_open (metricFromTetrad e) (extendMetric bulkVacuum g_local) bulkVacuum hOpen h_metrics_match_on_U x hx μ ν

  rw [h_ricci_match]
  exact h_r

end CGD.Gravity

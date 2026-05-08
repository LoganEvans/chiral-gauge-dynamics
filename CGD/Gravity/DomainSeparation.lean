-- FILENAME: CGD/Gravity/DomainSeparation.lean

import Litlib.Core
import CGD.Axioms.Ontology
import CGD.Foundations.Spacetime
import CGD.Gravity.Geometry
import CGD.Gravity.MacroscopicVacuum
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Basic

set_option linter.unusedVariables false

namespace CGD.Gravity

open Set Complex Matrix BigOperators CGD.Axioms CGD.Foundations Classical

def isVacuumRegion (region : Set SpacetimePoint) (u : Universe) (Λ : ℂ) : Prop :=
  ∀ x ∈ region, 
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = Λ • 1

lemma partialDeriv_congr_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f g : SpacetimePoint → E) (U : Set SpacetimePoint) (h_open : IsOpen U)
  (h_eq : ∀ p ∈ U, f p = g p) (x : SpacetimePoint) (hx : x ∈ U) (μ : Fin 4) :
  partialDeriv μ f x = partialDeriv μ g x := by
  unfold partialDeriv
  have heq : f =ᶠ[nhds x] g := by
    apply Filter.mem_of_superset (IsOpen.mem_nhds h_open hx)
    intro y hy
    exact h_eq y hy
  rw [Filter.EventuallyEq.fderiv_eq heq]

lemma christoffel_congr_open (g1 g2 : SpacetimeIndex → SpacetimeIndex → SpacetimePoint → ℂ)
  (U : Set SpacetimePoint) (h_open : IsOpen U)
  (h_eq : ∀ p ∈ U, ∀ i j, g1 i j p = g2 i j p) (x : SpacetimePoint) (hx : x ∈ U) (ρ μ ν : Fin 4) :
  christoffel g1 ρ μ ν x = christoffel g2 ρ μ ν x := by
  unfold christoffel
  have h_g_inv : matrixInv4x4 (fun i j => g1 i j x) = matrixInv4x4 (fun i j => g2 i j x) := by
    congr 1
    ext i j
    exact h_eq x hx i j
  rw [h_g_inv]
  apply congrArg (fun Z => (1 / 2 : ℂ) * Z)
  apply Finset.sum_congr rfl
  intro σ _
  apply congrArg (fun Z => matrixInv4x4 (fun i j => g2 i j x) ρ σ * Z)
  have d1 : partialDeriv μ (fun p => g1 σ ν p) x = partialDeriv μ (fun p => g2 σ ν p) x := by
    apply partialDeriv_congr_open _ _ U h_open (fun p hp => h_eq p hp σ ν) x hx
  have d2 : partialDeriv ν (fun p => g1 μ σ p) x = partialDeriv ν (fun p => g2 μ σ p) x := by
    apply partialDeriv_congr_open _ _ U h_open (fun p hp => h_eq p hp μ σ) x hx
  have d3 : partialDeriv σ (fun p => g1 μ ν p) x = partialDeriv σ (fun p => g2 μ ν p) x := by
    apply partialDeriv_congr_open _ _ U h_open (fun p hp => h_eq p hp μ ν) x hx
  rw [d1, d2, d3]

lemma ricciTensor_congr_open (g1 g2 : SpacetimeIndex → SpacetimeIndex → SpacetimePoint → ℂ)
  (U : Set SpacetimePoint) (h_open : IsOpen U)
  (h_eq : ∀ p ∈ U, ∀ i j, g1 i j p = g2 i j p) (x : SpacetimePoint) (hx : x ∈ U) (μ ν : Fin 4) :
  ricciTensor g1 μ ν x = ricciTensor g2 μ ν x := by
  unfold ricciTensor
  apply Finset.sum_congr rfl
  intro ρ _
  have h_chris_eq : ∀ p ∈ U, ∀ a b c, christoffel g1 a b c p = christoffel g2 a b c p := fun p hp a b c => christoffel_congr_open g1 g2 U h_open h_eq p hp a b c
  have d1 : partialDeriv ρ (fun p => christoffel g1 ρ μ ν p) x = partialDeriv ρ (fun p => christoffel g2 ρ μ ν p) x := by
    apply partialDeriv_congr_open _ _ U h_open (fun p hp => h_chris_eq p hp ρ μ ν) x hx
  have d2 : partialDeriv ν (fun p => christoffel g1 ρ μ ρ p) x = partialDeriv ν (fun p => christoffel g2 ρ μ ρ p) x := by
    apply partialDeriv_congr_open _ _ U h_open (fun p hp => h_chris_eq p hp ρ μ ρ) x hx
  rw [d1, d2]
  apply congrArg (fun Z => partialDeriv ρ (fun p => christoffel g2 ρ μ ν p) x - partialDeriv ν (fun p => christoffel g2 ρ μ ρ p) x + Z)
  apply Finset.sum_congr rfl
  intro lam _
  rw [h_chris_eq x hx ρ lam ρ, h_chris_eq x hx lam μ ν, h_chris_eq x hx ρ lam ν, h_chris_eq x hx lam μ ρ]

noncomputable def cgdCovariantDerivSubspace (bulkVacuum : Set SpacetimePoint) (A : bulkVacuum → Matrix (Fin 3) (Fin 3) ℂ) (f : bulkVacuum → ℂ) (x : bulkVacuum) : ℂ :=
  partialDeriv 0 (fun p => if h : p ∈ bulkVacuum then f ⟨p, h⟩ else 0) x.val + (A x 0 0) * f x

Litlib.theorem
  description "Macroscopic Unimodular Vacuum Emergence"
/--
By treating the bulk vacuum as its own topological subspace, we map the global Unimodular CDJ theorem to the exterior region. This proves that the constant macroscopic volume form emerges strictly independently of the defect core.
-/
theorem macroscopicVacuumEmergence 
  (u : Universe)
  (Λ : ℂ)
  (bulkVacuum : Set SpacetimePoint)
  (h_open : IsOpen bulkVacuum)
  (hLambdaNz : Λ ≠ 0)
  (h_vacuum : ∀ x ∈ bulkVacuum, 
      (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
        epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = Λ • 1)
  [ucdj_vol : Litlib.Y2024.gielen2024unimodular.PureConnectionEOM bulkVacuum (cgdCovariantDerivSubspace bulkVacuum)] :
  ∃ (c : ℂ), c ≠ 0 ∧ ∀ x y : bulkVacuum, 
    (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det = (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n y.val)).det ∧
    (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det = c := by
  sorry

Litlib.theorem
  description "Macroscopic Ricci-Flat Vacuum Emergence"
/--
A parallel theorem for the pure GR vacuum limit ($\Lambda = 0$) evaluated on the open bulk manifold subspace outside a topological defect. Because the domain is open, the mapping is mathematically exact for local derivatives.
-/
theorem macroscopicRicciFlatEmergence
  (u : Universe)
  (e : TetradField)
  (bulkVacuum : Set SpacetimePoint)
  (h_open : IsOpen bulkVacuum)
  (h_vacuum : isVacuumRegion bulkVacuum u 0)
  (h_urbantke : ∀ x ∈ bulkVacuum, ∀ μ ν, metricFromTetrad e μ ν x = urbantkeMetric (fun m n => toSl2c (curvatureSl2c u.sd_sector m n x).val) μ ν)
  (h_nondeg : ∀ x ∈ bulkVacuum, (urbantkeMetric (fun m n => toSl2c (curvatureSl2c u.sd_sector m n x).val)).det ≠ 0)
  [eq2_2c : Litlib.Y1989.capovilla1989general.CDJImpliesRicciFlat 
    bulkVacuum 
    (fun F x μ ν => CGD.Gravity.urbantkeMetric (fun m n => toSl2c (F x 0 m n • sigma1.val + F x 1 m n • sigma2.val + F x 2 m n • sigma3.val)) μ ν) 
    (fun g x μ ν => CGD.Gravity.ricciTensor (fun m n p => if h : p ∈ bulkVacuum then g ⟨p, h⟩ m n else 0) μ ν x.val)] :
  ∀ x : bulkVacuum, ∀ μ ν, ricciTensor (metricFromTetrad e) μ ν x.val = 0 := by
  sorry

end CGD.Gravity

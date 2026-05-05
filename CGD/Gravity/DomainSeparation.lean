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
  [ucdj_vol : Litlib.Y2024.gielen2024unimodular.Eq12 bulkVacuum 
    (fun μ f x => partialDeriv μ (fun p => if h : p ∈ bulkVacuum then f ⟨p, h⟩ else 0) x.val) 
    cgdUnimodularMetricAdapter] :
  ∃ (c : ℂ), c ≠ 0 ∧ ∀ x y : bulkVacuum, 
    (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det = (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n y.val)).det ∧
    (cgdUnimodularMetricAdapter (fun m n => cgdAdjointCurvature u m n x.val)).det = c := by
  
  let F_sub := fun (μ ν : Fin 4) (x : bulkVacuum) => cgdAdjointCurvature u μ ν x.val
  let A_sub := fun (μ : Fin 4) (x : bulkVacuum) => cgdAdjointConnection u μ x.val
  
  have h_anti_sub : ∀ μ ν (x : bulkVacuum), F_sub μ ν x = - F_sub ν μ x := by
    intro μ ν x
    ext i j
    unfold F_sub cgdAdjointCurvature
    simp only [Matrix.neg_apply, Matrix.sub_apply]
    ring
    
  have h_F_sub_def : ∀ μ ν (x : bulkVacuum) i j, F_sub μ ν x i j = 
    partialDeriv μ (fun p => if h : p ∈ bulkVacuum then A_sub ν ⟨p, h⟩ i j else 0) x.val - 
    partialDeriv ν (fun p => if h : p ∈ bulkVacuum then A_sub μ ⟨p, h⟩ i j else 0) x.val + 
    (A_sub μ x * A_sub ν x - A_sub ν x * A_sub μ x) i j := by
    intro μ ν x i j
    have hd1 : partialDeriv μ (fun p => if h : p ∈ bulkVacuum then A_sub ν ⟨p, h⟩ i j else 0) x.val = partialDeriv μ (fun p => cgdAdjointConnection u ν p i j) x.val := by
      apply partialDeriv_congr_open _ _ bulkVacuum h_open
      · intro p hp
        exact dif_pos hp
      · exact x.property
    have hd2 : partialDeriv ν (fun p => if h : p ∈ bulkVacuum then A_sub μ ⟨p, h⟩ i j else 0) x.val = partialDeriv ν (fun p => cgdAdjointConnection u μ p i j) x.val := by
      apply partialDeriv_congr_open _ _ bulkVacuum h_open
      · intro p hp
        exact dif_pos hp
      · exact x.property
    rw [hd1, hd2]
    rfl

  have h_cdj_sub : ∀ (x : bulkVacuum),
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      epsilon4 μ ν ρ σ • (F_sub μ ν x * F_sub ρ σ x)) = Λ • 1 := by
    intro x
    exact h_vacuum x.val x.property
    
  have hEpsilonAlt : ∀ α β γ δ, epsilon4 α β γ δ = -epsilon4 β α γ δ ∧ epsilon4 α β γ δ = -epsilon4 α γ β δ ∧ epsilon4 α β γ δ = -epsilon4 α β δ γ := CGD.Gravity.epsilon4_alt
  
  have hEpsilonNondeg : epsilon4 0 1 2 3 ≠ 0 := by
    rw [CGD.Gravity.epsilon4_0123]
    exact one_ne_zero
    
  have h_vol := ucdj_vol.cdjImpliesConstantVolume A_sub F_sub epsilon4 Λ hEpsilonAlt hEpsilonNondeg h_F_sub_def hLambdaNz h_cdj_sub
  
  rcases h_vol with ⟨c, hc_neq, hc_eq⟩
  use c
  constructor
  · exact hc_neq
  · intro x y
    constructor
    · rw [hc_eq x, hc_eq y]
    · exact hc_eq x

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
  [eq2_2c : Litlib.Y1991.capovilla1991pure.Eq2_2c 
    bulkVacuum 
    (fun μ f x => partialDeriv μ (fun p => if h : p ∈ bulkVacuum then f ⟨p, h⟩ else 0) x.val) 
    (fun F μ ν x => CGD.Gravity.urbantkeMetric (fun m n => toSl2c (F x m n)) μ ν) 
    (fun g μ ν x => CGD.Gravity.matrixInv4x4 (fun m n => g m n x) μ ν)
    (fun g ρ μ ν x => CGD.Gravity.christoffel (fun m n p => if h : p ∈ bulkVacuum then g m n ⟨p, h⟩ else 0) ρ μ ν x.val)
    (fun g μ ν x => CGD.Gravity.ricciTensor (fun m n p => if h : p ∈ bulkVacuum then g m n ⟨p, h⟩ else 0) μ ν x.val)] :
  ∀ x : bulkVacuum, ∀ μ ν, ricciTensor (metricFromTetrad e) μ ν x.val = 0 := by
  intro x μ ν
  
  let F_sub := fun (p : bulkVacuum) (m n : Fin 4) => (curvatureSl2c u.sd_sector m n p.val).val
  let A_sub := fun (p : bulkVacuum) (μ : Fin 4) => (u.sd_sector μ p.val).val
  let F_adj_sub := fun (p : bulkVacuum) (m n : Fin 4) => cgdAdjointCurvature u m n p.val
  
  have hd_A : ∀ α (p : SpacetimePoint) i j, DifferentiableAt ℝ (fun p' => (u.sd_sector α p').val i j) p := by
    intro α p i j
    exact ((u.sd_sector.is_smooth α i j).differentiable (by decide)) p
    
  have h_F_sub_def : ∀ (x : bulkVacuum) μ ν i j, F_sub x μ ν i j = 
    partialDeriv μ (fun p => if h : p ∈ bulkVacuum then A_sub ⟨p, h⟩ ν i j else 0) x.val - 
    partialDeriv ν (fun p => if h : p ∈ bulkVacuum then A_sub ⟨p, h⟩ μ i j else 0) x.val + 
    (A_sub x μ * A_sub x ν - A_sub x ν * A_sub x μ) i j := by
    intro x μ ν i j
    have hd1 : partialDeriv μ (fun p => if h : p ∈ bulkVacuum then A_sub ⟨p, h⟩ ν i j else 0) x.val = partialDeriv μ (fun p => (u.sd_sector ν p).val i j) x.val := by
      apply partialDeriv_congr_open _ _ bulkVacuum h_open
      · intro p hp
        exact dif_pos hp
      · exact x.property
    have hd2 : partialDeriv ν (fun p => if h : p ∈ bulkVacuum then A_sub ⟨p, h⟩ μ i j else 0) x.val = partialDeriv ν (fun p => (u.sd_sector μ p).val i j) x.val := by
      apply partialDeriv_congr_open _ _ bulkVacuum h_open
      · intro p hp
        exact dif_pos hp
      · exact x.property
    rw [hd1, hd2]
    exact curvatureSl2c_val_eq u.sd_sector μ ν x.val (hd_A μ x.val) (hd_A ν x.val) i j

  have hEpsilonAlt : ∀ α β γ δ, epsilon4 α β γ δ = -epsilon4 β α γ δ ∧ epsilon4 α β γ δ = -epsilon4 α γ β δ ∧ epsilon4 α β γ δ = -epsilon4 α β δ γ := CGD.Gravity.epsilon4_alt
  
  have hEpsilonNondeg : epsilon4 0 1 2 3 ≠ 0 := by
    rw [CGD.Gravity.epsilon4_0123]
    exact one_ne_zero
    
  have hNonDeg_sub : ∀ (p : bulkVacuum), Matrix.det (urbantkeMetric (fun m n => toSl2c (F_sub p m n))) ≠ 0 := by
    intro p
    exact h_nondeg p.val p.property
    
  have hPure_sub : ∀ (p : bulkVacuum), (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ • (F_adj_sub p μ ν * F_adj_sub p ρ σ)) = 0 := by
    intro p
    have hv := h_vacuum p.val p.property
    rw [hv]
    exact zero_smul _ _

  have h_axiom_zero := eq2_2c.urbantkeIsRicciFlat A_sub F_sub F_adj_sub epsilon4 hEpsilonAlt hEpsilonNondeg h_F_sub_def hNonDeg_sub hPure_sub x μ ν
  
  let g2 := fun (m n : Fin 4) (p : SpacetimePoint) => if h : p ∈ bulkVacuum then (urbantkeMetric (fun a b => toSl2c (F_sub ⟨p, h⟩ a b)) m n) else 0

  have h_axiom_exact : ricciTensor g2 μ ν x.val = 0 := h_axiom_zero
  
  have h_eq : ∀ p ∈ bulkVacuum, ∀ m n, metricFromTetrad e m n p = g2 m n p := by
    intro p hp m n
    dsimp [g2]
    rw [dif_pos hp]
    exact h_urbantke p hp m n
    
  have h_ricci_eq := ricciTensor_congr_open (metricFromTetrad e) g2 bulkVacuum h_open h_eq x.val x.property μ ν
  
  rw [h_ricci_eq]
  exact h_axiom_exact

end CGD.Gravity

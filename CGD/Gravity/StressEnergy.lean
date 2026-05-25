-- FILENAME: CGD/Gravity/StressEnergy.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Foundations.Calculus
import CGD.Axioms.Ontology
import CGD.Axioms.Phenomenology
import Litlib.Y2003.nakahara2003geometry.Signature

open Complex Matrix CGD.Foundations BigOperators Classical
open CGD.Axioms

namespace CGD.Gravity

instance : Nonempty SpacetimePoint := ⟨fun _ => 0⟩

noncomputable def emergentStressEnergy (F : Fin 4 → Fin 4 → SpacetimePoint → SL2C) (mu nu : Fin 4) (x : SpacetimePoint) : ℂ :=
  let g := fun m n p => CGD.Gravity.urbantkeMetric (fun a b => F a b p) m n
  let g_inv := CGD.Gravity.matrixInv4x4 (fun m n => g m n x)
  let R_mu_nu := CGD.Gravity.ricciTensor g mu nu x
  let R_scalar := ∑ alpha : Fin 4, ∑ beta : Fin 4, g_inv alpha beta * CGD.Gravity.ricciTensor g alpha beta x
  R_mu_nu - (1/2 : ℂ) * g mu nu x * R_scalar

Litlib.theorem
  description "Emergent Stress-Energy Conservation"
/-- 
The emergent Stress-Energy tensor (defined as the Einstein tensor of the dynamically emergent Urbantke metric) is covariantly conserved with respect to its own Levi-Civita connection.
-/
theorem emergentStressEnergyConservation (u : Universe) (bulk : Set SpacetimePoint)
  [Nonempty bulk]
  [_vol : MacroscopicVolume u bulk]
  (isSmooth : (bulk → ℂ) → Prop)
  [general_bianchi : Litlib.Y2003.nakahara2003geometry.Theorem_ContractedBianchi 
    bulk (Fin 4) isSmooth (fun mu f p => partialDeriv mu (fun p' => if _h : p' ∈ bulk then f ⟨p', _h⟩ else 0) p.val)]
  (h_symm : ∀ x : bulk, ∀ i j, CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x.val) i j = CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x.val) j i)
  (h_inv_symm : ∀ x : bulk, ∀ i j, CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x.val) m n) i j = CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x.val) m n) j i)
  (h_chris_eq : ∀ (x : bulk) (rho mu nu : Fin 4), CGD.Gravity.christoffel (fun m n p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n) rho mu nu x.val = (1 / 2 : ℂ) * ∑ sigma : Fin 4, CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x.val) m n) rho sigma * (partialDeriv mu (fun p' => if _h : p' ∈ bulk then CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') sigma nu else 0) x.val + partialDeriv nu (fun p' => if _h : p' ∈ bulk then CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') mu sigma else 0) x.val - partialDeriv sigma (fun p' => if _h : p' ∈ bulk then CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') mu nu else 0) x.val))
  (h_ricci_eq : ∀ (x : bulk) (mu nu : Fin 4), CGD.Gravity.ricciTensor (fun m n p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n) mu nu x.val = ∑ rho : Fin 4, (partialDeriv rho (fun p' => if _h : p' ∈ bulk then CGD.Gravity.christoffel (fun m n p'' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p'') m n) rho mu nu p' else 0) x.val - partialDeriv nu (fun p' => if _h : p' ∈ bulk then CGD.Gravity.christoffel (fun m n p'' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p'') m n) rho mu rho p' else 0) x.val + ∑ lambda : Fin 4, (CGD.Gravity.christoffel (fun m n p'' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p'') m n) rho lambda rho x.val * CGD.Gravity.christoffel (fun m n p'' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p'') m n) lambda mu nu x.val - CGD.Gravity.christoffel (fun m n p'' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p'') m n) rho lambda nu x.val * CGD.Gravity.christoffel (fun m n p'' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p'') m n) lambda mu rho x.val)))
  (h_smooth_g : ∀ i j, isSmooth (fun p : bulk => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) i j))
  (h_smooth_g_inv : ∀ i j, isSmooth (fun p : bulk => CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) m n) i j))
  (h_smooth_chris : ∀ rho mu nu, isSmooth (fun p : bulk => CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) rho mu nu p.val)) :
  ∀ nu (x : bulk),
    let g := fun m n p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n
    let g_inv := CGD.Gravity.matrixInv4x4 (fun m n => g m n x.val)
    let T := fun m n p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') m n p
    -- g^{mu alpha} \nabla_{alpha} T_{mu nu} = 0
    ∑ mu : Fin 4, ∑ alpha : Fin 4, g_inv mu alpha * (
      partialDeriv alpha (fun p => if _h : p ∈ bulk then T mu nu p else 0) x.val -
      ∑ lambda : Fin 4, (CGD.Gravity.christoffel g lambda alpha mu x.val * T lambda nu x.val + 
                         CGD.Gravity.christoffel g lambda alpha nu x.val * T mu lambda x.val)
    ) = 0 := by
  intro nu x

  let g_fn := fun i j (p : bulk) => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) i j
  let g_inv_fn := fun i j (p : bulk) => CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) m n) i j
  let chris_fn := fun rho mu nu (p : bulk) => CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) rho mu nu p.val
  let ricci_fn := fun mu nu (p : bulk) => CGD.Gravity.ricciTensor (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) mu nu p.val
  let scalar_fn := fun (p : bulk) => ∑ alpha : Fin 4, ∑ beta : Fin 4, g_inv_fn alpha beta p * ricci_fn alpha beta p
  let G_fn := fun mu nu (p : bulk) => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') mu nu p.val

  have h_bianchi := general_bianchi.all_metrics_satisfy_bianchi g_fn g_inv_fn chris_fn ricci_fn scalar_fn G_fn
  
  -- Provide premises
  have h_1 : ∀ (p : bulk) (i j : Fin 4), g_fn i j p = g_fn j i p := h_symm
  have h_2 : ∀ (p : bulk) (i j : Fin 4), g_inv_fn i j p = g_inv_fn j i p := h_inv_symm
  have h_3 : ∀ (p : bulk) (i j : Fin 4), (∑ k : Fin 4, g_fn i k p * g_inv_fn k j p) = if i = j then 1 else 0 := by
    intro p i j
    let M : Matrix (Fin 4) (Fin 4) ℂ := fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) m n
    have h_det_neq : M.det ≠ 0 := _vol.volume_exists p.val p.property
    have h_adj : M * M.adjugate = M.det • 1 := Matrix.mul_adjugate M
    have h_sum_adj : ∀ a b, (∑ k, M a k * M.adjugate k b) = M.det * if a = b then 1 else 0 := by
      intro a b
      have h_eq : (M * M.adjugate) a b = (M.det • (1 : Matrix (Fin 4) (Fin 4) ℂ)) a b := by rw [h_adj]
      have h_lhs : (M * M.adjugate) a b = ∑ k, M a k * M.adjugate k b := rfl
      have h_rhs : (M.det • (1 : Matrix (Fin 4) (Fin 4) ℂ)) a b = M.det * if a = b then 1 else 0 := by
        change M.det * (1 : Matrix (Fin 4) (Fin 4) ℂ) a b = _
        rw [Matrix.one_apply]
      rw [h_lhs, h_rhs] at h_eq
      exact h_eq
    
    have h_g_inv : ∀ a b, g_inv_fn a b p = (1 / M.det) * M.adjugate a b := by
      intro a b
      rfl
      
    calc (∑ k, g_fn i k p * g_inv_fn k j p)
      _ = ∑ k, M i k * ((1 / M.det) * M.adjugate k j) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [h_g_inv]
      _ = ∑ k, (1 / M.det) * (M i k * M.adjugate k j) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = (1 / M.det) * ∑ k, M i k * M.adjugate k j := by
        rw [← Finset.mul_sum]
      _ = (1 / M.det) * (M.det * if i = j then 1 else 0) := by
        rw [h_sum_adj]
      _ = ((1 / M.det) * M.det) * if i = j then 1 else 0 := by
        ring
      _ = 1 * if i = j then 1 else 0 := by
        have h_inv : (1 / M.det) * M.det = 1 := by
          have hd : (1 / M.det) * M.det = M.det / M.det := by ring
          rw [hd]
          exact div_self h_det_neq
        rw [h_inv]
      _ = if i = j then 1 else 0 := by
        rw [one_mul]

  have h_4 : ∀ (p : bulk) (rho mu nu : Fin 4), chris_fn rho mu nu p = (1 / 2 : ℂ) * ∑ sigma : Fin 4, g_inv_fn rho sigma p * (
        (fun mu f p => partialDeriv mu (fun p' => if _h : p' ∈ bulk then f ⟨p', _h⟩ else 0) p.val) mu (fun p => g_fn sigma nu p) p +
        (fun mu f p => partialDeriv mu (fun p' => if _h : p' ∈ bulk then f ⟨p', _h⟩ else 0) p.val) nu (fun p => g_fn mu sigma p) p -
        (fun mu f p => partialDeriv mu (fun p' => if _h : p' ∈ bulk then f ⟨p', _h⟩ else 0) p.val) sigma (fun p => g_fn mu nu p) p) := by
    intro p rho mu nu
    exact h_chris_eq p rho mu nu

  have h_5 : ∀ (p : bulk) (mu nu : Fin 4), ricci_fn mu nu p = ∑ rho : Fin 4, (
        (fun mu f p => partialDeriv mu (fun p' => if _h : p' ∈ bulk then f ⟨p', _h⟩ else 0) p.val) rho (fun p => chris_fn rho mu nu p) p -
        (fun mu f p => partialDeriv mu (fun p' => if _h : p' ∈ bulk then f ⟨p', _h⟩ else 0) p.val) nu (fun p => chris_fn rho mu rho p) p + 
        ∑ lambda : Fin 4, (chris_fn rho lambda rho p * chris_fn lambda mu nu p - chris_fn rho lambda nu p * chris_fn lambda mu rho p)) := by
    intro p mu nu
    exact h_ricci_eq p mu nu

  have h_6 : ∀ (p : bulk), scalar_fn p = ∑ alpha : Fin 4, ∑ beta : Fin 4, g_inv_fn alpha beta p * ricci_fn alpha beta p := by
    intro p
    rfl

  have h_7 : ∀ (p : bulk) (mu nu : Fin 4), G_fn mu nu p = ricci_fn mu nu p - (1 / 2 : ℂ) * g_fn mu nu p * scalar_fn p := by
    intro p mu nu
    rfl

  have h_8 : ∀ (i j : Fin 4), isSmooth (fun p => g_fn i j p) := h_smooth_g
  have h_9 : ∀ (i j : Fin 4), isSmooth (fun p => g_inv_fn i j p) := h_smooth_g_inv
  have h_10 : ∀ (rho mu nu : Fin 4), isSmooth (fun p => chris_fn rho mu nu p) := h_smooth_chris

  have h_final := h_bianchi h_1 h_2 h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 nu x
  exact h_final

end CGD.Gravity

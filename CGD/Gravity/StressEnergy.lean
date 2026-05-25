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
  [_vol : CGD.Axioms.MacroscopicVolume u bulk]
  (isSmooth : (bulk → ℂ) → Prop)
  [general_bianchi : Litlib.Y2003.nakahara2003geometry.Theorem_ContractedBianchi 
    bulk (Fin 4) isSmooth (fun mu f p => partialDeriv mu (fun p' => if _h : p' ∈ bulk then f ⟨p', _h⟩ else 0) p.val)]
  (h_symm : ∀ x : bulk, ∀ i j, CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x.val) i j = CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x.val) j i)
  (h_inv_symm : ∀ x : bulk, ∀ i j, CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x.val) m n) i j = CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x.val) m n) j i)
  (h_chris_eq : ∀ x : bulk, ∀ rho mu nu, CGD.Gravity.christoffel (fun m n p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n) rho mu nu x.val = (1/2 : ℂ) * ∑ sigma, CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b x.val) m n) rho sigma * (partialDeriv mu (fun p => if _h : p ∈ bulk then CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) sigma nu else 0) x.val + partialDeriv nu (fun p => if _h : p ∈ bulk then CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) mu sigma else 0) x.val - partialDeriv sigma (fun p => if _h : p ∈ bulk then CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) mu nu else 0) x.val))
  (h_ricci_eq : ∀ x : bulk, ∀ mu nu, CGD.Gravity.ricciTensor (fun m n p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n) mu nu x.val = ∑ rho, (partialDeriv rho (fun p => if _h : p ∈ bulk then CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) rho mu nu p else 0) x.val - partialDeriv nu (fun p => if _h : p ∈ bulk then CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) rho mu rho p else 0) x.val + ∑ lambda, (CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) rho lambda rho x.val * CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) lambda mu nu x.val - CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) rho lambda nu x.val * CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) lambda mu rho x.val)))
  (h_smooth_g : ∀ i j, isSmooth (fun p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) i j))
  (h_smooth_g_inv : ∀ i j, isSmooth (fun p => CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) m n) i j))
  (h_smooth_chris : ∀ rho mu nu, isSmooth (fun p => CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) rho mu nu p.val)) :
  ∀ nu (x : bulk),
    let g_urb := fun m n p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n
    let g_inv := CGD.Gravity.matrixInv4x4 (fun m n => g_urb m n x.val)
    let T := fun m n p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') m n p
    -- g^{mu alpha} \nabla_{alpha} T_{mu nu} = 0
    ∑ mu : Fin 4, ∑ alpha : Fin 4, g_inv mu alpha * (
      partialDeriv alpha (fun p => if _h : p ∈ bulk then T mu nu p else 0) x.val -
      ∑ lambda : Fin 4, (CGD.Gravity.christoffel g_urb lambda alpha mu x.val * T lambda nu x.val + 
                         CGD.Gravity.christoffel g_urb lambda alpha nu x.val * T mu lambda x.val)
    ) = 0 := by
  intro nu x
  let g := fun i j (p : bulk) => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) i j
  let g_inv := fun i j (p : bulk) => CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) m n) i j
  
  -- Rigorously derive invertibility of the metric via macroscopic volume axiom
  have h_inv_prop : ∀ p : bulk, ∀ i j, (∑ k : Fin 4, g i k p * g_inv k j p) = if i = j then 1 else 0 := by
    intro p i j
    let M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of (fun m n => g m n p)
    have h_det : M.det ≠ 0 := _vol.volume_exists p.val p.property
    have h_adj := Matrix.mul_adjugate M
    
    have step1 : (∑ k : Fin 4, g i k p * g_inv k j p) = ∑ k : Fin 4, M i k * ((1 / M.det) * M.adjugate k j) := rfl
    have step2 : ∑ k : Fin 4, M i k * ((1 / M.det) * M.adjugate k j) = (1 / M.det) * (M * M.adjugate) i j := by
      calc ∑ k : Fin 4, M i k * ((1 / M.det) * M.adjugate k j)
        _ = ∑ k : Fin 4, (1 / M.det) * (M i k * M.adjugate k j) := by apply Finset.sum_congr rfl; intro k _; ring
        _ = (1 / M.det) * ∑ k : Fin 4, M i k * M.adjugate k j := by rw [← Finset.mul_sum]
        _ = (1 / M.det) * (M * M.adjugate) i j := rfl
    have step3 : (1 / M.det) * (M * M.adjugate) i j = (1 / M.det) * (M.det • (1 : Matrix (Fin 4) (Fin 4) ℂ)) i j := by rw [h_adj]
    have step4 : (1 / M.det) * (M.det • (1 : Matrix (Fin 4) (Fin 4) ℂ)) i j = ((1 / M.det) * M.det) * (1 : Matrix (Fin 4) (Fin 4) ℂ) i j := by
      have h_eval : (M.det • (1 : Matrix (Fin 4) (Fin 4) ℂ)) i j = M.det * (1 : Matrix (Fin 4) (Fin 4) ℂ) i j := rfl
      rw [h_eval]
      ring
    have step5 : ((1 / M.det) * M.det) * (1 : Matrix (Fin 4) (Fin 4) ℂ) i j = 1 * (1 : Matrix (Fin 4) (Fin 4) ℂ) i j := by
      have h_cancel : (1 / M.det) * M.det = 1 := by
        calc (1 / M.det) * M.det = M.det / M.det := by ring
        _ = 1 := div_self h_det
      rw [h_cancel]
    have step6 : 1 * (1 : Matrix (Fin 4) (Fin 4) ℂ) i j = if i = j then 1 else 0 := by
      calc 1 * (1 : Matrix (Fin 4) (Fin 4) ℂ) i j 
        _ = (1 : Matrix (Fin 4) (Fin 4) ℂ) i j := by ring
        _ = if i = j then 1 else 0 := Matrix.one_apply
      
    rw [step1, step2, step3, step4, step5, step6]

  let chris := fun rho mu nu (p : bulk) => CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) rho mu nu p.val
  let ricci := fun mu nu (p : bulk) => CGD.Gravity.ricciTensor (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) mu nu p.val
  let scalar := fun (p : bulk) => ∑ alpha : Fin 4, ∑ beta : Fin 4, g_inv alpha beta p * ricci alpha beta p
  let G := fun mu nu (p : bulk) => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') mu nu p.val
  
  have h_G_eq : ∀ p mu nu, G mu nu p = ricci mu nu p - (1/2 : ℂ) * g mu nu p * scalar p := fun p mu nu => rfl

  exact general_bianchi.all_metrics_satisfy_bianchi g g_inv chris ricci scalar G h_symm h_inv_symm h_inv_prop h_chris_eq h_ricci_eq (fun p => rfl) h_G_eq h_smooth_g h_smooth_g_inv h_smooth_chris nu x

end CGD.Gravity

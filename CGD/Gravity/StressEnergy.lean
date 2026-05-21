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
  [ebi : Litlib.Y2003.nakahara2003geometry.ContractedBianchiIdentity 
    bulk (Fin 4) 
    (fun i j p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) i j)
    (fun i j p => CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) m n) i j)
    (fun rho mu nu p => CGD.Gravity.christoffel (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) rho mu nu p.val)
    (fun mu nu p => CGD.Gravity.ricciTensor (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) mu nu p.val)
    (fun p => ∑ alpha : Fin 4, ∑ beta : Fin 4, CGD.Gravity.matrixInv4x4 (fun m n => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p.val) m n) alpha beta * CGD.Gravity.ricciTensor (fun m n p' => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p') m n) alpha beta p.val)
    (fun mu nu p => emergentStressEnergy (fun a b p' => curvatureSl2c u.sd_sector a b p') mu nu p.val)
    (fun mu f p => partialDeriv mu (fun p' => if _h : p' ∈ bulk then f ⟨p', _h⟩ else 0) p.val)] :
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
  exact ebi.contractedBianchi nu x

end CGD.Gravity

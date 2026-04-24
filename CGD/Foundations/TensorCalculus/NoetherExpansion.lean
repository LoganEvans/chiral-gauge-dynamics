-- FILENAME: CGD/Foundations/TensorCalculus/NoetherExpansion.lean

import CGD.Foundations.Calculus
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology

set_option linter.unusedVariables false

open Matrix Complex BigOperators CGD.Axioms

namespace CGD.Foundations

/-- 
🔴 NEW SIGNATURE: Emergent Noether Current
Contracts the gauge commutators using the *inverse Urbantke metric*, 
rather than the hardcoded flat `eta` metric.
-/
noncomputable def emergentNoetherCurrent (A : Fin 4 → SpacetimePoint → SL2C) (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ) (alpha : Fin 4) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ beta : Fin 4, ∑ nu : Fin 4, ((CGD.Gravity.matrixInv4x4 (fun m n => g m n x)) alpha beta) • ⁅curvatureSl2c A beta nu x, A nu x⁆.val

/-- 
🔴 NEW SIGNATURE: Covariant Noether Conservation
The rigorous Levi-Civita covariant divergence of the emergent Noether current 
must identically vanish on-shell (when the CDJ constraint is satisfied).
-/
theorem emergentNoetherConservation (u : Universe) 
  (h_cdj : CGD.Gravity.satisfiesCdjConstraint (fun m n p => curvatureSl2c u.sd_sector m n p)) :
  ∀ x, 
    let g := fun m n p => CGD.Gravity.urbantkeMetric (fun a b => curvatureSl2c u.sd_sector a b p) m n
    let J := emergentNoetherCurrent u.sd_sector g
    ∑ mu : Fin 4, (
      partialDerivMat mu (fun p => J mu p) x +
      ∑ lambda : Fin 4, CGD.Gravity.christoffel g mu mu lambda x • J lambda x
    ) = 0 := by
  sorry

end CGD.Foundations

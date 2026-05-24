-- FILENAME: CGD/Gravity/ExactSolutionsPart21.lean

import CGD.Gravity.ExactSolutionsPart20

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma partialDerivMat_exactLorentzian (k mu : Fin 4) (x : SpacetimePoint) :
  partialDerivMat k (fun p => (exactLorentzianField mu p).val) x = L_map mu (Pi.single k 1) := by
  ext i j
  unfold partialDerivMat
  have h_eq : (fun p => (exactLorentzianField mu p).val i j) = (fun p => L_map mu p i j) := by
    ext p; rw [val_exactLorentzianField_eq]
  rw [h_eq]
  exact partialDeriv_L_map mu k x i j

lemma partialDerivSl2c_exactLorentzian_eval (k mu : Fin 4) (x : SpacetimePoint) :
  partialDerivSl2c k (exactLorentzianField mu) x = toSl2c (L_map mu (Pi.single k 1)) := by
  unfold partialDerivSl2c
  rw [partialDerivMat_exactLorentzian]

noncomputable def origin : SpacetimePoint := fun _ => 0

lemma exactLorentzianField_origin_zero (mu : Fin 4) :
  exactLorentzianField mu origin = 0 := by
  apply Subtype.ext
  rw [val_exactLorentzianField_eq mu origin]
  unfold L_map L_1 L_2 L_3 L_0 origin
  split_ifs <;> {
    ext i j
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply]
  }

end CGD.Gravity

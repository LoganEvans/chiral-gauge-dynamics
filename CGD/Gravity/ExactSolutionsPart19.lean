-- FILENAME: CGD/Gravity/ExactSolutionsPart19.lean

import CGD.Gravity.ExactSolutionsPart18

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def L_0 : SpacetimePoint →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ := 0
noncomputable def L_1 : SpacetimePoint →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ := 
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaX)) +
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 3) ((Complex.I / 2) • sigmaY)) -
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 2) ((Complex.I / 2) • sigmaZ))
noncomputable def L_2 : SpacetimePoint →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ := 
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaY)) +
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 1) ((Complex.I / 2) • sigmaZ)) -
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 3) ((Complex.I / 2) • sigmaX))
noncomputable def L_3 : SpacetimePoint →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ := 
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaZ)) +
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 2) ((Complex.I / 2) • sigmaX)) -
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 1) ((Complex.I / 2) • sigmaY))

noncomputable def L_map (mu : Fin 4) : SpacetimePoint →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  if mu = 1 then L_1
  else if mu = 2 then L_2
  else if mu = 3 then L_3
  else L_0

lemma exactLorentzianL_eq_L_map (mu : Fin 4) (p : SpacetimePoint) :
  exactLorentzianL mu p = L_map mu p := by
  unfold exactLorentzianL L_map L_1 L_2 L_3 L_0
  split_ifs <;> {
    ext i j
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply]
  }

end CGD.Gravity

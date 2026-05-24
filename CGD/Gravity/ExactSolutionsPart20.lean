-- FILENAME: CGD/Gravity/ExactSolutionsPart20.lean

import CGD.Gravity.ExactSolutionsPart19

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma exactLorentzianL_trace_zero (mu : Fin 4) (p : SpacetimePoint) :
  Matrix.trace (exactLorentzianL mu p) = 0 := by
  unfold exactLorentzianL
  split_ifs with h1 h2 h3
  · unfold Matrix.trace Matrix.diag sigmaX sigmaY sigmaZ mkMat; simp [Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
  · unfold Matrix.trace Matrix.diag sigmaX sigmaY sigmaZ mkMat; simp [Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
  · unfold Matrix.trace Matrix.diag sigmaX sigmaY sigmaZ mkMat; simp [Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
  · unfold Matrix.trace Matrix.diag; simp [Fin.sum_univ_two]

lemma val_exactLorentzianField_eq (mu : Fin 4) (p : SpacetimePoint) :
  (exactLorentzianField mu p).val = L_map mu p := by
  unfold exactLorentzianField
  have h_tr := exactLorentzianL_trace_zero mu p
  rw [toSl2c_val_eq _ h_tr]
  exact exactLorentzianL_eq_L_map mu p

lemma partialDeriv_cL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : SpacetimePoint →L[ℝ] E) (k : Fin 4) (x : SpacetimePoint) :
  partialDeriv k (fun p => L p) x = L (Pi.single k 1) := by
  unfold partialDeriv
  have h_fderiv : fderiv ℝ L x = L := HasFDerivAt.fderiv (ContinuousLinearMap.hasFDerivAt L)
  rw [h_fderiv]

lemma partialDeriv_L_map (mu k : Fin 4) (x : SpacetimePoint) (i j : Fin 2) :
  partialDeriv k (fun p => L_map mu p i j) x = L_map mu (Pi.single k 1) i j := by
  unfold L_map
  split_ifs with h1 h2 h3
  · let L : SpacetimePoint →L[ℝ] ℂ := 
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaX i j)) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 3) (((Complex.I / 2) • sigmaY) i j)) -
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 2) (((Complex.I / 2) • sigmaZ) i j))
    have h_eq : (fun p => L_1 p i j) = L := by
      ext p; unfold L_1
      have h_L_eval : L p = (p 0 : ℝ) • (-sigmaX i j) + (p 3 : ℝ) • (((Complex.I / 2) • sigmaY) i j) - (p 2 : ℝ) • (((Complex.I / 2) • sigmaZ) i j) := rfl
      rw [h_L_eval]
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
    rw [h_eq]
    exact partialDeriv_cL L k x
  · let L : SpacetimePoint →L[ℝ] ℂ := 
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaY i j)) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 1) (((Complex.I / 2) • sigmaZ) i j)) -
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 3) (((Complex.I / 2) • sigmaX) i j))
    have h_eq : (fun p => L_2 p i j) = L := by
      ext p; unfold L_2
      have h_L_eval : L p = (p 0 : ℝ) • (-sigmaY i j) + (p 1 : ℝ) • (((Complex.I / 2) • sigmaZ) i j) - (p 3 : ℝ) • (((Complex.I / 2) • sigmaX) i j) := rfl
      rw [h_L_eval]
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
    rw [h_eq]
    exact partialDeriv_cL L k x
  · let L : SpacetimePoint →L[ℝ] ℂ := 
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaZ i j)) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 2) (((Complex.I / 2) • sigmaX) i j)) -
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 1) (((Complex.I / 2) • sigmaY) i j))
    have h_eq : (fun p => L_3 p i j) = L := by
      ext p; unfold L_3
      have h_L_eval : L p = (p 0 : ℝ) • (-sigmaZ i j) + (p 2 : ℝ) • (((Complex.I / 2) • sigmaX) i j) - (p 1 : ℝ) • (((Complex.I / 2) • sigmaY) i j) := rfl
      rw [h_L_eval]
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
    rw [h_eq]
    exact partialDeriv_cL L k x
  · let L : SpacetimePoint →L[ℝ] ℂ := 0
    have h_eq : (fun p => L_0 p i j) = L := by
      ext p; unfold L_0; rfl
    rw [h_eq]
    exact partialDeriv_cL L k x

end CGD.Gravity

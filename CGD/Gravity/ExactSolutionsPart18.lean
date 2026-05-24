-- FILENAME: CGD/Gravity/ExactSolutionsPart18.lean

import CGD.Gravity.ExactSolutionsPart17

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma exactLorentzian_smooth (mu : Fin 4) (i j : Fin 2) : ContDiff ℝ ⊤ (fun x : SpacetimePoint => (exactLorentzianField mu x).val i j) := by
  dsimp [exactLorentzianField, exactLorentzianL]
  split_ifs with h1 h2 h3
  · let L : SpacetimePoint →L[ℝ] ℂ := 
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaX i j)) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 3) (((Complex.I / 2) • sigmaY) i j)) -
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 2) (((Complex.I / 2) • sigmaZ) i j))
    have h_eq : (fun x : SpacetimePoint => (toSl2c (- (x 0 : ℝ) • sigmaX + (x 3 : ℝ) • ((Complex.I / 2) • sigmaY) - (x 2 : ℝ) • ((Complex.I / 2) • sigmaZ))).val i j) = L := by
      ext x
      have h_tr : Matrix.trace (- (x 0 : ℝ) • sigmaX + (x 3 : ℝ) • ((Complex.I / 2) • sigmaY) - (x 2 : ℝ) • ((Complex.I / 2) • sigmaZ)) = 0 := by
        unfold Matrix.trace Matrix.diag sigmaX sigmaY sigmaZ mkMat; simp [Fin.sum_univ_two]
      rw [toSl2c_val_eq _ h_tr]
      change (- (x 0 : ℝ) • sigmaX + (x 3 : ℝ) • ((Complex.I / 2) • sigmaY) - (x 2 : ℝ) • ((Complex.I / 2) • sigmaZ)) i j = 
        (x 0 : ℝ) • (-sigmaX i j) + (x 3 : ℝ) • (((Complex.I / 2) • sigmaY) i j) - (x 2 : ℝ) • (((Complex.I / 2) • sigmaZ) i j)
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
    rw [h_eq]
    exact ContinuousLinearMap.contDiff L
  · let L : SpacetimePoint →L[ℝ] ℂ := 
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaY i j)) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 1) (((Complex.I / 2) • sigmaZ) i j)) -
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 3) (((Complex.I / 2) • sigmaX) i j))
    have h_eq : (fun x : SpacetimePoint => (toSl2c (- (x 0 : ℝ) • sigmaY + (x 1 : ℝ) • ((Complex.I / 2) • sigmaZ) - (x 3 : ℝ) • ((Complex.I / 2) • sigmaX))).val i j) = L := by
      ext x
      have h_tr : Matrix.trace (- (x 0 : ℝ) • sigmaY + (x 1 : ℝ) • ((Complex.I / 2) • sigmaZ) - (x 3 : ℝ) • ((Complex.I / 2) • sigmaX)) = 0 := by
        unfold Matrix.trace Matrix.diag sigmaX sigmaY sigmaZ mkMat; simp [Fin.sum_univ_two]
      rw [toSl2c_val_eq _ h_tr]
      change (- (x 0 : ℝ) • sigmaY + (x 1 : ℝ) • ((Complex.I / 2) • sigmaZ) - (x 3 : ℝ) • ((Complex.I / 2) • sigmaX)) i j = 
        (x 0 : ℝ) • (-sigmaY i j) + (x 1 : ℝ) • (((Complex.I / 2) • sigmaZ) i j) - (x 3 : ℝ) • (((Complex.I / 2) • sigmaX) i j)
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
    rw [h_eq]
    exact ContinuousLinearMap.contDiff L
  · let L : SpacetimePoint →L[ℝ] ℂ := 
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaZ i j)) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 2) (((Complex.I / 2) • sigmaX) i j)) -
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 1) (((Complex.I / 2) • sigmaY) i j))
    have h_eq : (fun x : SpacetimePoint => (toSl2c (- (x 0 : ℝ) • sigmaZ + (x 2 : ℝ) • ((Complex.I / 2) • sigmaX) - (x 1 : ℝ) • ((Complex.I / 2) • sigmaY))).val i j) = L := by
      ext x
      have h_tr : Matrix.trace (- (x 0 : ℝ) • sigmaZ + (x 2 : ℝ) • ((Complex.I / 2) • sigmaX) - (x 1 : ℝ) • ((Complex.I / 2) • sigmaY)) = 0 := by
        unfold Matrix.trace Matrix.diag sigmaX sigmaY sigmaZ mkMat; simp [Fin.sum_univ_two]
      rw [toSl2c_val_eq _ h_tr]
      change (- (x 0 : ℝ) • sigmaZ + (x 2 : ℝ) • ((Complex.I / 2) • sigmaX) - (x 1 : ℝ) • ((Complex.I / 2) • sigmaY)) i j = 
        (x 0 : ℝ) • (-sigmaZ i j) + (x 2 : ℝ) • (((Complex.I / 2) • sigmaX) i j) - (x 1 : ℝ) • (((Complex.I / 2) • sigmaY) i j)
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
    rw [h_eq]
    exact ContinuousLinearMap.contDiff L
  · exact contDiff_const

end CGD.Gravity

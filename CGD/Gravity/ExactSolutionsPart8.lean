-- FILENAME: CGD/Gravity/ExactSolutionsPart8.lean

import CGD.Gravity.ExactSolutionsPart7

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma partialDerivSl2c_exactAbelian (c : ℂ) (k l : Fin 4) (x : SpacetimePoint) :
  partialDerivSl2c k (exactAbelianField c l) x = if k = 1 ∧ l = 2 then toSl2c (c • sigmaX) else 0 := by
  unfold exactAbelianField
  by_cases hl : l = 2
  · have h_fun_eq : (fun p : SpacetimePoint => if l = 2 then toSl2c (exactAbelianL c p) else 0) = 
                    (fun p : SpacetimePoint => toSl2c (exactAbelianL c p)) := by
      funext p; rw [if_pos hl]
    rw [h_fun_eq]
    unfold partialDerivSl2c
    have h_val : (fun p => (toSl2c (exactAbelianL c p)).val) = (fun p => exactAbelianL c p) := by
      funext p; exact toSl2c_exactAbelianL c p
    rw [h_val]
    rw [partialDerivMat_exactAbelianL c k x]
    by_cases hk : k = 1
    · have hk1l2 : k = 1 ∧ l = 2 := And.intro hk hl
      rw [if_pos hk, if_pos hk1l2]
    · have hk1l2 : ¬(k = 1 ∧ l = 2) := fun h => hk h.left
      rw [if_neg hk, if_neg hk1l2]
      apply Subtype.ext
      unfold toSl2c
      simp
  · have h_fun_eq : (fun p : SpacetimePoint => if l = 2 then toSl2c (exactAbelianL c p) else 0) = 
                    (fun _ : SpacetimePoint => (0 : SL2C)) := by
      funext p; rw [if_neg hl]
    rw [h_fun_eq]
    have h_false : ¬(k = 1 ∧ l = 2) := fun h => hl h.right
    rw [if_neg h_false]
    unfold partialDerivSl2c partialDerivMat
    apply Subtype.ext
    dsimp
    ext i j
    have hzero : partialDeriv k (fun _ => (0 : ℂ)) x = 0 := partialDeriv_const 0 k x
    rw [hzero]
    unfold toSl2c
    dsimp
    have htr : Matrix.trace (fun (_ _ : Fin 2) => (0 : ℂ)) = 0 := by 
      unfold Matrix.trace Matrix.diag
      simp
    rw [htr]
    simp

end CGD.Gravity

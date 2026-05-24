-- FILENAME: CGD/Gravity/ExactSolutionsPart5.lean

import CGD.Gravity.ExactSolutionsPart4

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

lemma partialDeriv_coord_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] 
  (c_idx : Fin 4) (M : E) (k : Fin 4) (x : SpacetimePoint) :
  partialDeriv k (fun p : SpacetimePoint => p c_idx • M) x = if k = c_idx then M else 0 := by
  unfold partialDeriv
  let F : SpacetimePoint →L[ℝ] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.proj c_idx) M
  have h_eq : (fun p : SpacetimePoint => p c_idx • M) = F := rfl
  rw [h_eq]
  rw [HasFDerivAt.fderiv (ContinuousLinearMap.hasFDerivAt F)]
  have h_eval : F ((Pi.single k (1 : ℝ)) : Fin 4 → ℝ) = ((Pi.single k (1 : ℝ)) : Fin 4 → ℝ) c_idx • M := rfl
  rw [h_eval]
  by_cases hk : k = c_idx
  · rw [hk, Pi.single_eq_same, one_smul, if_pos rfl]
  · have h_neq : k ≠ c_idx := hk
    have h_eval_zero : ((Pi.single k (1 : ℝ)) : Fin 4 → ℝ) c_idx = 0 := by simp [h_neq.symm]
    rw [h_eval_zero, zero_smul, if_neg hk]

end CGD.Gravity

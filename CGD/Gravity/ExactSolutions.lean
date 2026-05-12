-- FILENAME: CGD/Gravity/ExactSolutions.lean

import Litlib.Core
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Axioms.Ontology
import CGD.Gravity.MacroscopicVacuum
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def exactAbelianL (c : ℂ) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  (x 1 : ℝ) • (c • sigmaX)

noncomputable def exactAbelianField (c : ℂ) (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  if mu = 2 then toSl2c (exactAbelianL c x) else 0

noncomputable def curvature_const (c : ℂ) (beta gamma : Fin 4) : SL2C :=
  if beta = 1 ∧ gamma = 2 then toSl2c (c • sigmaX)
  else if beta = 2 ∧ gamma = 1 then toSl2c ((-c) • sigmaX)
  else 0

lemma partialDeriv_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c_val : E) (μ : Fin 4) (x : SpacetimePoint) :
  partialDeriv μ (fun _ => c_val) x = 0 := by
  unfold partialDeriv
  simp [fderiv_const]

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

lemma partialDerivMat_exactAbelianL (c : ℂ) (k : Fin 4) (x : SpacetimePoint) :
  partialDerivMat k (fun p => exactAbelianL c p) x = if k = 1 then c • sigmaX else 0 := by
  ext i j
  unfold partialDerivMat exactAbelianL
  change partialDeriv k (fun p => p 1 • (c • sigmaX) i j) x = (if k = 1 then c • sigmaX else 0) i j
  rw [partialDeriv_coord_smul 1 ((c • sigmaX) i j) k x]
  by_cases hk : k = 1
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk]
    rfl

lemma toSl2c_exactAbelianL (c : ℂ) (p : SpacetimePoint) :
  (toSl2c (exactAbelianL c p)).val = exactAbelianL c p := by
  unfold toSl2c exactAbelianL
  dsimp
  have h_tr : Matrix.trace (p 1 • c • sigmaX) = 0 := by
    unfold Matrix.trace Matrix.diag
    have h_sum : ∑ i : Fin 2, (p 1 • c • sigmaX) i i = (p 1 • c • sigmaX) 0 0 + (p 1 • c • sigmaX) 1 1 := Fin.sum_univ_two _
    rw [h_sum]
    unfold sigmaX mkMat
    change p 1 * (c * 0) + p 1 * (c * 0) = 0
    ring
  rw [h_tr]
  have hz : (0 : ℂ) / 2 = 0 := by ring
  rw [hz, zero_smul, sub_zero]

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

lemma comm_exactAbelian (c : ℂ) (m n : Fin 4) (x : SpacetimePoint) :
  ⁅exactAbelianField c m x, exactAbelianField c n x⁆ = 0 := by
  unfold exactAbelianField
  by_cases hm : m = 2 <;> by_cases hn : n = 2
  · simp [hm, hn]
  · simp [hm, hn]
  · simp [hm, hn]
  · simp [hm, hn]

lemma toSl2c_neg (M : Matrix (Fin 2) (Fin 2) ℂ) : toSl2c (- M) = - toSl2c M := by
  apply Subtype.ext
  unfold toSl2c
  dsimp
  ext i j
  change - M i j - ((Matrix.trace (-M) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) = - (M i j - ((Matrix.trace M / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j))
  unfold Matrix.trace Matrix.diag
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  change - M i j - (((- M 0 0 + - M 1 1) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) = - (M i j - (((M 0 0 + M 1 1) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j))
  ring

lemma curvature_exactAbelian (c : ℂ) (m n : Fin 4) (x : SpacetimePoint) :
  curvatureSl2c (exactAbelianField c) m n x = curvature_const c m n := by
  rw [curvatureSl2c_def]
  rw [comm_exactAbelian c m n x, add_zero]
  rw [partialDerivSl2c_exactAbelian, partialDerivSl2c_exactAbelian]
  unfold curvature_const
  by_cases h1 : m = 1 ∧ n = 2
  · have h2_false : ¬(n = 1 ∧ m = 2) := by
      intro h
      have h_m : (1 : Fin 4) = 2 := Eq.trans h1.left.symm h.right
      revert h_m
      decide
    simp only [if_pos h1, if_neg h2_false, sub_zero]
  · by_cases h2 : m = 2 ∧ n = 1
    · have h2_rev : n = 1 ∧ m = 2 := And.intro h2.right h2.left
      simp only [if_neg h1, if_pos h2, if_pos h2_rev, zero_sub]
      have h_inner : (-c) • sigmaX = - (c • sigmaX) := by
        ext i j
        change (-c) * sigmaX i j = - (c * sigmaX i j)
        ring
      rw [h_inner]
      exact (toSl2c_neg (c • sigmaX)).symm
    · have h2_rev_false : ¬(n = 1 ∧ m = 2) := by
        intro h
        apply h2
        exact And.intro h.right h.left
      simp only [if_neg h1, if_neg h2, if_neg h2_rev_false, sub_zero]

lemma toSl2c_c_sigmaX_smul (c : ℂ) : toSl2c (c • sigmaX) = c • toSl2c sigmaX := by
  apply Subtype.ext
  unfold toSl2c
  dsimp
  ext i j
  have h_tr1 : Matrix.trace (c • sigmaX) = 0 := by
    unfold Matrix.trace Matrix.diag sigmaX mkMat
    simp [Fin.sum_univ_two]
  have h_tr2 : Matrix.trace sigmaX = 0 := by
    unfold Matrix.trace Matrix.diag sigmaX mkMat
    simp [Fin.sum_univ_two]
  rw [h_tr1, h_tr2]
  simp

lemma extractAdjoint_zero : extractAdjoint (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  unfold extractAdjoint
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.trace, Matrix.diag]

lemma sl2c_zero_val : (0 : SL2C).val = 0 := rfl

lemma curvature_const_supp (c : ℂ) (μ ν : Fin 4) :
  curvature_const c μ ν = 0 ∨ (μ = 1 ∧ ν = 2) ∨ (μ = 2 ∧ ν = 1) := by
  unfold curvature_const
  split_ifs with h1 h2
  · right; left; exact h1
  · right; right; exact h2
  · left; rfl

lemma epsilon4_1212 : epsilon4 1 2 1 2 = 0 := by
  unfold epsilon4 epsilon4_int
  exact Int.cast_zero

lemma epsilon4_1221 : epsilon4 1 2 2 1 = 0 := by
  unfold epsilon4 epsilon4_int
  exact Int.cast_zero

lemma epsilon4_2112 : epsilon4 2 1 1 2 = 0 := by
  unfold epsilon4 epsilon4_int
  exact Int.cast_zero

lemma epsilon4_2121 : epsilon4 2 1 2 1 = 0 := by
  unfold epsilon4 epsilon4_int
  exact Int.cast_zero

Litlib.theorem
  description "Exact Abelian Macroscopic Solution"
/--
Provides an exact analytical solution mapping an Abelian plane wave natively into the macroscopic pure CDJ volume constraint.
-/
theorem dynamicExactAbelianSolution (c : ℂ) (hc : c ≠ 0) :
  ∃ (u : Universe), 
    CGD.Gravity.satisfiesPureCdjConstraint (fun p m n => cgdAdjointCurvature u m n p) ∧ 
    (∀ x, curvatureSl2c u.sd_sector 1 2 x = c • toSl2c sigmaX) ∧
    (∃ x, curvatureSl2c u.sd_sector 1 2 x ≠ 0) := by
  have h_smooth_AL : ∀ mu i j, ContDiff ℝ ⊤ (fun x : SpacetimePoint => (exactAbelianField c mu x).val i j) := by
    intro mu i j
    dsimp [exactAbelianField]
    split_ifs with h_mu
    · have h_val : (fun x => (toSl2c (exactAbelianL c x)).val i j) = fun x => x 1 • (c • sigmaX) i j := by
        ext x
        rw [toSl2c_exactAbelianL c x]
        rfl
      rw [h_val]
      let L : SpacetimePoint →L[ℝ] ℂ := ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 1) ((c • sigmaX) i j)
      have h_eq : (fun x : SpacetimePoint => x 1 • (c • sigmaX) i j) = L := rfl
      rw [h_eq]
      exact ContinuousLinearMap.contDiff L
    · exact contDiff_const

  let A_L : Sl2cGaugeField := ⟨exactAbelianField c, h_smooth_AL⟩
  let A_R : Sl2cGaugeField := ⟨fun _ _ => 0, fun _ _ _ => contDiff_const⟩
  let u : Universe := universeEquiv.symm (A_L, A_R)

  have h_sd_val : u.sd_sector.val = A_L.val := by
    have h_u_eq : universeEquiv u = (A_L, A_R) := Equiv.right_inv universeEquiv (A_L, A_R)
    have h_sd : u.sd_sector = A_L := congrArg Prod.fst h_u_eq
    exact congrArg Sl2cGaugeField.val h_sd

  use u

  constructor
  · unfold satisfiesPureCdjConstraint cgdAdjointCurvature
    intro x
    have h_term_zero : ∀ μ ν ρ σ, epsilon4 μ ν ρ σ • (extractAdjoint (curvatureSl2c u.sd_sector μ ν x).val * extractAdjoint (curvatureSl2c u.sd_sector ρ σ x).val) = 0 := by
      intro μ ν ρ σ
      have h_curv_mu : curvatureSl2c u.sd_sector μ ν x = curvature_const c μ ν := by
        have h_sd_curv : curvatureSl2c u.sd_sector μ ν x = curvatureSl2c A_L μ ν x := by
          have h_sec : u.sd_sector = A_L := by
            have h_u_eq : universeEquiv u = (A_L, A_R) := Equiv.right_inv universeEquiv (A_L, A_R)
            exact congrArg Prod.fst h_u_eq
          rw [h_sec]
        rw [h_sd_curv]
        exact curvature_exactAbelian c μ ν x
      have h_curv_rho : curvatureSl2c u.sd_sector ρ σ x = curvature_const c ρ σ := by
        have h_sd_curv : curvatureSl2c u.sd_sector ρ σ x = curvatureSl2c A_L ρ σ x := by
          have h_sec : u.sd_sector = A_L := by
            have h_u_eq : universeEquiv u = (A_L, A_R) := Equiv.right_inv universeEquiv (A_L, A_R)
            exact congrArg Prod.fst h_u_eq
          rw [h_sec]
        rw [h_sd_curv]
        exact curvature_exactAbelian c ρ σ x
      rw [h_curv_mu, h_curv_rho]
      
      have h_supp1 := curvature_const_supp c μ ν
      have h_supp2 := curvature_const_supp c ρ σ
      rcases h_supp1 with h1 | h1
      · rw [h1, sl2c_zero_val, extractAdjoint_zero, Matrix.zero_mul, smul_zero]
      · rcases h_supp2 with h2 | h2
        · rw [h2, sl2c_zero_val, extractAdjoint_zero, Matrix.mul_zero, smul_zero]
        · have h_eps : epsilon4 μ ν ρ σ = 0 := by
            rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact epsilon4_1212
              · exact epsilon4_1221
            · rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact epsilon4_2112
              · exact epsilon4_2121
          rw [h_eps, zero_smul]

    apply Finset.sum_eq_zero; intro μ _
    apply Finset.sum_eq_zero; intro ν _
    apply Finset.sum_eq_zero; intro ρ _
    apply Finset.sum_eq_zero; intro σ _
    exact h_term_zero μ ν ρ σ

  constructor
  · intro x
    have h_sd_curv : curvatureSl2c u.sd_sector 1 2 x = curvatureSl2c A_L 1 2 x := by
      have h_sec : u.sd_sector = A_L := by
        have h_u_eq : universeEquiv u = (A_L, A_R) := Equiv.right_inv universeEquiv (A_L, A_R)
        exact congrArg Prod.fst h_u_eq
      rw [h_sec]
    rw [h_sd_curv, curvature_exactAbelian c 1 2 x]
    unfold curvature_const
    have h_1_eq : (1 : Fin 4) = 1 := rfl
    have h_2_eq : (2 : Fin 4) = 2 := rfl
    simp [h_1_eq, h_2_eq]
    exact toSl2c_c_sigmaX_smul c

  · use (fun _ => 0)
    intro h_zero
    have h_zero_val : (curvatureSl2c u.sd_sector 1 2 (fun _ => 0)).val = (0 : SL2C).val := congrArg Subtype.val h_zero
    have h_sd_curv : curvatureSl2c u.sd_sector 1 2 (fun _ => 0) = curvatureSl2c A_L 1 2 (fun _ => 0) := by
      have h_sec : u.sd_sector = A_L := by
        have h_u_eq : universeEquiv u = (A_L, A_R) := Equiv.right_inv universeEquiv (A_L, A_R)
        exact congrArg Prod.fst h_u_eq
      rw [h_sec]
    have h_curv_val : curvatureSl2c u.sd_sector 1 2 (fun _ => 0) = toSl2c (c • sigmaX) := by
      rw [h_sd_curv, curvature_exactAbelian c 1 2 (fun _ => 0)]
      unfold curvature_const
      have h_1_eq : (1 : Fin 4) = 1 := rfl
      have h_2_eq : (2 : Fin 4) = 2 := rfl
      simp [h_1_eq, h_2_eq]
    rw [h_curv_val] at h_zero_val
    rw [sl2c_zero_val] at h_zero_val
    have h_tr : Matrix.trace (c • sigmaX) = 0 := by
      unfold Matrix.trace Matrix.diag sigmaX mkMat
      simp [Fin.sum_univ_two]
    rw [toSl2c_val_eq _ h_tr] at h_zero_val
    have h_elem : (c • sigmaX) 0 1 = 0 := by rw [h_zero_val]; rfl
    change c * sigmaX 0 1 = 0 at h_elem
    have h_sig01 : sigmaX 0 1 = 1 := rfl
    rw [h_sig01, mul_one] at h_elem
    exact hc h_elem

end CGD.Gravity

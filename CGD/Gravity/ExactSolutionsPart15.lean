-- FILENAME: CGD/Gravity/ExactSolutionsPart15.lean

import CGD.Gravity.ExactSolutionsPart14

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

Litlib.theorem
  description "Exact Abelian Macroscopic Solution"
/--
Provides an exact analytical solution for an Abelian plane wave satisfying the pure CDJ 
constraint equation (F ∧ F = 0).
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
        ext x; rw [toSl2c_exactAbelianL c x]; rfl
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
    exact congrArg Sl2cGaugeField.val (congrArg Prod.fst h_u_eq)

  use u
  constructor
  · unfold satisfiesPureCdjConstraint cgdAdjointCurvature
    intro x
    have h_Sigma_zero : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      epsilon4 μ ν ρ σ • (extractAdjoint (curvatureSl2c u.sd_sector μ ν x).val * extractAdjoint (curvatureSl2c u.sd_sector ρ σ x).val)) = 0 := by
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

    rw [h_Sigma_zero]
    dsimp only
    simp

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
    simp
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
      simp
    rw [h_curv_val] at h_zero_val
    have h_zero_val_2 : (0 : SL2C).val = 0 := rfl
    rw [h_zero_val_2] at h_zero_val
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

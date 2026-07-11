-- FILENAME: CGD/Foundations/Lagrangian/Variation/Bianchi.lean

import CGD.Foundations.Lagrangian.Variation.Algebra
import CGD.Foundations.Lagrangian.Variation.Geometry
import CGD.Foundations.Lagrangian.Variation.Differentiability

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Matrix Complex BigOperators CGD.Axioms CGD.Foundations

namespace CGD.Foundations

lemma mixed_deriv_commute_sd (v : ℝ → PhysicalUniverse) (t : ℝ) (mu nu : Fin 4) (x : SpacetimePoint) (i j : Fin 2)
  (h_valid : isValidPhysicalVariation v) :
  deriv (fun s => partialDeriv nu (fun p => ((v s).toUniverse.sd_sector mu p).val i j) x) t =
  partialDeriv nu (fun p => deriv (fun s => ((v s).toUniverse.sd_sector mu p).val i j) t) x := by
  let f : ℝ × SpacetimePoint → ℂ := fun tx => ((v tx.1).toUniverse.sd_sector mu tx.2).val i j
  have h_smooth : ContDiff ℝ ⊤ f := h_valid.1 mu i j
  exact mixed_deriv_commute f t nu x h_smooth

lemma mixed_deriv_commute_asd (v : ℝ → PhysicalUniverse) (t : ℝ) (mu nu : Fin 4) (x : SpacetimePoint) (i j : Fin 2)
  (h_valid : isValidPhysicalVariation v) :
  deriv (fun s => partialDeriv nu (fun p => ((v s).toUniverse.asd_sector mu p).val i j) x) t =
  partialDeriv nu (fun p => deriv (fun s => ((v s).toUniverse.asd_sector mu p).val i j) t) x := by
  let f : ℝ × SpacetimePoint → ℂ := fun tx => ((v tx.1).toUniverse.asd_sector mu tx.2).val i j
  have h_smooth : ContDiff ℝ ⊤ f := h_valid.2.1 mu i j
  exact mixed_deriv_commute f t nu x h_smooth

lemma partialDerivChiral_eval_sd (μ : Fin 4) (f : SpacetimePoint → ChiralM) (x : SpacetimePoint) (i j : Fin 2)
  (h_diff : ∀ a b, DifferentiableAt ℝ (fun p => (chiralProject (f p)).self_dual.val a b) x) :
  partialDerivChiral μ f x (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) =
  partialDeriv μ (fun p => (chiralProject (f p)).self_dual.val i j) x := by
  rw [partialDerivChiral_eq_embed_proj]
  have h_sd_eval : (embedSelfDual (partialDerivSl2c μ (fun p => (chiralProject (f p)).self_dual) x)) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) =
                   (partialDerivSl2c μ (fun p => (chiralProject (f p)).self_dual) x).val i j := by
    exact embed_self_dual_inl_inl _ i j
  have h_asd_eval : (embedAntiSelfDual (partialDerivSl2c μ (fun p => (chiralProject (f p)).anti_self_dual) x)) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) = 0 := by
    exact embed_anti_self_dual_inl_left _ i _
  change (embedSelfDual (partialDerivSl2c μ (fun p => (chiralProject (f p)).self_dual) x)) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) +
         (embedAntiSelfDual (partialDerivSl2c μ (fun p => (chiralProject (f p)).anti_self_dual) x)) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) = _
  rw [h_sd_eval, h_asd_eval, add_zero]
  have h_mat := partialDerivSl2c_eq_mat (fun p => (chiralProject (f p)).self_dual) μ x h_diff
  exact congr_fun (congr_fun h_mat i) j

lemma partialDerivChiral_eval_asd (μ : Fin 4) (f : SpacetimePoint → ChiralM) (x : SpacetimePoint) (i j : Fin 2)
  (h_diff : ∀ a b, DifferentiableAt ℝ (fun p => (chiralProject (f p)).anti_self_dual.val a b) x) :
  partialDerivChiral μ f x (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) =
  partialDeriv μ (fun p => (chiralProject (f p)).anti_self_dual.val i j) x := by
  rw [partialDerivChiral_eq_embed_proj]
  have h_sd_eval : (embedSelfDual (partialDerivSl2c μ (fun p => (chiralProject (f p)).self_dual) x)) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) = 0 := by
    exact embed_self_dual_inr_left _ i _
  have h_asd_eval : (embedAntiSelfDual (partialDerivSl2c μ (fun p => (chiralProject (f p)).anti_self_dual) x)) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) =
                    (partialDerivSl2c μ (fun p => (chiralProject (f p)).anti_self_dual) x).val i j := by
    exact embed_anti_self_dual_inr_inr _ i j
  change (embedSelfDual (partialDerivSl2c μ (fun p => (chiralProject (f p)).self_dual) x)) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) +
         (embedAntiSelfDual (partialDerivSl2c μ (fun p => (chiralProject (f p)).anti_self_dual) x)) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) = _
  rw [h_sd_eval, h_asd_eval, zero_add]
  have h_mat := partialDerivSl2c_eq_mat (fun p => (chiralProject (f p)).anti_self_dual) μ x h_diff
  exact congr_fun (congr_fun h_mat i) j

lemma trace_bracket_F (dA A F : ChiralM) :
  Matrix.trace ((dA * A - A * dA) * F) = Matrix.trace (dA * (A * F - F * A)) := by
  have h1 : (dA * A - A * dA) * F = (dA * A) * F - (A * dA) * F := Matrix.sub_mul ..
  rw [h1, Matrix.trace_sub]
  have h_assoc1 : (dA * A) * F = dA * (A * F) := Matrix.mul_assoc ..
  have h_assoc2 : (A * dA) * F = A * (dA * F) := Matrix.mul_assoc ..
  rw [h_assoc1, h_assoc2]
  have h2 : dA * (A * F - F * A) = dA * (A * F) - dA * (F * A) := Matrix.mul_sub ..
  rw [h2, Matrix.trace_sub]
  have h_comm : Matrix.trace (A * (dA * F)) = Matrix.trace (dA * (F * A)) := by
    have ht := Matrix.trace_mul_comm A (dA * F)
    rw [ht]
    have hassoc : (dA * F) * A = dA * (F * A) := Matrix.mul_assoc ..
    rw [hassoc]
  rw [h_comm]

lemma trace_bracket_expand (dA_mu A_nu dA_nu A_mu F : ChiralM) :
  Matrix.trace ((dA_mu * A_nu - A_nu * dA_mu + A_mu * dA_nu - dA_nu * A_mu) * F) =
  Matrix.trace (dA_mu * (A_nu * F - F * A_nu)) - Matrix.trace (dA_nu * (A_mu * F - F * A_mu)) := by
  have h1 : (dA_mu * A_nu - A_nu * dA_mu + A_mu * dA_nu - dA_nu * A_mu) =
            (dA_mu * A_nu - A_nu * dA_mu) - (dA_nu * A_mu - A_mu * dA_nu) := by abel
  rw [h1, Matrix.sub_mul, Matrix.trace_sub]
  rw [trace_bracket_F dA_mu A_nu F]
  rw [trace_bracket_F dA_nu A_mu F]

lemma sum_epsilon_trace_swap (dA A : Fin 4 → ChiralM) (F : Fin 4 → Fin 4 → ChiralM) :
  (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * (A mu * F rho sigma - F rho sigma * A mu))) =
  - (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (A nu * F rho sigma - F rho sigma * A nu))) := by
  have h_comm : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * (A mu * F rho sigma - F rho sigma * A mu))) =
    (∑ nu : Fin 4, ∑ mu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * (A mu * F rho sigma - F rho sigma * A mu))) := Finset.sum_comm
  rw [h_comm]
  have h_relabel : (∑ nu : Fin 4, ∑ mu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * (A mu * F rho sigma - F rho sigma * A mu))) =
    (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 nu mu rho sigma * Matrix.trace (dA mu * (A nu * F rho sigma - F rho sigma * A nu))) := by
    apply Finset.sum_congr rfl; intro mu _
    apply Finset.sum_congr rfl; intro nu _
    rfl
  rw [h_relabel]
  have h_neg : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 nu mu rho sigma * Matrix.trace (dA mu * (A nu * F rho sigma - F rho sigma * A nu))) =
    (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    (- CGD.Gravity.epsilon4 mu nu rho sigma) * Matrix.trace (dA mu * (A nu * F rho sigma - F rho sigma * A nu))) := by
    apply Finset.sum_congr rfl; intro mu _
    apply Finset.sum_congr rfl; intro nu _
    apply Finset.sum_congr rfl; intro rho _
    apply Finset.sum_congr rfl; intro sigma _
    rw [epsilon_swap_mu_nu nu mu rho sigma]
  rw [h_neg]
  simp_rw [neg_mul, Finset.sum_neg_distrib]

lemma sum_sub_distrib_4 (f g : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
  (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, (f mu nu rho sigma - g mu nu rho sigma)) =
  (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, f mu nu rho sigma) -
  (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, g mu nu rho sigma) := by
  have h1 : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, (f mu nu rho sigma - g mu nu rho sigma)) =
            ∑ mu : Fin 4, ((∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, f mu nu rho sigma) -
                           (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, g mu nu rho sigma)) := by
    apply Finset.sum_congr rfl; intro mu _
    have h2 : (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, (f mu nu rho sigma - g mu nu rho sigma)) =
              ∑ nu : Fin 4, ((∑ rho : Fin 4, ∑ sigma : Fin 4, f mu nu rho sigma) -
                             (∑ rho : Fin 4, ∑ sigma : Fin 4, g mu nu rho sigma)) := by
      apply Finset.sum_congr rfl; intro nu _
      have h3 : (∑ rho : Fin 4, ∑ sigma : Fin 4, (f mu nu rho sigma - g mu nu rho sigma)) =
                ∑ rho : Fin 4, ((∑ sigma : Fin 4, f mu nu rho sigma) - (∑ sigma : Fin 4, g mu nu rho sigma)) := by
        apply Finset.sum_congr rfl; intro rho _
        exact @Finset.sum_sub_distrib (Fin 4) ℂ _ _ _ _
      rw [h3]
      exact @Finset.sum_sub_distrib (Fin 4) ℂ _ _ _ _
    rw [h2]
    exact @Finset.sum_sub_distrib (Fin 4) ℂ _ _ _ _
  rw [h1]
  exact @Finset.sum_sub_distrib (Fin 4) ℂ _ _ _ _

lemma sum_epsilon_trace_combine (dA A : Fin 4 → ChiralM) (F : Fin 4 → Fin 4 → ChiralM) :
  (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((dA mu * A nu - A nu * dA mu + A mu * dA nu - dA nu * A mu) * F rho sigma)) =
  2 * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (A nu * F rho sigma - F rho sigma * A nu))) := by
  let X := (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (A nu * F rho sigma - F rho sigma * A nu)))
  let Y := (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * (A mu * F rho sigma - F rho sigma * A mu)))

  have h_expand : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((dA mu * A nu - A nu * dA mu + A mu * dA nu - dA nu * A mu) * F rho sigma)) = X - Y := by
    have h1 : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((dA mu * A nu - A nu * dA mu + A mu * dA nu - dA nu * A mu) * F rho sigma)) =
      ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      (CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (A nu * F rho sigma - F rho sigma * A nu)) -
       CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * (A mu * F rho sigma - F rho sigma * A mu))) := by
      apply Finset.sum_congr rfl; intro mu _
      apply Finset.sum_congr rfl; intro nu _
      apply Finset.sum_congr rfl; intro rho _
      apply Finset.sum_congr rfl; intro sigma _
      rw [trace_bracket_expand]
      exact mul_sub _ _ _
    rw [h1]

    have h_sub_1 := sum_sub_distrib_4
      (fun mu nu rho sigma => CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (A nu * F rho sigma - F rho sigma * A nu)))
      (fun mu nu rho sigma => CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * (A mu * F rho sigma - F rho sigma * A mu)))

    exact h_sub_1

  have h_Y : Y = -X := sum_epsilon_trace_swap dA A F
  rw [h_expand, h_Y]
  ring

lemma sum_cyclic_3_eps_F (mu : Fin 4) (F : Fin 4 → Fin 4 → Fin 4 → ChiralM) :
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • F nu rho sigma) =
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • F rho sigma nu) := by
  have h1 := sum_cyclic_3 (fun a b c => CGD.Gravity.epsilon4 mu a b c • F a b c)
  have h_LHS : (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, CGD.Gravity.epsilon4 mu a b c • F a b c) =
               (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • F nu rho sigma) := rfl
  have h_RHS : (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, CGD.Gravity.epsilon4 mu b c a • F b c a) =
               (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu rho sigma nu • F rho sigma nu) := rfl
  rw [h_LHS] at h1
  have h_cyc : (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, (fun a b c => CGD.Gravity.epsilon4 mu a b c • F a b c) b c a) =
               ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, CGD.Gravity.epsilon4 mu b c a • F b c a := rfl
  rw [h_cyc, h_RHS] at h1
  rw [h1]
  apply Finset.sum_congr rfl; intro nu _
  apply Finset.sum_congr rfl; intro rho _
  apply Finset.sum_congr rfl; intro sigma _
  rw [epsilon4_cyclic_shift_2 mu nu rho sigma]

lemma push_sum_into_trace_eps (dA_mu : ChiralM) (mu : Fin 4) (f : Fin 4 → Fin 4 → Fin 4 → ChiralM) :
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA_mu * f nu rho sigma)) =
  Matrix.trace (dA_mu * (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • f nu rho sigma)) := by
  have h_trace_smul : ∀ nu rho sigma, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA_mu * f nu rho sigma) =
                                      Matrix.trace (dA_mu * (CGD.Gravity.epsilon4 mu nu rho sigma • f nu rho sigma)) := by
    intro nu rho sigma
    have h_pull : dA_mu * (CGD.Gravity.epsilon4 mu nu rho sigma • f nu rho sigma) = CGD.Gravity.epsilon4 mu nu rho sigma • (dA_mu * f nu rho sigma) := by
      ext i j
      simp [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h_pull, Matrix.trace_smul]
    exact smul_eq_mul (CGD.Gravity.epsilon4 mu nu rho sigma) (Matrix.trace (dA_mu * f nu rho sigma))

  have h_subst : (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA_mu * f nu rho sigma)) =
                 (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, Matrix.trace (dA_mu * (CGD.Gravity.epsilon4 mu nu rho sigma • f nu rho sigma))) := by
    apply Finset.sum_congr rfl; intro nu _
    apply Finset.sum_congr rfl; intro rho _
    apply Finset.sum_congr rfl; intro sigma _
    exact h_trace_smul nu rho sigma

  rw [h_subst]

  have h_sum1 : (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, Matrix.trace (dA_mu * (CGD.Gravity.epsilon4 mu nu rho sigma • f nu rho sigma))) =
                (∑ nu : Fin 4, Matrix.trace (dA_mu * (∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • f nu rho sigma))) := by
    apply Finset.sum_congr rfl; intro nu _
    have h_sum2 : (∑ rho : Fin 4, ∑ sigma : Fin 4, Matrix.trace (dA_mu * (CGD.Gravity.epsilon4 mu nu rho sigma • f nu rho sigma))) =
                  (∑ rho : Fin 4, Matrix.trace (dA_mu * (∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • f nu rho sigma))) := by
      apply Finset.sum_congr rfl; intro rho _
      rw [← Matrix.trace_sum]
      apply congrArg
      rw [← Matrix.mul_sum]
    rw [h_sum2]
    rw [← Matrix.trace_sum]
    apply congrArg
    rw [← Matrix.mul_sum]

  rw [h_sum1]
  rw [← Matrix.trace_sum]
  apply congrArg
  rw [← Matrix.mul_sum]

lemma bianchi_contraction_zero (u : Universe) (dA : Fin 4 → ChiralM) (x : SpacetimePoint) :
  (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (
      partialDerivChiral nu (fun p => curvature (fun m p' => u.spin4c_connection m p') rho sigma p) x +
      bracket (u.spin4c_connection nu x) (curvature (fun m p => u.spin4c_connection m p) rho sigma x)
    ))) = 0 := by

  have h_sum_trace : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (
      partialDerivChiral nu (fun p => curvature (fun m p' => u.spin4c_connection m p') rho sigma p) x +
      bracket (u.spin4c_connection nu x) (curvature (fun m p => u.spin4c_connection m p) rho sigma x)
    ))) =
    (∑ mu : Fin 4, Matrix.trace (dA mu * (
      ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      CGD.Gravity.epsilon4 mu nu rho sigma • (
        partialDerivChiral nu (fun p => curvature (fun m p' => u.spin4c_connection m p') rho sigma p) x +
        bracket (u.spin4c_connection nu x) (curvature (fun m p => u.spin4c_connection m p) rho sigma x)
      )
    ))) := by
    apply Finset.sum_congr rfl; intro mu _
    exact push_sum_into_trace_eps (dA mu) mu (fun n r s => partialDerivChiral n (fun p => curvature (fun m p' => u.spin4c_connection m p') r s p) x + bracket (u.spin4c_connection n x) (curvature (fun m p => u.spin4c_connection m p) r s x))

  rw [h_sum_trace]

  have h_cyc_apply : ∀ mu, (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      CGD.Gravity.epsilon4 mu nu rho sigma • (
        partialDerivChiral nu (fun p => curvature (fun m p' => u.spin4c_connection m p') rho sigma p) x +
        bracket (u.spin4c_connection nu x) (curvature (fun m p => u.spin4c_connection m p) rho sigma x)
      )) =
      (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      CGD.Gravity.epsilon4 mu nu rho sigma • (
        partialDerivChiral rho (fun p => curvature (fun m p' => u.spin4c_connection m p') sigma nu p) x +
        bracket (u.spin4c_connection rho x) (curvature (fun m p => u.spin4c_connection m p) sigma nu x)
      )) := by
    intro mu
    exact sum_cyclic_3_eps_F mu (fun n r s => partialDerivChiral n (fun p => curvature (fun m p' => u.spin4c_connection m p') r s p) x + bracket (u.spin4c_connection n x) (curvature (fun m p => u.spin4c_connection m p) r s x))

  have h_zero : (∑ mu : Fin 4, Matrix.trace (dA mu * (
      ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      CGD.Gravity.epsilon4 mu nu rho sigma • (
        partialDerivChiral nu (fun p => curvature (fun m p' => u.spin4c_connection m p') rho sigma p) x +
        bracket (u.spin4c_connection nu x) (curvature (fun m p => u.spin4c_connection m p) rho sigma x)
      )
    ))) = 0 := by
    apply Finset.sum_eq_zero
    intro mu _
    rw [h_cyc_apply mu]
    have hb := contracted_bianchi_identity_4x4 u mu x
    rw [hb]
    have hz : dA mu * 0 = 0 := Matrix.mul_zero _
    rw [hz, Matrix.trace_zero]

  exact h_zero

lemma hdA_diff (v : ℝ → PhysicalUniverse) (t : ℝ) (x : SpacetimePoint) (mu nu : Fin 4) (i j : Fin 4)
  (h_valid : isValidPhysicalVariation v) :
  DifferentiableAt ℝ (fun s => partialDerivChiral mu (fun p => (v s).toUniverse.spin4c_connection nu p) x i j) t := by
  exact diff_t_partialDerivChiral v h_valid t x nu mu i j

lemma hcomm_diff (v : ℝ → PhysicalUniverse) (t : ℝ) (x : SpacetimePoint) (mu nu : Fin 4) (i j : Fin 4)
  (h_valid : isValidPhysicalVariation v) :
  DifferentiableAt ℝ (fun s => (embedSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).self_dual +
                                embedAntiSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).anti_self_dual) i j) t := by
  have h_eq : (fun s => (embedSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).self_dual + embedAntiSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).anti_self_dual) i j) =
              fun s => (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x)) i j := by
    ext s
    have hb := chiralProject_bracket_spin4c_sd (v s).toUniverse mu nu x
    have hb2 := chiralProject_bracket_spin4c_asd (v s).toUniverse mu nu x
    have hb3 := bracket_spin4c (v s).toUniverse mu nu x
    rw [hb, hb2, hb3]
  rw [h_eq]
  exact diff_t_bracket v h_valid t x mu nu i j

lemma hF_diff (v : ℝ → PhysicalUniverse) (t : ℝ) (x : SpacetimePoint) (rho sigma : Fin 4) (i j : Fin 4)
  (h_valid : isValidPhysicalVariation v) :
  DifferentiableAt ℝ (fun s => curvature (fun m p => (v s).toUniverse.spin4c_connection m p) rho sigma x i j) t := by
  exact diff_t_curvature v h_valid t x rho sigma i j

lemma hF_diff_spatial (v : ℝ → PhysicalUniverse) (t : ℝ) (x : SpacetimePoint) (rho sigma : Fin 4) (i j : Fin 4)
  (h_valid : isValidPhysicalVariation v) :
  DifferentiableAt ℝ (fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j) x := by
  have hc : (fun p => curvature (fun m p' => (v t).toUniverse.spin4c_connection m p') rho sigma p i j) =
            (fun p => (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p)) i j + (embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j) := by
    ext p
    have h_curv := curvature_spin4c_eq (v t).toUniverse rho sigma p
    exact congr_fun (congr_fun h_curv i) j
  rw [hc]

  have hs_sd : ∀ a c d, ContDiff ℝ ⊤ (fun p => ((v t).toUniverse.sd_sector a p).val c d) := by
    intro a c d
    let c_pt : ℝ × SpacetimePoint := (t, 0)
    let L : SpacetimePoint →L[ℝ] (ℝ × SpacetimePoint) := ContinuousLinearMap.prod (0 : SpacetimePoint →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ SpacetimePoint)
    let g : SpacetimePoint → ℝ × SpacetimePoint := fun p => c_pt + L p
    have hg : ContDiff ℝ ⊤ g := ContDiff.add contDiff_const L.contDiff
    have h_eq : (fun p => ((v t).toUniverse.sd_sector a p).val c d) = (fun tx : ℝ × SpacetimePoint => ((v tx.1).toUniverse.sd_sector a tx.2).val c d) ∘ g := by
      ext p
      have hc1 : (g p).1 = t := by change t + 0 = t; ring
      have hc2 : (g p).2 = p := by change 0 + p = p; simp
      change ((v t).toUniverse.sd_sector a p).val c d = ((v (g p).1).toUniverse.sd_sector a (g p).2).val c d
      rw [hc1, hc2]
    rw [h_eq]
    exact (h_valid.1 a c d).comp hg
  have hd_sd : ∀ a b, DifferentiableAt ℝ (fun p => (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p).val a b) x :=
    diff_curvatureSl2c (v t).toUniverse.sd_sector rho sigma x hs_sd

  have hs_asd : ∀ a c d, ContDiff ℝ ⊤ (fun p => ((v t).toUniverse.asd_sector a p).val c d) := by
    intro a c d
    let c_pt : ℝ × SpacetimePoint := (t, 0)
    let L : SpacetimePoint →L[ℝ] (ℝ × SpacetimePoint) := ContinuousLinearMap.prod (0 : SpacetimePoint →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ SpacetimePoint)
    let g : SpacetimePoint → ℝ × SpacetimePoint := fun p => c_pt + L p
    have hg : ContDiff ℝ ⊤ g := ContDiff.add contDiff_const L.contDiff
    have h_eq : (fun p => ((v t).toUniverse.asd_sector a p).val c d) = (fun tx : ℝ × SpacetimePoint => ((v tx.1).toUniverse.asd_sector a tx.2).val c d) ∘ g := by
      ext p
      have hc1 : (g p).1 = t := by change t + 0 = t; ring
      have hc2 : (g p).2 = p := by change 0 + p = p; simp
      change ((v t).toUniverse.asd_sector a p).val c d = ((v (g p).1).toUniverse.asd_sector a (g p).2).val c d
      rw [hc1, hc2]
    rw [h_eq]
    exact (h_valid.2.1 a c d).comp hg
  have hd_asd : ∀ a b, DifferentiableAt ℝ (fun p => (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p).val a b) x :=
    diff_curvatureSl2c (v t).toUniverse.asd_sector rho sigma x hs_asd

  apply DifferentiableAt.add
  · rcases h_i : chiralIso.symm i with i' | i' <;> rcases h_j : chiralIso.symm j with j' | j'
    · have h_eq : (fun p => (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p)) i j) = (fun p => (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p).val i' j') := by
        ext p; unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [h_eq]; exact hd_sd i' j'
    · have h_eq : (fun p => (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p)) i j) = fun p => 0 := by ext p; unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [h_eq]; exact differentiableAt_const 0
    · have h_eq : (fun p => (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p)) i j) = fun p => 0 := by ext p; unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [h_eq]; exact differentiableAt_const 0
    · have h_eq : (fun p => (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p)) i j) = fun p => 0 := by ext p; unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [h_eq]; exact differentiableAt_const 0
  · rcases h_i : chiralIso.symm i with i' | i' <;> rcases h_j : chiralIso.symm j with j' | j'
    · have h_eq : (fun p => (embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j) = fun p => 0 := by ext p; unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [h_eq]; exact differentiableAt_const 0
    · have h_eq : (fun p => (embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j) = fun p => 0 := by ext p; unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [h_eq]; exact differentiableAt_const 0
    · have h_eq : (fun p => (embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j) = fun p => 0 := by ext p; unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [h_eq]; exact differentiableAt_const 0
    · have h_eq : (fun p => (embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j) = (fun p => (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p).val i' j') := by
        ext p; unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [h_eq]; exact hd_asd i' j'

lemma deriv_chiralProject_sd (v : ℝ → PhysicalUniverse) (h_valid : isValidPhysicalVariation v) (t : ℝ) (mu : Fin 4) (p : SpacetimePoint) (i j : Fin 2) :
  (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual.val i j =
  deriv (fun s => ((v s).toUniverse.sd_sector mu p).val i j) t := by
  have h_conn_eq : ∀ a b, (fun s => (v s).toUniverse.spin4c_connection mu p (chiralIso (Sum.inl a)) (chiralIso (Sum.inl b))) =
                          fun s => ((v s).toUniverse.sd_sector mu p).val a b := by
    intro a b
    ext s
    have hc := spin4c_connection_eq_embed (v s).toUniverse mu p
    have h_apply : (v s).toUniverse.spin4c_connection mu p (chiralIso (Sum.inl a)) (chiralIso (Sum.inl b)) = (embedSelfDual ((v s).toUniverse.sd_sector mu p) + embedAntiSelfDual ((v s).toUniverse.asd_sector mu p)) (chiralIso (Sum.inl a)) (chiralIso (Sum.inl b)) := by rw [hc]
    have h_eval : (embedSelfDual ((v s).toUniverse.sd_sector mu p) + embedAntiSelfDual ((v s).toUniverse.asd_sector mu p)) (chiralIso (Sum.inl a)) (chiralIso (Sum.inl b)) = ((v s).toUniverse.sd_sector mu p).val a b := by
      simp only [Matrix.add_apply, eval_embedSelfDual, eval_embedAntiSelfDual, Equiv.symm_apply_apply, add_zero]
    rw [h_apply, h_eval]

  have h_sd_tr : ∀ s, ((v s).toUniverse.sd_sector mu p).val 0 0 + ((v s).toUniverse.sd_sector mu p).val 1 1 = 0 := by
    intro s
    have h_prop := ((v s).toUniverse.sd_sector mu p).property
    change Matrix.trace ((v s).toUniverse.sd_sector mu p).val = 0 at h_prop
    unfold Matrix.trace Matrix.diag at h_prop
    rw [Fin.sum_univ_two] at h_prop
    exact h_prop

  unfold chiralProject toSl2c
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]

  have h_elem : ∀ x y, Matrix.of (fun a' b' => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a' b') t) (chiralIso (Sum.inl x)) (chiralIso (Sum.inl y)) =
                       deriv (fun s => ((v s).toUniverse.sd_sector mu p).val x y) t := by
    intro x y
    simp only [Matrix.of_apply]
    exact congrArg (fun F => deriv F t) (h_conn_eq x y)

  have h_tr : Matrix.trace (fun x y => Matrix.of (fun a' b' => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a' b') t) (chiralIso (Sum.inl x)) (chiralIso (Sum.inl y))) = 0 := by
    unfold Matrix.trace Matrix.diag
    rw [Fin.sum_univ_two]
    dsimp only
    rw [h_elem 0 0, h_elem 1 1]
    have h_diff_00 := smooth_implies_diff_t _ t p (h_valid.1 mu 0 0)
    have h_diff_11 := smooth_implies_diff_t _ t p (h_valid.1 mu 1 1)
    rw [← deriv_add_inner _ _ t h_diff_00 h_diff_11]
    have h_zero_fun : (fun s => ((v s).toUniverse.sd_sector mu p).val 0 0 + ((v s).toUniverse.sd_sector mu p).val 1 1) = fun s => 0 := by
      ext s
      exact h_sd_tr s
    rw [h_zero_fun]
    simp only [deriv_const]

  change (Matrix.of (fun a' b' => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a' b') t) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j))) -
         (Matrix.trace (fun x y => Matrix.of (fun a' b' => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a' b') t) (chiralIso (Sum.inl x)) (chiralIso (Sum.inl y))) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j =
         deriv (fun s => ((v s).toUniverse.sd_sector mu p).val i j) t
  rw [h_tr]
  simp only [zero_div, zero_mul, sub_zero]
  exact h_elem i j

lemma deriv_chiralProject_asd (v : ℝ → PhysicalUniverse) (h_valid : isValidPhysicalVariation v) (t : ℝ) (mu : Fin 4) (p : SpacetimePoint) (i j : Fin 2) :
  (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual.val i j =
  deriv (fun s => ((v s).toUniverse.asd_sector mu p).val i j) t := by
  have h_conn_eq : ∀ a b, (fun s => (v s).toUniverse.spin4c_connection mu p (chiralIso (Sum.inr a)) (chiralIso (Sum.inr b))) =
                          fun s => ((v s).toUniverse.asd_sector mu p).val a b := by
    intro a b
    ext s
    have hc := spin4c_connection_eq_embed (v s).toUniverse mu p
    have h_apply : (v s).toUniverse.spin4c_connection mu p (chiralIso (Sum.inr a)) (chiralIso (Sum.inr b)) = (embedSelfDual ((v s).toUniverse.sd_sector mu p) + embedAntiSelfDual ((v s).toUniverse.asd_sector mu p)) (chiralIso (Sum.inr a)) (chiralIso (Sum.inr b)) := by rw [hc]
    have h_eval : (embedSelfDual ((v s).toUniverse.sd_sector mu p) + embedAntiSelfDual ((v s).toUniverse.asd_sector mu p)) (chiralIso (Sum.inr a)) (chiralIso (Sum.inr b)) = ((v s).toUniverse.asd_sector mu p).val a b := by
      simp only [Matrix.add_apply, eval_embedSelfDual, eval_embedAntiSelfDual, Equiv.symm_apply_apply, zero_add]
    rw [h_apply, h_eval]

  have h_asd_tr : ∀ s, ((v s).toUniverse.asd_sector mu p).val 0 0 + ((v s).toUniverse.asd_sector mu p).val 1 1 = 0 := by
    intro s
    have h_prop := ((v s).toUniverse.asd_sector mu p).property
    change Matrix.trace ((v s).toUniverse.asd_sector mu p).val = 0 at h_prop
    unfold Matrix.trace Matrix.diag at h_prop
    rw [Fin.sum_univ_two] at h_prop
    exact h_prop

  unfold chiralProject toSl2c
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]

  have h_elem : ∀ x y, Matrix.of (fun a' b' => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a' b') t) (chiralIso (Sum.inr x)) (chiralIso (Sum.inr y)) =
                       deriv (fun s => ((v s).toUniverse.asd_sector mu p).val x y) t := by
    intro x y
    simp only [Matrix.of_apply]
    exact congrArg (fun F => deriv F t) (h_conn_eq x y)

  have h_tr : Matrix.trace (fun x y => Matrix.of (fun a' b' => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a' b') t) (chiralIso (Sum.inr x)) (chiralIso (Sum.inr y))) = 0 := by
    unfold Matrix.trace Matrix.diag
    rw [Fin.sum_univ_two]
    dsimp only
    rw [h_elem 0 0, h_elem 1 1]
    have h_diff_00 := smooth_implies_diff_t _ t p (h_valid.2.1 mu 0 0)
    have h_diff_11 := smooth_implies_diff_t _ t p (h_valid.2.1 mu 1 1)
    rw [← deriv_add_inner _ _ t h_diff_00 h_diff_11]
    have h_zero_fun : (fun s => ((v s).toUniverse.asd_sector mu p).val 0 0 + ((v s).toUniverse.asd_sector mu p).val 1 1) = fun s => 0 := by
      ext s
      exact h_asd_tr s
    rw [h_zero_fun]
    simp only [deriv_const]

  change (Matrix.of (fun a' b' => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a' b') t) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j))) -
         (Matrix.trace (fun x y => Matrix.of (fun a' b' => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a' b') t) (chiralIso (Sum.inr x)) (chiralIso (Sum.inr y))) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j =
         deriv (fun s => ((v s).toUniverse.asd_sector mu p).val i j) t
  rw [h_tr]
  simp only [zero_div, zero_mul, sub_zero]
  exact h_elem i j

lemma hdA_mu_commute (v : ℝ → PhysicalUniverse) (t : ℝ) (x : SpacetimePoint) (mu nu : Fin 4) (i j : Fin 4)
  (h_valid : isValidPhysicalVariation v) :
  deriv (fun s => partialDerivChiral nu (fun p => (v s).toUniverse.spin4c_connection mu p) x i j) t =
  partialDerivChiral nu (fun p => Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t)) x i j := by
  have hLHS : (fun s => partialDerivChiral nu (fun p => (v s).toUniverse.spin4c_connection mu p) x i j) =
    fun s => (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j +
             (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j := by
    ext s
    have hp := partialDerivChiral_eq_embed_proj nu (fun p => (v s).toUniverse.spin4c_connection mu p) x
    simp_rw [chiralProject_spin4c_sd, chiralProject_spin4c_asd] at hp
    exact congr_fun (congr_fun hp i) j

  rw [hLHS]

  have hRHS : partialDerivChiral nu (fun p => Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t)) x i j =
    (embedSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual) x)) i j +
    (embedAntiSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual) x)) i j := rfl

  rw [hRHS]

  rcases h_i : chiralIso.symm i with i' | i' <;> rcases h_j : chiralIso.symm j with j' | j'
  · have h_L1 : ∀ s, (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j = partialDeriv nu (fun p => ((v s).toUniverse.sd_sector mu p).val i' j') x := by
      intro s
      have h_eval_embed : (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j =
                          (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x).val i' j' := by
        unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [h_eval_embed]
      have h_diff_sd : ∀ c d, DifferentiableAt ℝ (fun p => ((v s).toUniverse.sd_sector mu p).val c d) x := by
        intro c d; exact smooth_implies_diff_x _ s x (h_valid.1 mu c d)
      have hm := partialDerivSl2c_eq_mat (fun p => (v s).toUniverse.sd_sector mu p) nu x h_diff_sd
      exact congr_fun (congr_fun hm i') j'

    have h_L2 : ∀ s, (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j = 0 := by
      intro s; unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]

    have h_LHS_eval : deriv (fun s => (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j + (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j) t =
                      deriv (fun s => partialDeriv nu (fun p => ((v s).toUniverse.sd_sector mu p).val i' j') x) t := by
      have h_eq : (fun s => (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j + (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j) =
                  fun s => partialDeriv nu (fun p => ((v s).toUniverse.sd_sector mu p).val i' j') x := by
        ext s; rw [h_L1 s, h_L2 s, add_zero]
      rw [h_eq]

    rw [h_LHS_eval]

    have h_diff_RHS : ∀ c d, DifferentiableAt ℝ (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual.val c d) x := by
      intro c d
      have h_eq : (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual.val c d) =
                  fun p => deriv (fun s => ((v s).toUniverse.sd_sector mu p).val c d) t := by
        ext p
        exact deriv_chiralProject_sd v h_valid t mu p c d
      rw [h_eq]
      exact smooth_implies_diff_x _ t x (deriv_t_smooth _ (h_valid.1 mu c d))

    have h_R1 : (embedSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual) x)) i j =
                partialDeriv nu (fun p => deriv (fun s => ((v s).toUniverse.sd_sector mu p).val i' j') t) x := by
      have h_eval_embed : (embedSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual) x)) i j =
                          (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual) x).val i' j' := by
        unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [h_eval_embed]
      have hm := partialDerivSl2c_eq_mat _ nu x h_diff_RHS
      have heval := congr_fun (congr_fun hm i') j'
      rw [heval]
      change partialDeriv nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual.val i' j') x = _
      have h_fun_eq : (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual.val i' j') =
                      (fun p => deriv (fun s => ((v s).toUniverse.sd_sector mu p).val i' j') t) := by
        ext p
        exact deriv_chiralProject_sd v h_valid t mu p i' j'
      rw [h_fun_eq]

    have h_R2 : (embedAntiSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual) x)) i j = 0 := by
      unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]

    rw [h_R1, h_R2, add_zero]
    exact mixed_deriv_commute_sd v t mu nu x i' j' h_valid

  · have h_LHS_zero : deriv (fun s => (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j + (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j) t = 0 := by
      have h_eq : (fun s => (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j + (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j) = fun s => 0 := by
        ext s
        have hs1 : (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j = 0 := by unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
        have hs2 : (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j = 0 := by unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
        rw [hs1, hs2, add_zero]
      rw [h_eq]; simp only [deriv_const]
    rw [h_LHS_zero]

    have h_RHS_zero : (embedSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual) x)) i j +
                      (embedAntiSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual) x)) i j = 0 := by
      have hr1 : (embedSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual) x)) i j = 0 := by unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      have hr2 : (embedAntiSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual) x)) i j = 0 := by unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [hr1, hr2, add_zero]
    rw [h_RHS_zero]

  · have h_LHS_zero : deriv (fun s => (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j + (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j) t = 0 := by
      have h_eq : (fun s => (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j + (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j) = fun s => 0 := by
        ext s
        have hs1 : (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j = 0 := by unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
        have hs2 : (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j = 0 := by unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
        rw [hs1, hs2, zero_add]
      rw [h_eq]; simp only [deriv_const]
    rw [h_LHS_zero]

    have h_RHS_zero : (embedSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual) x)) i j +
                      (embedAntiSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual) x)) i j = 0 := by
      have hr1 : (embedSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual) x)) i j = 0 := by unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      have hr2 : (embedAntiSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual) x)) i j = 0 := by unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [hr1, hr2, zero_add]
    rw [h_RHS_zero]

  · have h_L1 : ∀ s, (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j = 0 := by
      intro s; unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    have h_L2 : ∀ s, (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j = partialDeriv nu (fun p => ((v s).toUniverse.asd_sector mu p).val i' j') x := by
      intro s
      have h_eval_embed : (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j =
                          (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x).val i' j' := by
        unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [h_eval_embed]
      have h_diff_asd : ∀ c d, DifferentiableAt ℝ (fun p => ((v s).toUniverse.asd_sector mu p).val c d) x := by
        intro c d; exact smooth_implies_diff_x _ s x (h_valid.2.1 mu c d)
      have hm := partialDerivSl2c_eq_mat (fun p => (v s).toUniverse.asd_sector mu p) nu x h_diff_asd
      exact congr_fun (congr_fun hm i') j'

    have h_LHS_eval : deriv (fun s => (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j + (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j) t =
                      deriv (fun s => partialDeriv nu (fun p => ((v s).toUniverse.asd_sector mu p).val i' j') x) t := by
      have h_eq : (fun s => (embedSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.sd_sector mu p) x)) i j + (embedAntiSelfDual (partialDerivSl2c nu (fun p => (v s).toUniverse.asd_sector mu p) x)) i j) =
                  fun s => partialDeriv nu (fun p => ((v s).toUniverse.asd_sector mu p).val i' j') x := by
        ext s; rw [h_L1 s, h_L2 s, zero_add]
      rw [h_eq]

    rw [h_LHS_eval]

    have h_diff_RHS : ∀ c d, DifferentiableAt ℝ (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual.val c d) x := by
      intro c d
      have h_eq : (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual.val c d) =
                  fun p => deriv (fun s => ((v s).toUniverse.asd_sector mu p).val c d) t := by
        ext p
        exact deriv_chiralProject_asd v h_valid t mu p c d
      rw [h_eq]
      exact smooth_implies_diff_x _ t x (deriv_t_smooth _ (h_valid.2.1 mu c d))

    have h_R1 : (embedSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).self_dual) x)) i j = 0 := by
      unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]

    have h_R2 : (embedAntiSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual) x)) i j =
                partialDeriv nu (fun p => deriv (fun s => ((v s).toUniverse.asd_sector mu p).val i' j') t) x := by
      have h_eval_embed : (embedAntiSelfDual (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual) x)) i j =
                          (partialDerivSl2c nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual) x).val i' j' := by
        unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
      rw [h_eval_embed]
      have hm := partialDerivSl2c_eq_mat _ nu x h_diff_RHS
      have heval := congr_fun (congr_fun hm i') j'
      rw [heval]
      change partialDeriv nu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual.val i' j') x = _
      have h_fun_eq : (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t))).anti_self_dual.val i' j') =
                      (fun p => deriv (fun s => ((v s).toUniverse.asd_sector mu p).val i' j') t) := by
        ext p
        exact deriv_chiralProject_asd v h_valid t mu p i' j'
      rw [h_fun_eq]

    rw [h_R1, h_R2, zero_add]
    exact mixed_deriv_commute_asd v t mu nu x i' j' h_valid

lemma partialDerivChiral_matrix_of_deriv (v : ℝ → PhysicalUniverse) (h_valid : isValidPhysicalVariation v) (t : ℝ) (mu nu : Fin 4) (x : SpacetimePoint) :
  partialDerivChiral mu (fun p => Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t)) x =
  Matrix.of (fun i j => partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t) x) := by
  ext i j
  have hc : partialDerivChiral mu (fun p => Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t)) x i j =
            (embedSelfDual (partialDerivSl2c mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).self_dual) x)) i j +
            (embedAntiSelfDual (partialDerivSl2c mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).anti_self_dual) x)) i j := rfl
  rw [hc]
  rcases h_i : chiralIso.symm i with i' | i' <;> rcases h_j : chiralIso.symm j with j' | j'
  · have hr1 : (embedSelfDual (partialDerivSl2c mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).self_dual) x)) i j =
               (partialDerivSl2c mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).self_dual) x).val i' j' := by
      unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    rw [hr1]

    have h_diff_sd : ∀ c d, DifferentiableAt ℝ (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).self_dual.val c d) x := by
      intro c d
      have heq : (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).self_dual.val c d) =
                 fun p => deriv (fun s => ((v s).toUniverse.sd_sector nu p).val c d) t := by
        ext p; exact deriv_chiralProject_sd v h_valid t nu p c d
      rw [heq]
      exact smooth_implies_diff_x _ t x (deriv_t_smooth _ (h_valid.1 nu c d))

    have hm := partialDerivSl2c_eq_mat _ mu x h_diff_sd
    have heval := congr_fun (congr_fun hm i') j'
    rw [heval]

    have hr2 : (embedAntiSelfDual (partialDerivSl2c mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).anti_self_dual) x)) i j = 0 := by
      unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    rw [hr2, add_zero]

    have heq2 : (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).self_dual.val i' j') =
                fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t := by
      ext p
      have hc2 := deriv_chiralProject_sd v h_valid t nu p i' j'
      rw [hc2]
      have h_conn_eq : (fun s => (v s).toUniverse.spin4c_connection nu p i j) = fun s => ((v s).toUniverse.sd_sector nu p).val i' j' := by
        ext s
        have hs : (v s).toUniverse.spin4c_connection nu p i j = (embedSelfDual ((v s).toUniverse.sd_sector nu p) + embedAntiSelfDual ((v s).toUniverse.asd_sector nu p)) i j := by rw [spin4c_connection_eq_embed]
        rw [hs]
        simp only [Matrix.add_apply, eval_embedSelfDual, eval_embedAntiSelfDual, Equiv.symm_apply_apply, add_zero]
        rw [h_i, h_j]
        dsimp only
        ring
      rw [h_conn_eq]

    change partialDeriv mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).self_dual.val i' j') x =
           partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t) x
    exact congrArg (fun F => partialDeriv mu F x) heq2

  · have h1 : (embedSelfDual (partialDerivSl2c mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).self_dual) x)) i j = 0 := by
      unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    have h2 : (embedAntiSelfDual (partialDerivSl2c mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).anti_self_dual) x)) i j = 0 := by
      unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    rw [h1, h2, add_zero]
    change 0 = partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t) x
    have h_zero : (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t) = fun p => (0 : ℂ) := by
      ext p
      have h_conn_eq : (fun s => (v s).toUniverse.spin4c_connection nu p i j) = fun s => 0 := by
        ext s
        have hs : (v s).toUniverse.spin4c_connection nu p i j = (embedSelfDual ((v s).toUniverse.sd_sector nu p) + embedAntiSelfDual ((v s).toUniverse.asd_sector nu p)) i j := by rw [spin4c_connection_eq_embed]
        rw [hs]
        simp only [Matrix.add_apply, eval_embedSelfDual, eval_embedAntiSelfDual, Equiv.symm_apply_apply]
        rw [h_i, h_j]; ring
      rw [h_conn_eq]; simp only [deriv_const]
    rw [h_zero]; exact (partialDeriv_const (0 : ℂ) mu x).symm

  · have h1 : (embedSelfDual (partialDerivSl2c mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).self_dual) x)) i j = 0 := by
      unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    have h2 : (embedAntiSelfDual (partialDerivSl2c mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).anti_self_dual) x)) i j = 0 := by
      unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    rw [h1, h2, zero_add]
    change 0 = partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t) x
    have h_zero : (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t) = fun p => (0 : ℂ) := by
      ext p
      have h_conn_eq : (fun s => (v s).toUniverse.spin4c_connection nu p i j) = fun s => 0 := by
        ext s
        have hs : (v s).toUniverse.spin4c_connection nu p i j = (embedSelfDual ((v s).toUniverse.sd_sector nu p) + embedAntiSelfDual ((v s).toUniverse.asd_sector nu p)) i j := by rw [spin4c_connection_eq_embed]
        rw [hs]
        simp only [Matrix.add_apply, eval_embedSelfDual, eval_embedAntiSelfDual, Equiv.symm_apply_apply]
        rw [h_i, h_j]; ring
      rw [h_conn_eq]; simp only [deriv_const]
    rw [h_zero]; exact (partialDeriv_const (0 : ℂ) mu x).symm

  · have hr1 : (embedSelfDual (partialDerivSl2c mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).self_dual) x)) i j = 0 := by
      unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    rw [hr1, zero_add]

    have hr2 : (embedAntiSelfDual (partialDerivSl2c mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).anti_self_dual) x)) i j =
               (partialDerivSl2c mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).anti_self_dual) x).val i' j' := by
      unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    rw [hr2]

    have h_diff_asd : ∀ c d, DifferentiableAt ℝ (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).anti_self_dual.val c d) x := by
      intro c d
      have heq : (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).anti_self_dual.val c d) =
                 fun p => deriv (fun s => ((v s).toUniverse.asd_sector nu p).val c d) t := by
        ext p; exact deriv_chiralProject_asd v h_valid t nu p c d
      rw [heq]
      exact smooth_implies_diff_x _ t x (deriv_t_smooth _ (h_valid.2.1 nu c d))

    have hm := partialDerivSl2c_eq_mat _ mu x h_diff_asd
    have heval := congr_fun (congr_fun hm i') j'
    rw [heval]

    have heq2 : (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).anti_self_dual.val i' j') =
                fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t := by
      ext p
      have hc2 := deriv_chiralProject_asd v h_valid t nu p i' j'
      rw [hc2]
      have h_conn_eq : (fun s => (v s).toUniverse.spin4c_connection nu p i j) = fun s => ((v s).toUniverse.asd_sector nu p).val i' j' := by
        ext s
        have hs : (v s).toUniverse.spin4c_connection nu p i j = (embedSelfDual ((v s).toUniverse.sd_sector nu p) + embedAntiSelfDual ((v s).toUniverse.asd_sector nu p)) i j := by rw [spin4c_connection_eq_embed]
        rw [hs]
        simp only [Matrix.add_apply, eval_embedSelfDual, eval_embedAntiSelfDual, Equiv.symm_apply_apply, zero_add]
        rw [h_i, h_j]
        dsimp only
        ring
      rw [h_conn_eq]

    change partialDeriv mu (fun p => (chiralProject (Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t))).anti_self_dual.val i' j') x =
           partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t) x
    exact congrArg (fun F => partialDeriv mu F x) heq2

lemma partialDerivChiral_curvature (v : ℝ → PhysicalUniverse) (h_valid : isValidPhysicalVariation v) (t : ℝ) (mu rho sigma : Fin 4) (x : SpacetimePoint) :
  partialDerivChiral mu (fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p) x =
  Matrix.of (fun i j => partialDeriv mu (fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j) x) := by
  ext i j
  have hc : partialDerivChiral mu (fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p) x i j =
            (embedSelfDual (partialDerivSl2c mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).self_dual) x)) i j +
            (embedAntiSelfDual (partialDerivSl2c mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).anti_self_dual) x)) i j := rfl
  rw [hc]

  rcases h_i : chiralIso.symm i with i' | i' <;> rcases h_j : chiralIso.symm j with j' | j'
  · have hr1 : (embedSelfDual (partialDerivSl2c mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).self_dual) x)) i j =
               (partialDerivSl2c mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).self_dual) x).val i' j' := by
      unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    rw [hr1]

    have h_diff_sd : ∀ c d, DifferentiableAt ℝ (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).self_dual.val c d) x := by
      intro c d
      have heq : (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).self_dual.val c d) =
                 fun p => (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p).val c d := by
        ext p
        have h_curv := curvature_spin4c_eq (v t).toUniverse rho sigma p
        have hs : (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).self_dual = curvatureSl2c (v t).toUniverse.sd_sector rho sigma p := by
          rw [h_curv, chiralProject_embed_sd]
        rw [hs]
      rw [heq]

      have hs_sd : ∀ a c' d', ContDiff ℝ ⊤ (fun p => ((v t).toUniverse.sd_sector a p).val c' d') := by
        intro a c' d'
        let c_pt : ℝ × SpacetimePoint := (t, 0)
        let L : SpacetimePoint →L[ℝ] (ℝ × SpacetimePoint) := ContinuousLinearMap.prod (0 : SpacetimePoint →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ SpacetimePoint)
        let g : SpacetimePoint → ℝ × SpacetimePoint := fun p => c_pt + L p
        have hg : ContDiff ℝ ⊤ g := ContDiff.add contDiff_const L.contDiff
        have h_eq : (fun p => ((v t).toUniverse.sd_sector a p).val c' d') = (fun tx : ℝ × SpacetimePoint => ((v tx.1).toUniverse.sd_sector a tx.2).val c' d') ∘ g := by
          ext p
          have hc1 : (g p).1 = t := by change t + 0 = t; ring
          have hc2 : (g p).2 = p := by change 0 + p = p; simp
          change ((v t).toUniverse.sd_sector a p).val c' d' = ((v (g p).1).toUniverse.sd_sector a (g p).2).val c' d'
          rw [hc1, hc2]
        rw [h_eq]
        exact (h_valid.1 a c' d').comp hg
      exact diff_curvatureSl2c (v t).toUniverse.sd_sector rho sigma x hs_sd c d

    have hm := partialDerivSl2c_eq_mat _ mu x h_diff_sd
    have heval := congr_fun (congr_fun hm i') j'
    rw [heval]

    have hr2 : (embedAntiSelfDual (partialDerivSl2c mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).anti_self_dual) x)) i j = 0 := by
      unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    rw [hr2, add_zero]

    have heq2 : (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).self_dual.val i' j') =
                fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j := by
      ext p
      have h_curv := curvature_spin4c_eq (v t).toUniverse rho sigma p
      have hc2 : (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).self_dual = curvatureSl2c (v t).toUniverse.sd_sector rho sigma p := by
        rw [h_curv, chiralProject_embed_sd]
      rw [hc2]
      have h_conn_eq : curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j = (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p).val i' j' := by
        have hs : curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j = (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p) + embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j := by rw [h_curv]
        rw [hs]
        simp only [Matrix.add_apply, eval_embedSelfDual, eval_embedAntiSelfDual, Equiv.symm_apply_apply, add_zero]
        rw [h_i, h_j]
        dsimp only
        ring
      rw [h_conn_eq]

    change partialDeriv mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).self_dual.val i' j') x =
           partialDeriv mu (fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j) x
    exact congrArg (fun F => partialDeriv mu F x) heq2

  · have h1 : (embedSelfDual (partialDerivSl2c mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).self_dual) x)) i j = 0 := by
      unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    have h2 : (embedAntiSelfDual (partialDerivSl2c mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).anti_self_dual) x)) i j = 0 := by
      unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    rw [h1, h2, add_zero]
    change 0 = partialDeriv mu (fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j) x
    have h_zero : (fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j) = fun p => (0 : ℂ) := by
      ext p
      have h_curv := curvature_spin4c_eq (v t).toUniverse rho sigma p
      have hs : curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j = (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p) + embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j := by rw [h_curv]
      rw [hs]
      simp only [Matrix.add_apply, eval_embedSelfDual, eval_embedAntiSelfDual, Equiv.symm_apply_apply]
      rw [h_i, h_j]; ring
    rw [h_zero]; exact (partialDeriv_const (0 : ℂ) mu x).symm

  · have h1 : (embedSelfDual (partialDerivSl2c mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).self_dual) x)) i j = 0 := by
      unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    have h2 : (embedAntiSelfDual (partialDerivSl2c mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).anti_self_dual) x)) i j = 0 := by
      unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    rw [h1, h2, zero_add]
    change 0 = partialDeriv mu (fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j) x
    have h_zero : (fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j) = fun p => (0 : ℂ) := by
      ext p
      have h_curv := curvature_spin4c_eq (v t).toUniverse rho sigma p
      have hs : curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j = (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p) + embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j := by rw [h_curv]
      rw [hs]
      simp only [Matrix.add_apply, eval_embedSelfDual, eval_embedAntiSelfDual, Equiv.symm_apply_apply]
      rw [h_i, h_j]; ring
    rw [h_zero]; exact (partialDeriv_const (0 : ℂ) mu x).symm

  · have hr1 : (embedSelfDual (partialDerivSl2c mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).self_dual) x)) i j = 0 := by
      unfold embedSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    rw [hr1, zero_add]

    have hr2 : (embedAntiSelfDual (partialDerivSl2c mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).anti_self_dual) x)) i j =
               (partialDerivSl2c mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).anti_self_dual) x).val i' j' := by
      unfold embedAntiSelfDual; simp only [Matrix.of_apply, Equiv.symm_apply_apply]; rw [h_i, h_j]
    rw [hr2]

    have h_diff_asd : ∀ c d, DifferentiableAt ℝ (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).anti_self_dual.val c d) x := by
      intro c d
      have heq : (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).anti_self_dual.val c d) =
                 fun p => (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p).val c d := by
        ext p
        have h_curv := curvature_spin4c_eq (v t).toUniverse rho sigma p
        have hs : (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).anti_self_dual = curvatureSl2c (v t).toUniverse.asd_sector rho sigma p := by
          rw [h_curv, chiralProject_embed_asd]
        rw [hs]
      rw [heq]

      have hs_asd : ∀ a c' d', ContDiff ℝ ⊤ (fun p => ((v t).toUniverse.asd_sector a p).val c' d') := by
        intro a c' d'
        let c_pt : ℝ × SpacetimePoint := (t, 0)
        let L : SpacetimePoint →L[ℝ] (ℝ × SpacetimePoint) := ContinuousLinearMap.prod (0 : SpacetimePoint →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ SpacetimePoint)
        let g : SpacetimePoint → ℝ × SpacetimePoint := fun p => c_pt + L p
        have hg : ContDiff ℝ ⊤ g := ContDiff.add contDiff_const L.contDiff
        have h_eq : (fun p => ((v t).toUniverse.asd_sector a p).val c' d') = (fun tx : ℝ × SpacetimePoint => ((v tx.1).toUniverse.asd_sector a tx.2).val c' d') ∘ g := by
          ext p
          have hc1 : (g p).1 = t := by change t + 0 = t; ring
          have hc2 : (g p).2 = p := by change 0 + p = p; simp
          change ((v t).toUniverse.asd_sector a p).val c' d' = ((v (g p).1).toUniverse.asd_sector a (g p).2).val c' d'
          rw [hc1, hc2]
        rw [h_eq]
        exact (h_valid.2.1 a c' d').comp hg
      exact diff_curvatureSl2c (v t).toUniverse.asd_sector rho sigma x hs_asd c d

    have hm := partialDerivSl2c_eq_mat _ mu x h_diff_asd
    have heval := congr_fun (congr_fun hm i') j'
    rw [heval]

    have heq2 : (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).anti_self_dual.val i' j') =
                fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j := by
      ext p
      have h_curv := curvature_spin4c_eq (v t).toUniverse rho sigma p
      have hc2 : (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).anti_self_dual = curvatureSl2c (v t).toUniverse.asd_sector rho sigma p := by
        rw [h_curv, chiralProject_embed_asd]
      rw [hc2]
      have h_conn_eq : curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j = (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p).val i' j' := by
        have hs : curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j = (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p) + embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j := by rw [h_curv]
        rw [hs]
        simp only [Matrix.add_apply, eval_embedSelfDual, eval_embedAntiSelfDual, Equiv.symm_apply_apply, zero_add]
        rw [h_i, h_j]
        dsimp only
        ring
      rw [h_conn_eq]

    change partialDeriv mu (fun p => (chiralProject (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)).anti_self_dual.val i' j') x =
           partialDeriv mu (fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j) x
    exact congrArg (fun F => partialDeriv mu F x) heq2

lemma sum_bracket_trace_combine (dA A : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (F : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
  (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((bracket (dA mu) (A nu) + bracket (A mu) (dA nu)) * F rho sigma)) =
  2 * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * bracket (A nu) (F rho sigma))) := by
  have h1 : ∀ mu nu, bracket (dA mu) (A nu) + bracket (A mu) (dA nu) = dA mu * A nu - A nu * dA mu + A mu * dA nu - dA nu * A mu := by
    intro mu nu; unfold bracket; abel
  have h2 : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((bracket (dA mu) (A nu) + bracket (A mu) (dA nu)) * F rho sigma)) =
            (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((dA mu * A nu - A nu * dA mu + A mu * dA nu - dA nu * A mu) * F rho sigma)) := by
    apply Finset.sum_congr rfl; intro mu _
    apply Finset.sum_congr rfl; intro nu _
    apply Finset.sum_congr rfl; intro rho _
    apply Finset.sum_congr rfl; intro sigma _
    rw [h1 mu nu]
  rw [h2]
  have h3 := sum_epsilon_trace_combine dA A F
  rw [h3]
  apply congrArg
  apply Finset.sum_congr rfl; intro mu _
  apply Finset.sum_congr rfl; intro nu _
  apply Finset.sum_congr rfl; intro rho _
  apply Finset.sum_congr rfl; intro sigma _
  have h4 : A nu * F rho sigma - F rho sigma * A nu = bracket (A nu) (F rho sigma) := rfl
  rw [h4]

lemma trace_dA_dF_swap (dA : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (dF : Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (mu nu rho sigma : Fin 4) :
  CGD.Gravity.epsilon4 nu mu rho sigma * Matrix.trace (dA nu * dF mu rho sigma) =
  - (CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * dF mu rho sigma)) := by
  have h_eps : CGD.Gravity.epsilon4 nu mu rho sigma = - CGD.Gravity.epsilon4 mu nu rho sigma := epsilon_swap_mu_nu nu mu rho sigma
  rw [h_eps, neg_mul]

lemma sum_trace_dA_dF_swap (dA : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (dF : Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
  (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 nu mu rho sigma * Matrix.trace (dA nu * dF mu rho sigma)) =
  - (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * dF mu rho sigma)) := by
  have h_pull_neg : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, - (CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * dF mu rho sigma))) =
                    - (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * dF mu rho sigma)) := by
    simp_rw [Finset.sum_neg_distrib]
  rw [← h_pull_neg]
  apply Finset.sum_congr rfl; intro mu _
  apply Finset.sum_congr rfl; intro nu _
  apply Finset.sum_congr rfl; intro rho _
  apply Finset.sum_congr rfl; intro sigma _
  exact trace_dA_dF_swap dA dF mu nu rho sigma

lemma sum_add_distrib_4_c (f g : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
  (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, (f mu nu rho sigma + g mu nu rho sigma)) =
  (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, f mu nu rho sigma) +
  (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, g mu nu rho sigma) := by
  have h1 : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, (f mu nu rho sigma + g mu nu rho sigma)) =
            ∑ mu : Fin 4, ((∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, f mu nu rho sigma) +
                           (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, g mu nu rho sigma)) := by
    apply Finset.sum_congr rfl; intro mu _
    have h2 : (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, (f mu nu rho sigma + g mu nu rho sigma)) =
              ∑ nu : Fin 4, ((∑ rho : Fin 4, ∑ sigma : Fin 4, f mu nu rho sigma) +
                             (∑ rho : Fin 4, ∑ sigma : Fin 4, g mu nu rho sigma)) := by
      apply Finset.sum_congr rfl; intro nu _
      have h3 : (∑ rho : Fin 4, ∑ sigma : Fin 4, (f mu nu rho sigma + g mu nu rho sigma)) =
                ∑ rho : Fin 4, ((∑ sigma : Fin 4, f mu nu rho sigma) + (∑ sigma : Fin 4, g mu nu rho sigma)) := by
        apply Finset.sum_congr rfl; intro rho _
        exact Finset.sum_add_distrib
      rw [h3]
      exact Finset.sum_add_distrib
    rw [h2]
    exact Finset.sum_add_distrib
  rw [h1]
  exact Finset.sum_add_distrib

lemma sum_bianchi_trace_split (dA : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (A : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (F : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (dF : Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (h_bianchi : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (dF nu rho sigma + bracket (A nu) (F rho sigma)))) = 0) :
  (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * bracket (A nu) (F rho sigma))) =
  (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * dF mu rho sigma)) := by

  let X := (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * dF nu rho sigma))
  let Y := (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * bracket (A nu) (F rho sigma)))
  let W := (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * dF mu rho sigma))
  let Z := (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 nu mu rho sigma * Matrix.trace (dA nu * dF mu rho sigma))

  have h_add : ∀ mu nu rho sigma, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (dF nu rho sigma + bracket (A nu) (F rho sigma))) =
                                  CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * dF nu rho sigma) +
                                  CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * bracket (A nu) (F rho sigma)) := by
    intro mu nu rho sigma
    rw [Matrix.mul_add, Matrix.trace_add, mul_add]

  have h_sum_add : X + Y = 0 := by
    have h1 : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (dF nu rho sigma + bracket (A nu) (F rho sigma)))) = X + Y := by
      have h2 : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (dF nu rho sigma + bracket (A nu) (F rho sigma)))) =
                (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, (CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * dF nu rho sigma) + CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * bracket (A nu) (F rho sigma)))) := by
        apply Finset.sum_congr rfl; intro mu _; apply Finset.sum_congr rfl; intro nu _; apply Finset.sum_congr rfl; intro rho _; apply Finset.sum_congr rfl; intro sigma _
        exact h_add mu nu rho sigma
      rw [h2]
      exact sum_add_distrib_4_c _ _
    rw [← h1]
    exact h_bianchi

  have h_B_eval : Y = -X := by
    calc Y = 0 + Y := (zero_add Y).symm
         _ = -X + X + Y := by rw [neg_add_cancel]
         _ = -X + (X + Y) := by rw [add_assoc]
         _ = -X + 0 := by rw [h_sum_add]
         _ = -X := add_zero (-X)

  have h_swap : X = Z := by
    have h_comm : X = (∑ nu : Fin 4, ∑ mu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * dF nu rho sigma)) := Finset.sum_comm
    have h_rel : (∑ nu : Fin 4, ∑ mu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * dF nu rho sigma)) = Z := by
      apply Finset.sum_congr rfl; intro mu _
      apply Finset.sum_congr rfl; intro nu _
      rfl
    rw [h_comm, h_rel]

  have h_eps : Z = -W := sum_trace_dA_dF_swap dA dF

  have h_XW : X = -W := by
    rw [h_swap, h_eps]

  have h_final : Y = W := by
    rw [h_B_eval, h_XW, neg_neg]

  exact h_final

lemma satisfies_bianchi_natively (v : ℝ → PhysicalUniverse) (t : ℝ) (x : SpacetimePoint)
  (h_valid : isValidPhysicalVariation v) :
  satisfiesBianchiIdentity v t x := by
  unfold satisfiesBianchiIdentity

  let dA := fun mu => Matrix.of (fun i j => deriv (fun s => (v s).toUniverse.spin4c_connection mu x i j) t)
  let F := fun rho sigma => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma x
  let dF := fun nu rho sigma => Matrix.of (fun i j => partialDeriv nu (fun p => curvature (fun m p' => (v t).toUniverse.spin4c_connection m p') rho sigma p i j) x)
  let d_mu_dA_nu := fun mu nu => Matrix.of (fun i j => partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t) x)
  let A := fun mu => (v t).toUniverse.spin4c_connection mu x

  have hdA_diff1 : ∀ mu nu i j, DifferentiableAt ℝ (fun s => partialDerivChiral mu (fun p => (v s).toUniverse.spin4c_connection nu p) x i j) t := fun mu nu i j => hdA_diff v t x mu nu i j h_valid
  have hcomm_diff' : ∀ mu nu i j, DifferentiableAt ℝ (fun s => (embedSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).self_dual + embedAntiSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).anti_self_dual) i j) t := fun mu nu i j => hcomm_diff v t x mu nu i j h_valid

  have h_split := deriv_L_split v t x (fun mu nu i j => hdA_mu_commute v t x mu nu i j h_valid) hdA_diff1 hcomm_diff'
  have h_dF_orig := deriv_L_eq_trace_dF v t x (fun mu nu i j => hF_diff v t x mu nu i j h_valid)

  have h_bracket_simpl : ∀ mu nu, Matrix.of (fun i j => deriv (fun s => (embedSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).self_dual + embedAntiSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).anti_self_dual) i j) t) =
                                  bracket (dA mu) (A nu) + bracket (A mu) (dA nu) := by
    intro mu nu
    have h_eq : (fun i j => deriv (fun s => (embedSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).self_dual + embedAntiSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).anti_self_dual) i j) t) =
                (fun i j => deriv (fun s => bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x) i j) t) := by
      ext i j
      have hc : (fun s => (embedSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).self_dual + embedAntiSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).anti_self_dual) i j) =
                fun s => bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x) i j := by
        ext s
        have hb := chiralProject_bracket_spin4c_sd (v s).toUniverse mu nu x
        have hb2 := chiralProject_bracket_spin4c_asd (v s).toUniverse mu nu x
        have hb3 := bracket_spin4c (v s).toUniverse mu nu x
        rw [hb, hb2, hb3]
      rw [hc]
    rw [h_eq]
    have hA : ∀ a b, DifferentiableAt ℝ (fun s => (v s).toUniverse.spin4c_connection mu x a b) t := fun a b => diff_t_conn v h_valid t x mu a b
    have hB : ∀ a b, DifferentiableAt ℝ (fun s => (v s).toUniverse.spin4c_connection nu x a b) t := fun a b => diff_t_conn v h_valid t x nu a b
    exact deriv_bracket (fun s => (v s).toUniverse.spin4c_connection mu x) (fun s => (v s).toUniverse.spin4c_connection nu x) t hA hB

  have h_split_rw : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (Matrix.of (fun i j => deriv (fun s => curvature (fun m p => (v s).toUniverse.spin4c_connection m p) mu nu x i j) t) * F rho sigma)) =
                    (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((d_mu_dA_nu mu nu - d_mu_dA_nu nu mu) * F rho sigma)) +
                    (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((bracket (dA mu) (A nu) + bracket (A mu) (dA nu)) * F rho sigma)) := by
    have hs := h_split
    have h1 : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((partialDerivChiral mu (fun p => Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection nu p a b) t)) x - partialDerivChiral nu (fun p => Matrix.of (fun a b => deriv (fun s => (v s).toUniverse.spin4c_connection mu p a b) t)) x) * F rho sigma)) =
              (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((d_mu_dA_nu mu nu - d_mu_dA_nu nu mu) * F rho sigma)) := by
      apply Finset.sum_congr rfl; intro mu _
      apply Finset.sum_congr rfl; intro nu _
      apply Finset.sum_congr rfl; intro rho _
      apply Finset.sum_congr rfl; intro sigma _
      rw [partialDerivChiral_matrix_of_deriv v h_valid t mu nu x, partialDerivChiral_matrix_of_deriv v h_valid t nu mu x]
    rw [h1] at hs
    have h2 : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (Matrix.of (fun i j => deriv (fun s => (embedSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).self_dual + embedAntiSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).anti_self_dual) i j) t) * F rho sigma)) =
              (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace ((bracket (dA mu) (A nu) + bracket (A mu) (dA nu)) * F rho sigma)) := by
      apply Finset.sum_congr rfl; intro mu _
      apply Finset.sum_congr rfl; intro nu _
      apply Finset.sum_congr rfl; intro rho _
      apply Finset.sum_congr rfl; intro sigma _
      rw [h_bracket_simpl mu nu]
    rw [h2] at hs
    exact hs

  have h_T_diff := epsilon_contract_antisymm_diff d_mu_dA_nu F
  have h_B_diff := sum_bracket_trace_combine dA A F
  rw [h_T_diff, h_B_diff] at h_split_rw

  have h_bianchi_0 := bianchi_contraction_zero (v t).toUniverse dA x

  have hb_eq : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (dF nu rho sigma + bracket (A nu) (F rho sigma)))) = 0 := by
    have h_subst : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (partialDerivChiral nu (fun p => curvature (fun m p' => (v t).toUniverse.spin4c_connection m p') rho sigma p) x + bracket (A nu) (F rho sigma)))) = 0 := h_bianchi_0
    have h_apply : ∀ nu rho sigma, partialDerivChiral nu (fun p => curvature (fun m p' => (v t).toUniverse.spin4c_connection m p') rho sigma p) x = dF nu rho sigma := by
      intro nu rho sigma
      exact partialDerivChiral_curvature v h_valid t nu rho sigma x
    have h_rw : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (partialDerivChiral nu (fun p => curvature (fun m p' => (v t).toUniverse.spin4c_connection m p') rho sigma p) x + bracket (A nu) (F rho sigma)))) =
                (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA mu * (dF nu rho sigma + bracket (A nu) (F rho sigma)))) := by
      apply Finset.sum_congr rfl; intro mu _
      apply Finset.sum_congr rfl; intro nu _
      apply Finset.sum_congr rfl; intro rho _
      apply Finset.sum_congr rfl; intro sigma _
      rw [h_apply nu rho sigma]
    rw [← h_rw]
    exact h_subst

  have h_swap_B := sum_bianchi_trace_split dA A F dF hb_eq
  rw [h_swap_B] at h_split_rw

  have h_fac : 2 * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (d_mu_dA_nu mu nu * F rho sigma)) +
               2 * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * dF mu rho sigma)) =
               2 * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * (Matrix.trace (d_mu_dA_nu mu nu * F rho sigma) + Matrix.trace (dA nu * dF mu rho sigma))) := by
    rw [← mul_add]
    apply congrArg
    have h_add : ∀ mu nu rho sigma, CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (d_mu_dA_nu mu nu * F rho sigma) + CGD.Gravity.epsilon4 mu nu rho sigma * Matrix.trace (dA nu * dF mu rho sigma) =
                                    CGD.Gravity.epsilon4 mu nu rho sigma * (Matrix.trace (d_mu_dA_nu mu nu * F rho sigma) + Matrix.trace (dA nu * dF mu rho sigma)) := by
      intro mu nu rho sigma
      rw [mul_add]
    simp_rw [← Finset.sum_add_distrib, h_add]

  rw [h_fac] at h_split_rw
  rw [h_split_rw] at h_dF_orig

  have h_dF_final : deriv (fun s => lagrangianDensity (fun mu nu => curvature (fun m p => (v s).toUniverse.spin4c_connection m p) mu nu x)) t =
                    (-2 : ℂ) * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * (Matrix.trace (d_mu_dA_nu mu nu * F rho sigma) + Matrix.trace (dA nu * dF mu rho sigma))) := by
    rw [h_dF_orig]
    ring

  have h_sub_mat : ∀ mu nu rho sigma, Matrix.trace (d_mu_dA_nu mu nu * F rho sigma) = Matrix.trace (Matrix.of (fun i j => partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p) t i j) x) * F rho sigma) := by
    intro mu nu rho sigma
    have hc : d_mu_dA_nu mu nu = Matrix.of (fun i j => partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p) t i j) x) :=
      Matrix.ext (fun i j => congrArg (fun F => partialDeriv mu F x) (funext (fun p => (deriv_matrix_apply (fun s => (v s).toUniverse.spin4c_connection nu p) t (fun a b => diff_t_conn v h_valid t p nu a b) i j).symm)))
    exact congrArg (fun M => Matrix.trace (M * F rho sigma)) hc

  have h_sub_mat2 : ∀ mu nu rho sigma, Matrix.trace (dA nu * dF mu rho sigma) = Matrix.trace (deriv (fun s => (v s).toUniverse.spin4c_connection nu x) t * Matrix.of (fun i j => partialDeriv mu (fun p => curvature (fun m p' => (v t).toUniverse.spin4c_connection m p') rho sigma p i j) x)) := by
    intro mu nu rho sigma
    have hd_mat : dA nu = deriv (fun s => (v s).toUniverse.spin4c_connection nu x) t :=
      Matrix.ext (fun i j => (deriv_matrix_apply (fun s => (v s).toUniverse.spin4c_connection nu x) t (fun a b => diff_t_conn v h_valid t x nu a b) i j).symm)
    exact congrArg (fun M => Matrix.trace (M * dF mu rho sigma)) hd_mat

  have h_sub_total : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * (Matrix.trace (d_mu_dA_nu mu nu * F rho sigma) + Matrix.trace (dA nu * dF mu rho sigma))) =
                     (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * (Matrix.trace (Matrix.of (fun i j => partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p) t i j) x) * F rho sigma) + Matrix.trace (deriv (fun s => (v s).toUniverse.spin4c_connection nu x) t * dF mu rho sigma))) := by
    apply Finset.sum_congr rfl; intro mu _
    apply Finset.sum_congr rfl; intro nu _
    apply Finset.sum_congr rfl; intro rho _
    apply Finset.sum_congr rfl; intro sigma _
    rw [h_sub_mat, h_sub_mat2]

  have h_unroll_F : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * (Matrix.trace (Matrix.of (fun i j => partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p) t i j) x) * F rho sigma) + Matrix.trace (deriv (fun s => (v s).toUniverse.spin4c_connection nu x) t * dF mu rho sigma))) =
                    (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * (Matrix.trace (Matrix.of (fun i j => partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p) t i j) x) * curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma x) + Matrix.trace (deriv (fun s => (v s).toUniverse.spin4c_connection nu x) t * Matrix.of (fun i j => partialDeriv mu (fun p => curvature (fun m p' => (v t).toUniverse.spin4c_connection m p') rho sigma p i j) x)))) := by
    rfl

  have h_dF_sub : deriv (fun s => lagrangianDensity (fun mu nu => curvature (fun m p => (v s).toUniverse.spin4c_connection m p) mu nu x)) t =
                  (-2 : ℂ) * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * (Matrix.trace (Matrix.of (fun i j => partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p) t i j) x) * curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma x) + Matrix.trace (deriv (fun s => (v s).toUniverse.spin4c_connection nu x) t * Matrix.of (fun i j => partialDeriv mu (fun p => curvature (fun m p' => (v t).toUniverse.spin4c_connection m p') rho sigma p i j) x)))) := by
    calc deriv (fun s => lagrangianDensity (fun mu nu => curvature (fun m p => (v s).toUniverse.spin4c_connection m p) mu nu x)) t =
         (-2 : ℂ) * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * (Matrix.trace (d_mu_dA_nu mu nu * F rho sigma) + Matrix.trace (dA nu * dF mu rho sigma))) := h_dF_final
         _ = (-2 : ℂ) * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * (Matrix.trace (Matrix.of (fun i j => partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p) t i j) x) * F rho sigma) + Matrix.trace (deriv (fun s => (v s).toUniverse.spin4c_connection nu x) t * dF mu rho sigma))) := by rw [h_sub_total]
         _ = (-2 : ℂ) * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma * (Matrix.trace (Matrix.of (fun i j => partialDeriv mu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p) t i j) x) * curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma x) + Matrix.trace (deriv (fun s => (v s).toUniverse.spin4c_connection nu x) t * Matrix.of (fun i j => partialDeriv mu (fun p => curvature (fun m p' => (v t).toUniverse.spin4c_connection m p') rho sigma p i j) x)))) := by rw [h_unroll_F]

  have hA_diff : ∀ nu i j, DifferentiableAt ℝ (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p) t i j) x := fun nu i j => diff_x_deriv_t_conn_matrix v h_valid t x nu i j
  have hF_diff' : ∀ rho sigma i j, DifferentiableAt ℝ (fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j) x := fun rho sigma i j => hF_diff_spatial v t x rho sigma i j h_valid

  have h_div := variationCurrent_divergence v t x hA_diff hF_diff'
  rw [h_dF_sub]
  exact h_div.symm

end CGD.Foundations

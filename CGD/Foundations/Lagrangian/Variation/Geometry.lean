-- FILENAME: CGD/Foundations/Lagrangian/Variation/Geometry.lean

import CGD.Foundations.TensorCalculus.BianchiIdentity
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology
import CGD.Foundations.Calculus
import CGD.Foundations.Spacetime
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

open Matrix Complex BigOperators CGD.Axioms CGD.Foundations

namespace CGD.Foundations

/--
Contracts the geometric SL(2,C) Bianchi identity against the totally antisymmetric 
Levi-Civita tensor. Because ε is invariant under even permutations, the three 
cyclic permutations natively combine.
-/
lemma epsilon_contract_bianchi (A : Sl2cGaugeField) (mu : Fin 4) (x : SpacetimePoint) :
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma • (covariantDeriv A.val rho sigma nu x + 
                                            covariantDeriv A.val sigma nu rho x + 
                                            covariantDeriv A.val nu rho sigma x)) = 0 := by
  have h_bianchi_zero : ∀ nu rho sigma, covariantDeriv A.val rho sigma nu x + 
                                        covariantDeriv A.val sigma nu rho x + 
                                        covariantDeriv A.val nu rho sigma x = 0 := by
    intro nu rho sigma
    exact bianchiIdentity A rho sigma nu x
  apply Finset.sum_eq_zero; intro nu _
  apply Finset.sum_eq_zero; intro rho _
  apply Finset.sum_eq_zero; intro sigma _
  rw [h_bianchi_zero nu rho sigma]
  exact smul_zero _

lemma sum_cyclic_3 {α : Type*} [AddCommMonoid α] (f : Fin 4 → Fin 4 → Fin 4 → α) :
  (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, f a b c) =
  (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, f b c a) := by
  have h1 : (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c := by
    apply Finset.sum_congr rfl; intro a _
    exact Finset.sum_comm
  rw [h1, Finset.sum_comm]
  
lemma sum_cyclic_3_rev {α : Type*} [AddCommMonoid α] (f : Fin 4 → Fin 4 → Fin 4 → α) :
  (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, f a b c) =
  (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, f c a b) := by
  have h1 : (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
  rw [h1]
  have h2 : (∑ b, ∑ a, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
    apply Finset.sum_congr rfl; intro b _
    exact Finset.sum_comm
  rw [h2]

lemma eps_swap23 (a b c d : Fin 4) : CGD.Gravity.epsilon4 a b c d = - CGD.Gravity.epsilon4 a c b d :=
  (CGD.Gravity.epsilon4_alt a b c d).2.1

lemma eps_swap34 (a b c d : Fin 4) : CGD.Gravity.epsilon4 a b c d = - CGD.Gravity.epsilon4 a b d c :=
  (CGD.Gravity.epsilon4_alt a b c d).2.2

lemma epsilon4_cyclic_shift_2 (mu nu rho sigma : Fin 4) :
  CGD.Gravity.epsilon4 mu rho sigma nu = CGD.Gravity.epsilon4 mu nu rho sigma := by
  have h1 := eps_swap23 mu nu rho sigma
  have h2 := eps_swap34 mu rho nu sigma
  rw [h2] at h1
  calc CGD.Gravity.epsilon4 mu rho sigma nu
    _ = - - CGD.Gravity.epsilon4 mu rho sigma nu := (neg_neg _).symm
    _ = CGD.Gravity.epsilon4 mu nu rho sigma := h1.symm

lemma epsilon4_cyclic_shift_1 (mu nu rho sigma : Fin 4) :
  CGD.Gravity.epsilon4 mu sigma nu rho = CGD.Gravity.epsilon4 mu nu rho sigma := by
  have h_base := epsilon4_cyclic_shift_2 mu nu rho sigma
  have h1 := eps_swap23 mu rho sigma nu
  have h2 := eps_swap34 mu sigma rho nu
  rw [h2] at h1
  calc CGD.Gravity.epsilon4 mu sigma nu rho
    _ = - - CGD.Gravity.epsilon4 mu sigma nu rho := (neg_neg _).symm
    _ = CGD.Gravity.epsilon4 mu rho sigma nu := h1.symm
    _ = CGD.Gravity.epsilon4 mu nu rho sigma := h_base

lemma sum_covariantDeriv_shift1 (A : Sl2cGaugeField) (mu : Fin 4) (x : SpacetimePoint) :
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val sigma nu rho x) =
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val rho sigma nu x) := by
  have h_cyc := sum_cyclic_3_rev (fun a b c => CGD.Gravity.epsilon4 mu a b c • covariantDeriv A.val c a b x)
  have h_LHS : (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, (fun a b c => CGD.Gravity.epsilon4 mu a b c • covariantDeriv A.val c a b x) a b c) =
               (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val sigma nu rho x) := rfl
  have h_RHS : (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, (fun a b c => CGD.Gravity.epsilon4 mu a b c • covariantDeriv A.val c a b x) c a b) =
               (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu sigma nu rho • covariantDeriv A.val rho sigma nu x) := rfl
  rw [h_LHS, h_RHS] at h_cyc
  rw [h_cyc]
  apply Finset.sum_congr rfl; intro nu _
  apply Finset.sum_congr rfl; intro rho _
  apply Finset.sum_congr rfl; intro sigma _
  rw [epsilon4_cyclic_shift_1 mu nu rho sigma]

lemma sum_covariantDeriv_shift2 (A : Sl2cGaugeField) (mu : Fin 4) (x : SpacetimePoint) :
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val nu rho sigma x) =
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val rho sigma nu x) := by
  have h_cyc := sum_cyclic_3 (fun a b c => CGD.Gravity.epsilon4 mu a b c • covariantDeriv A.val a b c x)
  have h_LHS : (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, (fun a b c => CGD.Gravity.epsilon4 mu a b c • covariantDeriv A.val a b c x) a b c) =
               (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val nu rho sigma x) := rfl
  have h_RHS : (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, (fun a b c => CGD.Gravity.epsilon4 mu a b c • covariantDeriv A.val a b c x) b c a) =
               (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu rho sigma nu • covariantDeriv A.val rho sigma nu x) := rfl
  rw [h_LHS, h_RHS] at h_cyc
  rw [h_cyc]
  apply Finset.sum_congr rfl; intro nu _
  apply Finset.sum_congr rfl; intro rho _
  apply Finset.sum_congr rfl; intro sigma _
  rw [epsilon4_cyclic_shift_2 mu nu rho sigma]
  
/-- 
The fully contracted Bianchi Identity. 
Because the three cyclic geometric permutations natively map onto each other across the 
epsilon tensor, the triple sum collapses into a single term, proving that the exact covariant divergence 
evaluates to zero natively.
-/
lemma contracted_bianchi_identity (A : Sl2cGaugeField) (mu : Fin 4) (x : SpacetimePoint) :
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val rho sigma nu x) = 0 := by
  have h_full := epsilon_contract_bianchi A mu x
  
  have h_dist : (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma • (covariantDeriv A.val rho sigma nu x + covariantDeriv A.val sigma nu rho x + covariantDeriv A.val nu rho sigma x)) =
    (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val rho sigma nu x) +
    (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val sigma nu rho x) +
    (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val nu rho sigma x) := by
    simp_rw [smul_add, Finset.sum_add_distrib]
    
  rw [h_dist] at h_full
  rw [sum_covariantDeriv_shift1 A mu x] at h_full
  rw [sum_covariantDeriv_shift2 A mu x] at h_full
  
  have h_add3 : ∀ y : SL2C, y + y + y = (3 : ℂ) • y := by
    intro y
    apply Subtype.ext
    change y.val + y.val + y.val = (3 : ℂ) • y.val
    have h3 : (3 : ℂ) = 1 + 1 + 1 := by norm_num
    rw [h3, add_smul, add_smul, one_smul]
  
  have h_sum_add : (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val rho sigma nu x) +
                   (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val rho sigma nu x) +
                   (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val rho sigma nu x) =
                   (3 : ℂ) • (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val rho sigma nu x) := by
    exact h_add3 _
    
  have h_zero : (3 : ℂ) • (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val rho sigma nu x) = 0 := by
    rw [← h_sum_add]
    exact h_full
  
  apply Subtype.ext
  have h_val_zero : ((3 : ℂ) • (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val rho sigma nu x)).val = 0 := congrArg Subtype.val h_zero
  change (3 : ℂ) • ((∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv A.val rho sigma nu x).val) = 0 at h_val_zero
  exact smul_eq_zero.mp h_val_zero |>.resolve_left (by norm_num)

lemma bracket_embed_split (L1 R1 L2 R2 : SL2C) :
  bracket (embedSelfDual L1 + embedAntiSelfDual R1) (embedSelfDual L2 + embedAntiSelfDual R2) =
  embedSelfDual ⁅L1, L2⁆ + embedAntiSelfDual ⁅R1, R2⁆ := by
  ext i j
  unfold bracket
  have h_expand1 : ((embedSelfDual L1 + embedAntiSelfDual R1) * (embedSelfDual L2 + embedAntiSelfDual R2)) = 
                   embedSelfDual L1 * embedSelfDual L2 + embedAntiSelfDual R1 * embedAntiSelfDual R2 := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    rw [chiralOrthogonality, chiralOrthogonalityDl]
    simp
  have h_expand2 : ((embedSelfDual L2 + embedAntiSelfDual R2) * (embedSelfDual L1 + embedAntiSelfDual R1)) = 
                   embedSelfDual L2 * embedSelfDual L1 + embedAntiSelfDual R2 * embedAntiSelfDual R1 := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    rw [chiralOrthogonality, chiralOrthogonalityDl]
    simp
  rw [h_expand1, h_expand2]
  
  cases h_i : chiralIso.symm i with
  | inl il =>
    cases h_j : chiralIso.symm j with
    | inl jl =>
      have h_sd1 := embed_self_dual_mul_inl_inl L1 L2 il jl
      have h_sd2 := embed_self_dual_mul_inl_inl L2 L1 il jl
      have h_asd1 : (embedAntiSelfDual R1 * embedAntiSelfDual R2) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_anti_self_dual_mul_apply R1 R2 (Sum.inl il) (Sum.inl jl)
      have h_asd2 : (embedAntiSelfDual R2 * embedAntiSelfDual R1) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_anti_self_dual_mul_apply R2 R1 (Sum.inl il) (Sum.inl jl)
      have h_res_sd : (embedSelfDual ⁅L1, L2⁆) i j = ⁅L1, L2⁆.val il jl := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_self_dual_inl_inl _ il jl
      have h_res_asd : (embedAntiSelfDual ⁅R1, R2⁆) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        unfold embedAntiSelfDual; simp
      simp only [Matrix.add_apply, Matrix.sub_apply]
      rw [h_asd1, h_asd2, h_res_asd]
      have h_rw1 : (embedSelfDual L1 * embedSelfDual L2) i j = (L1.val * L2.val) il jl := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact h_sd1
      have h_rw2 : (embedSelfDual L2 * embedSelfDual L1) i j = (L2.val * L1.val) il jl := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact h_sd2
      rw [h_rw1, h_rw2, h_res_sd]
      have h_comm : ⁅L1, L2⁆.val il jl = (L1.val * L2.val) il jl - (L2.val * L1.val) il jl := rfl
      rw [h_comm]
      ring
    | inr jr =>
      have h_sd1 : (embedSelfDual L1 * embedSelfDual L2) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_self_dual_mul_apply L1 L2 (Sum.inl il) (Sum.inr jr)
      have h_asd1 : (embedAntiSelfDual R1 * embedAntiSelfDual R2) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_anti_self_dual_mul_apply R1 R2 (Sum.inl il) (Sum.inr jr)
      have h_sd2 : (embedSelfDual L2 * embedSelfDual L1) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_self_dual_mul_apply L2 L1 (Sum.inl il) (Sum.inr jr)
      have h_asd2 : (embedAntiSelfDual R2 * embedAntiSelfDual R1) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_anti_self_dual_mul_apply R2 R1 (Sum.inl il) (Sum.inr jr)
      have h_res_sd : (embedSelfDual ⁅L1, L2⁆) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        unfold embedSelfDual; simp
      have h_res_asd : (embedAntiSelfDual ⁅R1, R2⁆) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        unfold embedAntiSelfDual; simp
      simp only [Matrix.add_apply, Matrix.sub_apply]
      rw [h_sd1, h_asd1, h_sd2, h_asd2, h_res_sd, h_res_asd]
      ring
  | inr ir =>
    cases h_j : chiralIso.symm j with
    | inl jl =>
      have h_sd1 : (embedSelfDual L1 * embedSelfDual L2) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_self_dual_mul_apply L1 L2 (Sum.inr ir) (Sum.inl jl)
      have h_asd1 : (embedAntiSelfDual R1 * embedAntiSelfDual R2) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_anti_self_dual_mul_apply R1 R2 (Sum.inr ir) (Sum.inl jl)
      have h_sd2 : (embedSelfDual L2 * embedSelfDual L1) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_self_dual_mul_apply L2 L1 (Sum.inr ir) (Sum.inl jl)
      have h_asd2 : (embedAntiSelfDual R2 * embedAntiSelfDual R1) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_anti_self_dual_mul_apply R2 R1 (Sum.inr ir) (Sum.inl jl)
      have h_res_sd : (embedSelfDual ⁅L1, L2⁆) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        unfold embedSelfDual; simp
      have h_res_asd : (embedAntiSelfDual ⁅R1, R2⁆) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        unfold embedAntiSelfDual; simp
      simp only [Matrix.add_apply, Matrix.sub_apply]
      rw [h_sd1, h_asd1, h_sd2, h_asd2, h_res_sd, h_res_asd]
      ring
    | inr jr =>
      have h_asd1 := embed_anti_self_dual_mul_inr_inr R1 R2 ir jr
      have h_asd2 := embed_anti_self_dual_mul_inr_inr R2 R1 ir jr
      have h_sd1 : (embedSelfDual L1 * embedSelfDual L2) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_self_dual_mul_apply L1 L2 (Sum.inr ir) (Sum.inr jr)
      have h_sd2 : (embedSelfDual L2 * embedSelfDual L1) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_self_dual_mul_apply L2 L1 (Sum.inr ir) (Sum.inr jr)
      have h_res_asd : (embedAntiSelfDual ⁅R1, R2⁆) i j = ⁅R1, R2⁆.val ir jr := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact embed_anti_self_dual_inr_inr _ ir jr
      have h_res_sd : (embedSelfDual ⁅L1, L2⁆) i j = 0 := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        unfold embedSelfDual; simp
      simp only [Matrix.add_apply, Matrix.sub_apply]
      rw [h_sd1, h_sd2, h_res_sd]
      have h_rw1 : (embedAntiSelfDual R1 * embedAntiSelfDual R2) i j = (R1.val * R2.val) ir jr := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact h_asd1
      have h_rw2 : (embedAntiSelfDual R2 * embedAntiSelfDual R1) i j = (R2.val * R1.val) ir jr := by
        rw [← Equiv.apply_symm_apply chiralIso i, ← Equiv.apply_symm_apply chiralIso j, h_i, h_j]
        exact h_asd2
      rw [h_rw1, h_rw2, h_res_asd]
      have h_comm : ⁅R1, R2⁆.val ir jr = (R1.val * R2.val) ir jr - (R2.val * R1.val) ir jr := rfl
      rw [h_comm]
      ring

lemma eval_embedSelfDual (A : SL2C) (i j : Fin 4) : 
  (embedSelfDual A) i j = match chiralIso.symm i, chiralIso.symm j with
    | Sum.inl i', Sum.inl j' => A.val i' j'
    | _, _ => 0 := rfl

lemma eval_embedAntiSelfDual (A : SL2C) (i j : Fin 4) : 
  (embedAntiSelfDual A) i j = match chiralIso.symm i, chiralIso.symm j with
    | Sum.inr i', Sum.inr j' => A.val i' j'
    | _, _ => 0 := rfl

lemma partialDerivChiral_eq_embed_proj (μ : Fin 4) (f : SpacetimePoint → ChiralM) (x : SpacetimePoint) :
  partialDerivChiral μ f x = 
  embedSelfDual (partialDerivSl2c μ (fun p => (chiralProject (f p)).self_dual) x) + 
  embedAntiSelfDual (partialDerivSl2c μ (fun p => (chiralProject (f p)).anti_self_dual) x) := rfl

lemma embedSelfDual_add (A B : SL2C) : embedSelfDual (A + B) = embedSelfDual A + embedSelfDual B := by
  ext i j
  change (embedSelfDual (A + B)) i j = (embedSelfDual A) i j + (embedSelfDual B) i j
  rw [eval_embedSelfDual, eval_embedSelfDual, eval_embedSelfDual]
  cases chiralIso.symm i <;> cases chiralIso.symm j
  · rfl
  · ring
  · ring
  · ring

lemma embedAntiSelfDual_add (A B : SL2C) : embedAntiSelfDual (A + B) = embedAntiSelfDual A + embedAntiSelfDual B := by
  ext i j
  change (embedAntiSelfDual (A + B)) i j = (embedAntiSelfDual A) i j + (embedAntiSelfDual B) i j
  rw [eval_embedAntiSelfDual, eval_embedAntiSelfDual, eval_embedAntiSelfDual]
  cases chiralIso.symm i <;> cases chiralIso.symm j
  · ring
  · ring
  · ring
  · rfl

lemma embedSelfDual_sub (A B : SL2C) : embedSelfDual (A - B) = embedSelfDual A - embedSelfDual B := by
  ext i j
  change (embedSelfDual (A - B)) i j = (embedSelfDual A) i j - (embedSelfDual B) i j
  rw [eval_embedSelfDual, eval_embedSelfDual, eval_embedSelfDual]
  cases chiralIso.symm i <;> cases chiralIso.symm j
  · rfl
  · ring
  · ring
  · ring

lemma embedAntiSelfDual_sub (A B : SL2C) : embedAntiSelfDual (A - B) = embedAntiSelfDual A - embedAntiSelfDual B := by
  ext i j
  change (embedAntiSelfDual (A - B)) i j = (embedAntiSelfDual A) i j - (embedAntiSelfDual B) i j
  rw [eval_embedAntiSelfDual, eval_embedAntiSelfDual, eval_embedAntiSelfDual]
  cases chiralIso.symm i <;> cases chiralIso.symm j
  · ring
  · ring
  · ring
  · rfl

lemma embedSelfDual_smul (c : ℂ) (A : SL2C) : c • embedSelfDual A = embedSelfDual (c • A) := by
  ext i j
  change c * (embedSelfDual A) i j = (embedSelfDual (c • A)) i j
  rw [eval_embedSelfDual, eval_embedSelfDual]
  cases chiralIso.symm i <;> cases chiralIso.symm j
  · rfl
  · ring
  · ring
  · ring

lemma embedAntiSelfDual_smul (c : ℂ) (A : SL2C) : c • embedAntiSelfDual A = embedAntiSelfDual (c • A) := by
  ext i j
  change c * (embedAntiSelfDual A) i j = (embedAntiSelfDual (c • A)) i j
  rw [eval_embedAntiSelfDual, eval_embedAntiSelfDual]
  cases chiralIso.symm i <;> cases chiralIso.symm j
  · ring
  · ring
  · ring
  · rfl

lemma sum_embedSelfDual_3 (f : Fin 4 → Fin 4 → Fin 4 → SL2C) :
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, embedSelfDual (f nu rho sigma)) =
  embedSelfDual (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, f nu rho sigma) := by
  ext i j
  change (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, (embedSelfDual (f nu rho sigma)) i j) = (embedSelfDual (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, f nu rho sigma)) i j
  simp_rw [eval_embedSelfDual]
  cases chiralIso.symm i <;> cases chiralIso.symm j
  · rfl
  · exact Finset.sum_eq_zero (fun _ _ => Finset.sum_eq_zero (fun _ _ => Finset.sum_eq_zero (fun _ _ => rfl)))
  · exact Finset.sum_eq_zero (fun _ _ => Finset.sum_eq_zero (fun _ _ => Finset.sum_eq_zero (fun _ _ => rfl)))
  · exact Finset.sum_eq_zero (fun _ _ => Finset.sum_eq_zero (fun _ _ => Finset.sum_eq_zero (fun _ _ => rfl)))

lemma sum_embedAntiSelfDual_3 (f : Fin 4 → Fin 4 → Fin 4 → SL2C) :
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, embedAntiSelfDual (f nu rho sigma)) =
  embedAntiSelfDual (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, f nu rho sigma) := by
  ext i j
  change (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, (embedAntiSelfDual (f nu rho sigma)) i j) = (embedAntiSelfDual (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, f nu rho sigma)) i j
  simp_rw [eval_embedAntiSelfDual]
  cases chiralIso.symm i <;> cases chiralIso.symm j
  · exact Finset.sum_eq_zero (fun _ _ => Finset.sum_eq_zero (fun _ _ => Finset.sum_eq_zero (fun _ _ => rfl)))
  · exact Finset.sum_eq_zero (fun _ _ => Finset.sum_eq_zero (fun _ _ => Finset.sum_eq_zero (fun _ _ => rfl)))
  · exact Finset.sum_eq_zero (fun _ _ => Finset.sum_eq_zero (fun _ _ => Finset.sum_eq_zero (fun _ _ => rfl)))
  · rfl

lemma chiralProject_spin4c_sd (u : Universe) (mu : Fin 4) (p : SpacetimePoint) :
  (chiralProject (u.spin4c_connection mu p)).self_dual = u.sd_sector mu p := by
  have h := spin4c_connection_eq_embed u mu p
  rw [h]
  exact chiralProject_embed_sd _ _

lemma chiralProject_spin4c_asd (u : Universe) (mu : Fin 4) (p : SpacetimePoint) :
  (chiralProject (u.spin4c_connection mu p)).anti_self_dual = u.asd_sector mu p := by
  have h := spin4c_connection_eq_embed u mu p
  rw [h]
  exact chiralProject_embed_asd _ _

lemma bracket_spin4c (u : Universe) (mu nu : Fin 4) (x : SpacetimePoint) :
  bracket (u.spin4c_connection mu x) (u.spin4c_connection nu x) =
  embedSelfDual ⁅u.sd_sector mu x, u.sd_sector nu x⁆ +
  embedAntiSelfDual ⁅u.asd_sector mu x, u.asd_sector nu x⁆ := by
  have h1 := spin4c_connection_eq_embed u mu x
  have h2 := spin4c_connection_eq_embed u nu x
  rw [h1, h2]
  exact bracket_embed_split _ _ _ _

lemma chiralProject_bracket_spin4c_sd (u : Universe) (mu nu : Fin 4) (x : SpacetimePoint) :
  (chiralProject (bracket (u.spin4c_connection mu x) (u.spin4c_connection nu x))).self_dual =
  ⁅u.sd_sector mu x, u.sd_sector nu x⁆ := by
  rw [bracket_spin4c]
  exact chiralProject_embed_sd _ _

lemma chiralProject_bracket_spin4c_asd (u : Universe) (mu nu : Fin 4) (x : SpacetimePoint) :
  (chiralProject (bracket (u.spin4c_connection mu x) (u.spin4c_connection nu x))).anti_self_dual =
  ⁅u.asd_sector mu x, u.asd_sector nu x⁆ := by
  rw [bracket_spin4c]
  exact chiralProject_embed_asd _ _

lemma curvature_spin4c_eq (u : Universe) (mu nu : Fin 4) (x : SpacetimePoint) :
  curvature (fun m p => u.spin4c_connection m p) mu nu x =
  embedSelfDual (curvatureSl2c u.sd_sector mu nu x) +
  embedAntiSelfDual (curvatureSl2c u.asd_sector mu nu x) := by
  unfold curvature curvatureSl2c
  rw [partialDerivChiral_eq_embed_proj, partialDerivChiral_eq_embed_proj]
  
  have h_proj_nu_sd : (fun p => (chiralProject (u.spin4c_connection nu p)).self_dual) = (fun p => u.sd_sector.val nu p) := by funext p; exact chiralProject_spin4c_sd u nu p
  have h_proj_nu_asd : (fun p => (chiralProject (u.spin4c_connection nu p)).anti_self_dual) = (fun p => u.asd_sector.val nu p) := by funext p; exact chiralProject_spin4c_asd u nu p
  have h_proj_mu_sd : (fun p => (chiralProject (u.spin4c_connection mu p)).self_dual) = (fun p => u.sd_sector.val mu p) := by funext p; exact chiralProject_spin4c_sd u mu p
  have h_proj_mu_asd : (fun p => (chiralProject (u.spin4c_connection mu p)).anti_self_dual) = (fun p => u.asd_sector.val mu p) := by funext p; exact chiralProject_spin4c_asd u mu p

  rw [h_proj_nu_sd, h_proj_nu_asd, h_proj_mu_sd, h_proj_mu_asd]
  
  dsimp only
  rw [chiralProject_bracket_spin4c_sd, chiralProject_bracket_spin4c_asd]
  
  rw [embedSelfDual_add, embedSelfDual_sub]
  rw [embedAntiSelfDual_add, embedAntiSelfDual_sub]
  abel

lemma D_F_eq (u : Universe) (rho sigma nu : Fin 4) (x : SpacetimePoint) :
  partialDerivChiral rho (fun p => curvature (fun m p' => u.spin4c_connection m p') sigma nu p) x +
  bracket (u.spin4c_connection rho x) (curvature (fun m p => u.spin4c_connection m p) sigma nu x) =
  embedSelfDual (covariantDeriv u.sd_sector.val rho sigma nu x) +
  embedAntiSelfDual (covariantDeriv u.asd_sector.val rho sigma nu x) := by
  
  have h_pd : partialDerivChiral rho (fun p => curvature (fun m p' => u.spin4c_connection m p') sigma nu p) x =
              embedSelfDual (partialDerivSl2c rho (fun p => curvatureSl2c u.sd_sector.val sigma nu p) x) +
              embedAntiSelfDual (partialDerivSl2c rho (fun p => curvatureSl2c u.asd_sector.val sigma nu p) x) := by
    rw [partialDerivChiral_eq_embed_proj]
    have h_sd : (fun p => (chiralProject (curvature (fun m p' => u.spin4c_connection m p') sigma nu p)).self_dual) = 
                (fun p => curvatureSl2c u.sd_sector.val sigma nu p) := by
      funext p
      have hc : curvature (fun m p' => u.spin4c_connection m p') sigma nu p = embedSelfDual (curvatureSl2c u.sd_sector sigma nu p) + embedAntiSelfDual (curvatureSl2c u.asd_sector sigma nu p) := curvature_spin4c_eq u sigma nu p
      rw [hc, chiralProject_embed_sd]
    have h_asd : (fun p => (chiralProject (curvature (fun m p' => u.spin4c_connection m p') sigma nu p)).anti_self_dual) = 
                 (fun p => curvatureSl2c u.asd_sector.val sigma nu p) := by
      funext p
      have hc : curvature (fun m p' => u.spin4c_connection m p') sigma nu p = embedSelfDual (curvatureSl2c u.sd_sector sigma nu p) + embedAntiSelfDual (curvatureSl2c u.asd_sector sigma nu p) := curvature_spin4c_eq u sigma nu p
      rw [hc, chiralProject_embed_asd]
    rw [h_sd, h_asd]
    
  have h_br : bracket (u.spin4c_connection rho x) (curvature (fun m p => u.spin4c_connection m p) sigma nu x) =
              embedSelfDual ⁅u.sd_sector.val rho x, curvatureSl2c u.sd_sector.val sigma nu x⁆ +
              embedAntiSelfDual ⁅u.asd_sector.val rho x, curvatureSl2c u.asd_sector.val sigma nu x⁆ := by
    have h_conn : u.spin4c_connection rho x = embedSelfDual (u.sd_sector.val rho x) + embedAntiSelfDual (u.asd_sector.val rho x) := spin4c_connection_eq_embed u rho x
    have h_curv : curvature (fun m p => u.spin4c_connection m p) sigma nu x = embedSelfDual (curvatureSl2c u.sd_sector.val sigma nu x) + embedAntiSelfDual (curvatureSl2c u.asd_sector.val sigma nu x) := curvature_spin4c_eq u sigma nu x
    rw [h_conn, h_curv]
    exact bracket_embed_split _ _ _ _

  rw [h_pd, h_br]
  unfold covariantDeriv
  rw [embedSelfDual_add, embedAntiSelfDual_add]
  abel

lemma sum_add_distrib_3 (f g : Fin 4 → Fin 4 → Fin 4 → ChiralM) :
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, (f nu rho sigma + g nu rho sigma)) =
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, f nu rho sigma) + 
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, g nu rho sigma) := by
  have h1 : (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, (f nu rho sigma + g nu rho sigma)) =
            ∑ nu : Fin 4, ((∑ rho : Fin 4, ∑ sigma : Fin 4, f nu rho sigma) + (∑ rho : Fin 4, ∑ sigma : Fin 4, g nu rho sigma)) := by
    apply Finset.sum_congr rfl
    intro nu _
    have h2 : (∑ rho : Fin 4, ∑ sigma : Fin 4, (f nu rho sigma + g nu rho sigma)) =
              ∑ rho : Fin 4, ((∑ sigma : Fin 4, f nu rho sigma) + (∑ sigma : Fin 4, g nu rho sigma)) := by
      apply Finset.sum_congr rfl
      intro rho _
      exact Finset.sum_add_distrib
    rw [h2]
    exact Finset.sum_add_distrib
  rw [h1]
  exact Finset.sum_add_distrib

lemma embedSelfDual_zero : embedSelfDual (0 : SL2C) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma embedAntiSelfDual_zero : embedAntiSelfDual (0 : SL2C) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- 
Lifts the 2x2 SL(2,C) contracted Bianchi identity up to the full 4x4 ChiralM geometry. 
Since the connection splits into Self-Dual and Anti-Self-Dual blocks, the covariant derivative 
and the Bianchi identity identically split and map to zero.
-/
lemma contracted_bianchi_identity_4x4 (u : Universe) (mu : Fin 4) (x : SpacetimePoint) :
  (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    CGD.Gravity.epsilon4 mu nu rho sigma • (
      partialDerivChiral rho (fun p => curvature (fun m p' => u.spin4c_connection m p') sigma nu p) x +
      bracket (u.spin4c_connection rho x) (curvature (fun m p => u.spin4c_connection m p) sigma nu x)
    )) = 0 := by
  
  have h_inner_eq : 
    (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      CGD.Gravity.epsilon4 mu nu rho sigma • (
        partialDerivChiral rho (fun p => curvature (fun m p' => u.spin4c_connection m p') sigma nu p) x +
        bracket (u.spin4c_connection rho x) (curvature (fun m p => u.spin4c_connection m p) sigma nu x)
      )) = 
    (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      CGD.Gravity.epsilon4 mu nu rho sigma • (
        embedSelfDual (covariantDeriv u.sd_sector.val rho sigma nu x) + 
        embedAntiSelfDual (covariantDeriv u.asd_sector.val rho sigma nu x)
      )) := by
    apply Finset.sum_congr rfl; intro nu _
    apply Finset.sum_congr rfl; intro rho _
    apply Finset.sum_congr rfl; intro sigma _
    rw [D_F_eq u rho sigma nu x]

  rw [h_inner_eq]

  have h_smul_distrib : 
    (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      CGD.Gravity.epsilon4 mu nu rho sigma • (
        embedSelfDual (covariantDeriv u.sd_sector.val rho sigma nu x) + 
        embedAntiSelfDual (covariantDeriv u.asd_sector.val rho sigma nu x)
      )) =
    (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
      (CGD.Gravity.epsilon4 mu nu rho sigma • embedSelfDual (covariantDeriv u.sd_sector.val rho sigma nu x) + 
       CGD.Gravity.epsilon4 mu nu rho sigma • embedAntiSelfDual (covariantDeriv u.asd_sector.val rho sigma nu x))) := by
    apply Finset.sum_congr rfl; intro nu _
    apply Finset.sum_congr rfl; intro rho _
    apply Finset.sum_congr rfl; intro sigma _
    exact smul_add (CGD.Gravity.epsilon4 mu nu rho sigma) _ _

  rw [h_smul_distrib]

  have h_sum_split := sum_add_distrib_3 
    (fun nu rho sigma => CGD.Gravity.epsilon4 mu nu rho sigma • embedSelfDual (covariantDeriv u.sd_sector.val rho sigma nu x))
    (fun nu rho sigma => CGD.Gravity.epsilon4 mu nu rho sigma • embedAntiSelfDual (covariantDeriv u.asd_sector.val rho sigma nu x))
  
  rw [h_sum_split]

  have h_pull_sd : 
    (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • embedSelfDual (covariantDeriv u.sd_sector.val rho sigma nu x)) =
    (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, embedSelfDual (CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv u.sd_sector.val rho sigma nu x)) := by
    apply Finset.sum_congr rfl; intro nu _
    apply Finset.sum_congr rfl; intro rho _
    apply Finset.sum_congr rfl; intro sigma _
    exact embedSelfDual_smul (CGD.Gravity.epsilon4 mu nu rho sigma) _
    
  have h_pull_asd : 
    (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • embedAntiSelfDual (covariantDeriv u.asd_sector.val rho sigma nu x)) =
    (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, embedAntiSelfDual (CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv u.asd_sector.val rho sigma nu x)) := by
    apply Finset.sum_congr rfl; intro nu _
    apply Finset.sum_congr rfl; intro rho _
    apply Finset.sum_congr rfl; intro sigma _
    exact embedAntiSelfDual_smul (CGD.Gravity.epsilon4 mu nu rho sigma) _

  rw [h_pull_sd, h_pull_asd]

  have h_sum_sd_3 : 
    (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, embedSelfDual (CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv u.sd_sector.val rho sigma nu x)) =
    embedSelfDual (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv u.sd_sector.val rho sigma nu x) := by
    exact sum_embedSelfDual_3 _
    
  have h_sum_asd_3 : 
    (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, embedAntiSelfDual (CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv u.asd_sector.val rho sigma nu x)) =
    embedAntiSelfDual (∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, CGD.Gravity.epsilon4 mu nu rho sigma • covariantDeriv u.asd_sector.val rho sigma nu x) := by
    exact sum_embedAntiSelfDual_3 _
    
  rw [h_sum_sd_3, h_sum_asd_3]

  have h_sd_zero := contracted_bianchi_identity u.sd_sector mu x
  have h_asd_zero := contracted_bianchi_identity u.asd_sector mu x
  
  rw [h_sd_zero, h_asd_zero]

  rw [embedSelfDual_zero, embedAntiSelfDual_zero]
  exact add_zero 0

/--
A rigorous bridge mapping the 1D Gâteaux temporal derivative natively to the Fréchet directional derivative.
-/
lemma fderiv_slice_t (f : ℝ × SpacetimePoint → ℂ) (t : ℝ) (p : SpacetimePoint)
  (hf : DifferentiableAt ℝ f (t, p)) :
  deriv (fun s => f (s, p)) t = fderiv ℝ f (t, p) (1, 0) := by
  let L1 := ContinuousLinearMap.id ℝ ℝ
  let L2 := (0 : ℝ →L[ℝ] SpacetimePoint)
  let L := ContinuousLinearMap.prod L1 L2
  let c : ℝ × SpacetimePoint := (0, p)
  let g : ℝ → ℝ × SpacetimePoint := fun s => L s + c
  
  have hg_eq : (fun s => f (s, p)) = f ∘ g := by
    ext s
    have h_gs : (s, p) = g s := by
      apply Prod.ext
      · change s = s + 0; exact Eq.symm (add_zero s)
      · change p = 0 + p; exact Eq.symm (zero_add p)
    exact congrArg f h_gs
    
  have hd_L : HasFDerivAt L L t := ContinuousLinearMap.hasFDerivAt L
  have hd_c : HasFDerivAt (fun _ : ℝ => c) (0 : ℝ →L[ℝ] (ℝ × SpacetimePoint)) t := hasFDerivAt_const c t
  have hd_g : HasFDerivAt g (L + 0) t := HasFDerivAt.add hd_L hd_c
  
  have heq_L : L + 0 = L := add_zero L
  have hd_g_L : HasFDerivAt g L t := by
    rw [← heq_L]
    exact hd_g
    
  have h_g_t : g t = (t, p) := by
    apply Prod.ext
    · change t + 0 = t; exact add_zero t
    · change 0 + p = p; exact zero_add p
    
  have hf_g : DifferentiableAt ℝ f (g t) := by
    rw [h_g_t]
    exact hf
    
  have h_comp := HasFDerivAt.comp t hf_g.hasFDerivAt hd_g_L
  
  have h_fderiv : fderiv ℝ (f ∘ g) t = (fderiv ℝ f (g t)).comp L := h_comp.fderiv
  
  have h_deriv : deriv (fun s => f (s, p)) t = fderiv ℝ (fun s => f (s, p)) t 1 := rfl
  rw [h_deriv, hg_eq, h_fderiv]
  
  have h_L_1 : L 1 = (1, 0) := rfl
  
  change (fderiv ℝ f (g t)) (L 1) = _
  rw [h_g_t, h_L_1]

/--
A rigorous bridge mapping the 1D spatial partial derivative natively to the Fréchet directional derivative.
-/
lemma fderiv_slice_x (f : ℝ × SpacetimePoint → ℂ) (t : ℝ) (p : SpacetimePoint) (mu : Fin 4)
  (hf : DifferentiableAt ℝ f (t, p)) :
  partialDeriv mu (fun p' => f (t, p')) p = fderiv ℝ f (t, p) (0, Pi.single mu 1) := by
  unfold partialDeriv
  let v : SpacetimePoint := Pi.single mu 1
  
  let L1 := (0 : SpacetimePoint →L[ℝ] ℝ)
  let L2 := ContinuousLinearMap.id ℝ SpacetimePoint
  let L := ContinuousLinearMap.prod L1 L2
  let c : ℝ × SpacetimePoint := (t, 0)
  let g : SpacetimePoint → ℝ × SpacetimePoint := fun p' => L p' + c
  
  have hg_eq : (fun p' => f (t, p')) = f ∘ g := by
    ext p'
    have h_gp : (t, p') = g p' := by
      apply Prod.ext
      · change t = 0 + t; exact Eq.symm (zero_add t)
      · change p' = p' + 0; exact Eq.symm (add_zero p')
    exact congrArg f h_gp
    
  have hd_L : HasFDerivAt L L p := ContinuousLinearMap.hasFDerivAt L
  have hd_c : HasFDerivAt (fun _ : SpacetimePoint => c) (0 : SpacetimePoint →L[ℝ] (ℝ × SpacetimePoint)) p := hasFDerivAt_const c p
  have hd_g : HasFDerivAt g (L + 0) p := HasFDerivAt.add hd_L hd_c
  
  have heq_L : L + 0 = L := add_zero L
  have hd_g_L : HasFDerivAt g L p := by
    rw [← heq_L]
    exact hd_g
    
  have h_g_p : g p = (t, p) := by
    apply Prod.ext
    · change 0 + t = t; exact zero_add t
    · change p + 0 = p; exact add_zero p
    
  have hf_g : DifferentiableAt ℝ f (g p) := by
    rw [h_g_p]
    exact hf
    
  have h_comp := HasFDerivAt.comp p hf_g.hasFDerivAt hd_g_L
  
  have h_fderiv : fderiv ℝ (f ∘ g) p = (fderiv ℝ f (g p)).comp L := h_comp.fderiv
  
  rw [← hg_eq] at h_fderiv
  
  have h_eval : fderiv ℝ (fun p' => f (t, p')) p v = ((fderiv ℝ f (g p)).comp L) v := by rw [h_fderiv]
  
  have h_L_v : L v = (0, v) := rfl
  
  change fderiv ℝ (fun p' => f (t, p')) p v = fderiv ℝ f (g p) (L v) at h_eval
  rw [h_g_p, h_L_v] at h_eval
  exact h_eval

/--
Proves that spatial and temporal derivatives commute flawlessly for infinitely smooth functions 
over the joint ℝ × SpacetimePoint manifold, by reducing them into Fréchet directional derivatives
and applying Mathlib's core symmetric second derivative theorem.
-/
lemma mixed_deriv_commute (f : ℝ × SpacetimePoint → ℂ) (t : ℝ) (mu : Fin 4) (x : SpacetimePoint)
  (h_smooth : ContDiff ℝ ⊤ f) :
  deriv (fun s => partialDeriv mu (fun p => f (s, p)) x) t =
  partialDeriv mu (fun p => deriv (fun s => f (s, p)) t) x := by
  let y : ℝ × SpacetimePoint := (t, x)
  let v_t : ℝ × SpacetimePoint := (1, 0)
  let v_x : ℝ × SpacetimePoint := (0, Pi.single mu 1)

  have h_diff : Differentiable ℝ f := ContDiff.differentiable h_smooth (by decide)
  have h_deriv_smooth : ContDiff ℝ 1 (fderiv ℝ f) := ContDiff.fderiv_right h_smooth (by decide)
  have h_diff_deriv : DifferentiableAt ℝ (fderiv ℝ f) y := ContDiff.differentiable h_deriv_smooth (by decide) y
  have h_hasFDeriv : ∀ y', HasFDerivAt f (fderiv ℝ f y') y' := fun y' => (h_diff y').hasFDerivAt
  
  have h_symm := second_derivative_symmetric h_hasFDeriv h_diff_deriv.hasFDerivAt v_t v_x

  let G : ℝ × SpacetimePoint → ℂ := fun p' => fderiv ℝ f p' v_x
  
  have h_G_eq : ∀ s, partialDeriv mu (fun p => f (s, p)) x = G (s, x) := by
    intro s
    exact fderiv_slice_x f s x mu (h_diff (s, x))
    
  have h_LHS_eq : (fun s => partialDeriv mu (fun p => f (s, p)) x) = (fun s => G (s, x)) := by
    ext s
    exact h_G_eq s
  
  have h_LHS : deriv (fun s => partialDeriv mu (fun p => f (s, p)) x) t = deriv (fun s => G (s, x)) t := by
    rw [h_LHS_eq]

  let L : (ℝ × SpacetimePoint →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ v_x
  
  have h_L_has : HasFDerivAt L L (fderiv ℝ f y) := ContinuousLinearMap.hasFDerivAt L
  have h_comp2 := HasFDerivAt.comp y h_L_has h_diff_deriv.hasFDerivAt
  have h_G_diff : DifferentiableAt ℝ G y := h_comp2.differentiableAt
  
  have h_deriv_G : deriv (fun s => G (s, x)) t = fderiv ℝ G y v_t := fderiv_slice_t G t x h_G_diff
  
  have h_fderiv_G : fderiv ℝ G y = L.comp (fderiv ℝ (fderiv ℝ f) y) := h_comp2.fderiv
    
  have h_LHS_final : deriv (fun s => partialDeriv mu (fun p => f (s, p)) x) t = fderiv ℝ (fderiv ℝ f) y v_t v_x := by
    rw [h_LHS, h_deriv_G, h_fderiv_G]
    rfl

  let H : ℝ × SpacetimePoint → ℂ := fun p' => fderiv ℝ f p' v_t
  
  have h_H_eq : ∀ p, deriv (fun s => f (s, p)) t = H (t, p) := by
    intro p
    exact fderiv_slice_t f t p (h_diff (t, p))
    
  have h_RHS_eq : (fun p => deriv (fun s => f (s, p)) t) = (fun p => H (t, p)) := by
    ext p
    exact h_H_eq p
    
  have h_RHS : partialDeriv mu (fun p => deriv (fun s => f (s, p)) t) x = partialDeriv mu (fun p => H (t, p)) x := by
    rw [h_RHS_eq]

  let L2 : (ℝ × SpacetimePoint →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ v_t
  
  have h_L2_has : HasFDerivAt L2 L2 (fderiv ℝ f y) := ContinuousLinearMap.hasFDerivAt L2
  have h_comp3 := HasFDerivAt.comp y h_L2_has h_diff_deriv.hasFDerivAt
  have h_H_diff : DifferentiableAt ℝ H y := h_comp3.differentiableAt
  
  have h_deriv_H : partialDeriv mu (fun p => H (t, p)) x = fderiv ℝ H y v_x := fderiv_slice_x H t x mu h_H_diff
  
  have h_fderiv_H : fderiv ℝ H y = L2.comp (fderiv ℝ (fderiv ℝ f) y) := h_comp3.fderiv
    
  have h_RHS_final : partialDeriv mu (fun p => deriv (fun s => f (s, p)) t) x = fderiv ℝ (fderiv ℝ f) y v_x v_t := by
    rw [h_RHS, h_deriv_H, h_fderiv_H]
    rfl

  rw [h_LHS_final, h_RHS_final]
  exact h_symm

end CGD.Foundations

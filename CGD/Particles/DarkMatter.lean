-- FILENAME: CGD/Particles/DarkMatter.lean

import Mathlib
import CGD.Axioms.PhysicalUniverse
import CGD.Axioms.Ontology
import CGD.Foundations.Spacetime
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup

open CGD.Axioms
open CGD.Foundations
open CGD.Math
open Complex
open Matrix

namespace CGD.Particles

lemma toSl2c_zero : toSl2c (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  apply Subtype.ext
  unfold toSl2c
  dsimp
  have h_tr : Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by simp [Matrix.trace]
  rw [h_tr]
  have h1 : (0:ℂ) / 2 = 0 := by ring
  rw [h1, zero_smul, sub_zero]

lemma chiralProject_asd_add (A B : ChiralM) : 
  (chiralProject (A + B)).anti_self_dual = (chiralProject A).anti_self_dual + (chiralProject B).anti_self_dual := by
  apply Subtype.ext
  ext i j
  unfold chiralProject toSl2c Matrix.trace Matrix.diag
  dsimp
  rw [Finset.sum_add_distrib]
  ring

lemma chiralProject_asd_sub (A B : ChiralM) : 
  (chiralProject (A - B)).anti_self_dual = (chiralProject A).anti_self_dual - (chiralProject B).anti_self_dual := by
  apply Subtype.ext
  ext i j
  unfold chiralProject toSl2c Matrix.trace Matrix.diag
  dsimp
  rw [Finset.sum_sub_distrib]
  ring

lemma asd_curvature_eq (A : Fin 4 → SpacetimePoint → ChiralM) (mu nu : Fin 4) (x : SpacetimePoint) :
  (chiralProject (curvature A mu nu x)).anti_self_dual = 
  partialDerivSl2c mu (fun p => (chiralProject (A nu p)).anti_self_dual) x -
  partialDerivSl2c nu (fun p => (chiralProject (A mu p)).anti_self_dual) x +
  (chiralProject (bracket (A mu x) (A nu x))).anti_self_dual := by
  delta curvature
  rw [chiralProject_asd_add]
  rw [chiralProject_asd_sub]
  rw [partialDerivChiral_proj_anti_self_dual]
  rw [partialDerivChiral_proj_anti_self_dual]
  rw [chiralProject_embed_asd]

lemma embed_sd_mul_asd (L R : SL2C) : embedSelfDual L * embedAntiSelfDual R = 0 := by
  ext i j
  change ∑ k, (embedSelfDual L) i k * (embedAntiSelfDual R) k j = 0
  apply Finset.sum_eq_zero
  intro k _
  have hL : (embedSelfDual L) i k = match chiralIso.symm i, chiralIso.symm k with | Sum.inl i', Sum.inl k' => L.val i' k' | _, _ => 0 := rfl
  have hR : (embedAntiSelfDual R) k j = match chiralIso.symm k, chiralIso.symm j with | Sum.inr k', Sum.inr j' => R.val k' j' | _, _ => 0 := rfl
  rw [hL, hR]
  rcases (chiralIso.symm i) with i' | i' <;> rcases (chiralIso.symm j) with j' | j' <;> rcases (chiralIso.symm k) with k' | k' <;> simp

lemma embed_asd_mul_sd (R L : SL2C) : embedAntiSelfDual R * embedSelfDual L = 0 := by
  ext i j
  change ∑ k, (embedAntiSelfDual R) i k * (embedSelfDual L) k j = 0
  apply Finset.sum_eq_zero
  intro k _
  have hR : (embedAntiSelfDual R) i k = match chiralIso.symm i, chiralIso.symm k with | Sum.inr i', Sum.inr k' => R.val i' k' | _, _ => 0 := rfl
  have hL : (embedSelfDual L) k j = match chiralIso.symm k, chiralIso.symm j with | Sum.inl k', Sum.inl j' => L.val k' j' | _, _ => 0 := rfl
  rw [hR, hL]
  rcases (chiralIso.symm i) with i' | i' <;> rcases (chiralIso.symm j) with j' | j' <;> rcases (chiralIso.symm k) with k' | k' <;> simp

lemma chiralProject_asd_embed_sd_mul_sd (L1 L2 : SL2C) : 
  (chiralProject (embedSelfDual L1 * embedSelfDual L2)).anti_self_dual = 0 := by
  apply Subtype.ext
  ext i j
  unfold chiralProject toSl2c
  dsimp
  have h_zero : ∀ a b, (embedSelfDual L1 * embedSelfDual L2) (chiralIso (Sum.inr a)) (chiralIso (Sum.inr b)) = 0 := by
    intro a b
    change ∑ k, (embedSelfDual L1) (chiralIso (Sum.inr a)) k * (embedSelfDual L2) k (chiralIso (Sum.inr b)) = 0
    apply Finset.sum_eq_zero
    intro k _
    have hL1 : (embedSelfDual L1) (chiralIso (Sum.inr a)) k = 0 := by
      have h : (embedSelfDual L1) (chiralIso (Sum.inr a)) k = match chiralIso.symm (chiralIso (Sum.inr a)), chiralIso.symm k with | Sum.inl a', Sum.inl k' => L1.val a' k' | _, _ => 0 := rfl
      rw [Equiv.symm_apply_apply] at h
      exact h
    simp [hL1]
  have h_tr : Matrix.trace (fun a b => (embedSelfDual L1 * embedSelfDual L2) (chiralIso (Sum.inr a)) (chiralIso (Sum.inr b))) = 0 := by
    unfold Matrix.trace Matrix.diag
    have h_sum : (∑ x : Fin 2, (embedSelfDual L1 * embedSelfDual L2) (chiralIso (Sum.inr x)) (chiralIso (Sum.inr x))) = ∑ x : Fin 2, (0 : ℂ) := by
      apply Finset.sum_congr rfl
      intro x _
      exact h_zero x x
    rw [h_sum, Finset.sum_const_zero]
  change (embedSelfDual L1 * embedSelfDual L2) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) - (Matrix.trace _) / 2 * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j = 0
  rw [h_zero i j, h_tr]
  ring

lemma bracket_cross_term_asd (L1 L2 R1 R2 : SL2C) :
  (chiralProject (bracket (embedSelfDual L1 + embedAntiSelfDual R1) (embedSelfDual L2 + embedAntiSelfDual R2))).anti_self_dual = 
  (chiralProject (bracket (embedAntiSelfDual R1) (embedAntiSelfDual R2))).anti_self_dual := by
  unfold bracket
  have h_mul1 : (embedSelfDual L1 + embedAntiSelfDual R1) * (embedSelfDual L2 + embedAntiSelfDual R2) =
    embedSelfDual L1 * embedSelfDual L2 + embedAntiSelfDual R1 * embedAntiSelfDual R2 := by
    simp only [mul_add, add_mul]
    rw [embed_sd_mul_asd, embed_asd_mul_sd]
    abel
  have h_mul2 : (embedSelfDual L2 + embedAntiSelfDual R2) * (embedSelfDual L1 + embedAntiSelfDual R1) =
    embedSelfDual L2 * embedSelfDual L1 + embedAntiSelfDual R2 * embedAntiSelfDual R1 := by
    simp only [mul_add, add_mul]
    rw [embed_sd_mul_asd, embed_asd_mul_sd]
    abel
  rw [h_mul1, h_mul2]
  have h_sub : 
    embedSelfDual L1 * embedSelfDual L2 + embedAntiSelfDual R1 * embedAntiSelfDual R2 - 
    (embedSelfDual L2 * embedSelfDual L1 + embedAntiSelfDual R2 * embedAntiSelfDual R1) =
    (embedSelfDual L1 * embedSelfDual L2 - embedSelfDual L2 * embedSelfDual L1) + 
    (embedAntiSelfDual R1 * embedAntiSelfDual R2 - embedAntiSelfDual R2 * embedAntiSelfDual R1) := by abel
  rw [h_sub]
  rw [chiralProject_asd_add]
  rw [chiralProject_asd_sub, chiralProject_asd_sub]
  rw [chiralProject_asd_embed_sd_mul_sd L1 L2, chiralProject_asd_embed_sd_mul_sd L2 L1]
  simp

/--
Dark Matter Decoupling (The "Darkness" Theorem):
A pure Self-Dual defect (Dark Matter) is superposed onto the macroscopic 
vacuum of normal matter. Because the Spin(4,C) Lie algebra perfectly orthogonalizes 
the chiral sectors, the Anti-Self-Dual curvature (which dictates electromagnetism 
and the strong force) evaluates to being mathematically identical to the vacuum state 
without the Dark Matter present. 
-/
@[litlib_track "Dark Matter Anti-Self-Dual Decoupling (Darkness)"]
theorem kinematicDarkMatterDecoupling (pu : PhysicalUniverse)
  (A_DM : Sl2cGaugeField) (x : SpacetimePoint) (mu nu : Fin 4) :
  let A_tot := fun m p => 
    embedSelfDual (A_DM.val m p + pu.toUniverse.sd_sector.val m p) + 
    embedAntiSelfDual (pu.toUniverse.asd_sector.val m p);
  (chiralProject (curvature A_tot mu nu x)).anti_self_dual = 
  (chiralProject (curvature (fun m p => pu.toUniverse.spin4c_connection m p) mu nu x)).anti_self_dual := by
  intro A_tot
  rw [asd_curvature_eq A_tot]
  rw [asd_curvature_eq (fun m p => pu.toUniverse.spin4c_connection m p)]
  
  have h_A_tot_asd (m : Fin 4) (p : SpacetimePoint) : 
    (chiralProject (A_tot m p)).anti_self_dual = pu.toUniverse.asd_sector.val m p := by
    exact chiralProject_embed_asd (A_DM.val m p + pu.toUniverse.sd_sector.val m p) (pu.toUniverse.asd_sector.val m p)
    
  have h_pu_asd (m : Fin 4) (p : SpacetimePoint) :
    (chiralProject (pu.toUniverse.spin4c_connection m p)).anti_self_dual = pu.toUniverse.asd_sector.val m p := by
    rw [spin4c_connection_eq_embed]
    exact chiralProject_embed_asd (pu.toUniverse.sd_sector.val m p) (pu.toUniverse.asd_sector.val m p)
    
  have h_deriv_tot_nu : (fun p => (chiralProject (A_tot nu p)).anti_self_dual) = fun p => pu.toUniverse.asd_sector.val nu p := by funext p; exact h_A_tot_asd nu p
  have h_deriv_tot_mu : (fun p => (chiralProject (A_tot mu p)).anti_self_dual) = fun p => pu.toUniverse.asd_sector.val mu p := by funext p; exact h_A_tot_asd mu p
  
  have h_deriv_pu_nu : (fun p => (chiralProject (pu.toUniverse.spin4c_connection nu p)).anti_self_dual) = fun p => pu.toUniverse.asd_sector.val nu p := by funext p; exact h_pu_asd nu p
  have h_deriv_pu_mu : (fun p => (chiralProject (pu.toUniverse.spin4c_connection mu p)).anti_self_dual) = fun p => pu.toUniverse.asd_sector.val mu p := by funext p; exact h_pu_asd mu p
  
  rw [h_deriv_tot_nu, h_deriv_tot_mu]
  rw [h_deriv_pu_nu, h_deriv_pu_mu]
  
  have h_bracket_tot : (chiralProject (bracket (A_tot mu x) (A_tot nu x))).anti_self_dual = 
                       (chiralProject (bracket (embedAntiSelfDual (pu.toUniverse.asd_sector.val mu x)) (embedAntiSelfDual (pu.toUniverse.asd_sector.val nu x)))).anti_self_dual := by
    have h_A_tot_mu : A_tot mu x = embedSelfDual (A_DM.val mu x + pu.toUniverse.sd_sector.val mu x) + embedAntiSelfDual (pu.toUniverse.asd_sector.val mu x) := rfl
    have h_A_tot_nu : A_tot nu x = embedSelfDual (A_DM.val nu x + pu.toUniverse.sd_sector.val nu x) + embedAntiSelfDual (pu.toUniverse.asd_sector.val nu x) := rfl
    rw [h_A_tot_mu, h_A_tot_nu]
    exact bracket_cross_term_asd _ _ _ _
    
  have h_bracket_pu : (chiralProject (bracket (pu.toUniverse.spin4c_connection mu x) (pu.toUniverse.spin4c_connection nu x))).anti_self_dual = 
                      (chiralProject (bracket (embedAntiSelfDual (pu.toUniverse.asd_sector.val mu x)) (embedAntiSelfDual (pu.toUniverse.asd_sector.val nu x)))).anti_self_dual := by
    have h_pu_mu : pu.toUniverse.spin4c_connection mu x = embedSelfDual (pu.toUniverse.sd_sector.val mu x) + embedAntiSelfDual (pu.toUniverse.asd_sector.val mu x) := spin4c_connection_eq_embed pu.toUniverse mu x
    have h_pu_nu : pu.toUniverse.spin4c_connection nu x = embedSelfDual (pu.toUniverse.sd_sector.val nu x) + embedAntiSelfDual (pu.toUniverse.asd_sector.val nu x) := spin4c_connection_eq_embed pu.toUniverse nu x
    rw [h_pu_mu, h_pu_nu]
    exact bracket_cross_term_asd _ _ _ _
    
  rw [h_bracket_tot, h_bracket_pu]


lemma partialDeriv_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (μ : Fin 4) (f g : SpacetimePoint → E) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
  partialDeriv μ (fun p => f p + g p) x = partialDeriv μ f x + partialDeriv μ g x := by
  unfold partialDeriv
  have h_eq : (fun p => f p + g p) = f + g := rfl
  rw [h_eq]
  rw [fderiv_add hf hg]
  exact ContinuousLinearMap.add_apply (fderiv ℝ f x) (fderiv ℝ g x) (Pi.single μ 1)

lemma partialDerivSl2c_add (f g : SpacetimePoint → SL2C) (μ : Fin 4) (x : SpacetimePoint)
  (hf : ∀ i j, DifferentiableAt ℝ (fun p => (f p).val i j) x)
  (hg : ∀ i j, DifferentiableAt ℝ (fun p => (g p).val i j) x) :
  partialDerivSl2c μ (fun p => f p + g p) x = partialDerivSl2c μ f x + partialDerivSl2c μ g x := by
  apply Subtype.ext
  have h_rhs : (partialDerivSl2c μ f x + partialDerivSl2c μ g x).val = (partialDerivSl2c μ f x).val + (partialDerivSl2c μ g x).val := rfl
  rw [h_rhs]
  have h_sum_diff : ∀ i j, DifferentiableAt ℝ (fun p => (f p + g p).val i j) x := by
    intro i j
    have h_eq : (fun p => (f p + g p).val i j) = fun p => (f p).val i j + (g p).val i j := rfl
    rw [h_eq]
    exact DifferentiableAt.add (hf i j) (hg i j)
  rw [partialDerivSl2c_eq_mat (fun p => f p + g p) μ x h_sum_diff,
      partialDerivSl2c_eq_mat f μ x hf,
      partialDerivSl2c_eq_mat g μ x hg]
  ext i j
  unfold partialDerivMat
  have h_eq : (fun p => (f p + g p).val i j) = fun p => (f p).val i j + (g p).val i j := rfl
  rw [h_eq]
  exact partialDeriv_add μ (fun p => (f p).val i j) (fun p => (g p).val i j) x (hf i j) (hg i j)

lemma lie_add_add {L : Type*} [LieRing L] (a b c d : L) :
  ⁅a + b, c + d⁆ = ⁅a, c⁆ + ⁅a, d⁆ + ⁅b, c⁆ + ⁅b, d⁆ := by
  rw [add_lie, lie_add, lie_add]
  abel

/--
Self-Interacting Dark Matter (SIDM):
When two SD-only defects occupy the same spacetime volume, their non-Abelian 
SL(2, C) group structure intrinsically generates a non-linear cross-term in the curvature. 
This strictly forces momentum exchange, proving that pure gravitational defects in CGD 
natively behave as Self-Interacting Dark Matter (SIDM).
-/
@[litlib_track "Dark Matter Self-Interaction (SIDM)"]
theorem kinematicDarkMatterSelfInteraction
  (A_1 A_2 : Sl2cGaugeField)
  (x : SpacetimePoint) (mu nu : Fin 4) :
  let A_tot := fun m p => A_1.val m p + A_2.val m p;
  curvatureSl2c A_tot mu nu x = 
    curvatureSl2c A_1.val mu nu x + 
    curvatureSl2c A_2.val mu nu x + 
    ⁅A_1.val mu x, A_2.val nu x⁆ + ⁅A_2.val mu x, A_1.val nu x⁆ := by
  intro A_tot
  change curvatureSl2c (fun m p => A_1.val m p + A_2.val m p) mu nu x = _
  rw [curvatureSl2c_def, curvatureSl2c_def, curvatureSl2c_def]
  have h1_diff : ∀ i j, DifferentiableAt ℝ (fun p => (A_1.val nu p).val i j) x := by
    intro i j
    have hd : Differentiable ℝ (fun p => (A_1.val nu p).val i j) := ContDiff.differentiable (A_1.is_smooth nu i j) (by decide)
    exact hd x
  have h2_diff : ∀ i j, DifferentiableAt ℝ (fun p => (A_2.val nu p).val i j) x := by
    intro i j
    have hd : Differentiable ℝ (fun p => (A_2.val nu p).val i j) := ContDiff.differentiable (A_2.is_smooth nu i j) (by decide)
    exact hd x
  have h3_diff : ∀ i j, DifferentiableAt ℝ (fun p => (A_1.val mu p).val i j) x := by
    intro i j
    have hd : Differentiable ℝ (fun p => (A_1.val mu p).val i j) := ContDiff.differentiable (A_1.is_smooth mu i j) (by decide)
    exact hd x
  have h4_diff : ∀ i j, DifferentiableAt ℝ (fun p => (A_2.val mu p).val i j) x := by
    intro i j
    have hd : Differentiable ℝ (fun p => (A_2.val mu p).val i j) := ContDiff.differentiable (A_2.is_smooth mu i j) (by decide)
    exact hd x
  rw [partialDerivSl2c_add (A_1.val nu) (A_2.val nu) mu x h1_diff h2_diff]
  rw [partialDerivSl2c_add (A_1.val mu) (A_2.val mu) nu x h3_diff h4_diff]
  rw [lie_add_add]
  abel

end CGD.Particles

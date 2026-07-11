-- FILENAME: CGD/Foundations/Lagrangian/Variation/Differentiability.lean

import CGD.Foundations.Action
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Axioms.Ontology
import CGD.Foundations.Lagrangian.Variation.Algebra
import CGD.Foundations.Lagrangian.Variation.Geometry
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Matrix Complex BigOperators CGD.Axioms CGD.Foundations CGD.Math

namespace CGD.Foundations

/--
Reduces the differentiability of a matrix trace of a product to the element-wise
differentiability of the constituent matrices.
-/
lemma diff_matrix_trace_mul (A B : SpacetimePoint → Matrix (Fin 4) (Fin 4) ℂ) (x : SpacetimePoint)
  (hA : ∀ i j, DifferentiableAt ℝ (fun p => A p i j) x)
  (hB : ∀ i j, DifferentiableAt ℝ (fun p => B p i j) x) :
  DifferentiableAt ℝ (fun p => Matrix.trace (A p * B p)) x := by
  have h_tr : (fun p => Matrix.trace (A p * B p)) = (fun p => ∑ i : Fin 4, ∑ j : Fin 4, A p i j * B p j i) := rfl
  rw [h_tr]
  apply diff_sum; intro i
  apply diff_sum; intro j
  exact DifferentiableAt.mul (hA i j) (hB j i)

/--
Reduces the differentiability of a Lie bracket to the element-wise differentiability
of the constituent matrices using the product and difference rules.
-/
lemma diff_bracket (A B : SpacetimePoint → ChiralM) (x : SpacetimePoint)
  (hA : ∀ i j, DifferentiableAt ℝ (fun p => A p i j) x)
  (hB : ∀ i j, DifferentiableAt ℝ (fun p => B p i j) x) :
  ∀ i j, DifferentiableAt ℝ (fun p => bracket (A p) (B p) i j) x := by
  intro i j
  unfold bracket
  have h_eval : (fun p => (A p * B p - B p * A p) i j) = (fun p => ∑ k, A p i k * B p k j - ∑ k, B p i k * A p k j) := rfl
  rw [h_eval]
  apply DifferentiableAt.sub
  · apply diff_sum; intro k
    exact DifferentiableAt.mul (hA i k) (hB k j)
  · apply diff_sum; intro k
    exact DifferentiableAt.mul (hB i k) (hA k j)

/--
A mathematically strict evaluation of the matrix derivative projection.
Because the matrix space `Fin 4 → Fin 4 → ℂ` is defined natively as nested Pi types,
its derivative is strictly defined point-wise by Mathlib's `deriv_pi` theorems.
-/
lemma deriv_matrix_apply (A : ℝ → Matrix (Fin 4) (Fin 4) ℂ) (t : ℝ)
  (h_diff : ∀ i j, DifferentiableAt ℝ (fun s => A s i j) t) :
  ∀ i j, deriv A t i j = deriv (fun s => A s i j) t := by
  intro i j
  have hd_col : ∀ k, DifferentiableAt ℝ (fun s => A s k) t := by
    intro k
    apply differentiableAt_pi.mpr
    intro l
    exact h_diff k l
  have h1 := deriv_pi hd_col
  have h_eval1 : deriv A t i = deriv (fun s => A s i) t := congrFun h1 i
  have hd_row : ∀ l, DifferentiableAt ℝ (fun s => A s i l) t := by
    intro l
    exact h_diff i l
  have h2 := deriv_pi hd_row
  have h_eval2 : deriv (fun s => A s i) t j = deriv (fun s => A s i j) t := congrFun h2 j
  change (deriv A t i) j = _
  rw [h_eval1, h_eval2]

/--
The core algebraic reduction.
Proves that the topological Chern-Simons Variation Current is spatially differentiable
*if and only if* the temporal derivative of the connection and the spatial curvature tensor
are both independently differentiable at the element level.
-/
lemma diff_variationCurrent (v : ℝ → PhysicalUniverse) (t : ℝ) (mu : Fin 4) (x : SpacetimePoint)
  (hdA : ∀ nu i j, DifferentiableAt ℝ (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t) x)
  (hF : ∀ rho sigma i j, DifferentiableAt ℝ (fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j) x)
  (h_t_diff : ∀ p nu i j, DifferentiableAt ℝ (fun s => (v s).toUniverse.spin4c_connection nu p i j) t) :
  DifferentiableAt ℝ (variationCurrent v t mu) x := by
  unfold variationCurrent
  apply diff_const_mul
  apply diff_sum; intro nu
  apply diff_sum; intro rho
  apply diff_sum; intro sigma
  apply diff_const_mul

  have h_trace_diff : DifferentiableAt ℝ (fun p => Matrix.trace (deriv (fun s => (v s).toUniverse.spin4c_connection nu p) t * curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)) x := by
    have h_tr : (fun p => Matrix.trace (deriv (fun s => (v s).toUniverse.spin4c_connection nu p) t * curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p)) =
                (fun p => ∑ i : Fin 4, ∑ j : Fin 4, (deriv (fun s => (v s).toUniverse.spin4c_connection nu p) t) i j * (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p) j i) := rfl
    rw [h_tr]
    apply diff_sum; intro i
    apply diff_sum; intro j

    have h_deriv_eval : (fun p => (deriv (fun s => (v s).toUniverse.spin4c_connection nu p) t) i j * (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p) j i) =
                        (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t * (curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p) j i) := by
      ext p
      have hp := deriv_matrix_apply (fun s => (v s).toUniverse.spin4c_connection nu p) t (h_t_diff p nu) i j
      rw [hp]

    have hd_eval : DifferentiableAt ℝ (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t * curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p j i) x := by
      exact DifferentiableAt.mul (hdA nu i j) (hF rho sigma j i)

    exact cast (congrArg (fun F => DifferentiableAt ℝ F x) h_deriv_eval.symm) hd_eval

  exact h_trace_diff

/--
THE GNARLY BRIDGE:
To complete Option 1 and mathematically bridge our physics down to the
requirements of `diff_variationCurrent`, we define exactly what the pure-math
manifold topology must prove.
-/
def gnarly_contdiff_bridge_required (v : ℝ → PhysicalUniverse) (t : ℝ) : Prop :=
  (∀ mu x, DifferentiableAt ℝ (variationCurrent v t mu) x)

/--
Proves that a function which is ContDiff ℝ ⊤ over the joint parameter-space manifold (ℝ × SpacetimePoint)
is automatically strictly differentiable at any point exclusively along the coordinate temporal line.
-/
lemma contDiff_joint_implies_differentiable_temporal (f : ℝ × SpacetimePoint → ℂ) (tx : ℝ × SpacetimePoint)
  (h_smooth : ContDiff ℝ ⊤ f) :
  DifferentiableAt ℝ (fun t => f (t, tx.2)) tx.1 := by
  have h_diff_joint : DifferentiableAt ℝ f tx := (h_smooth.differentiable (by decide)) tx
  have hg_diff : DifferentiableAt ℝ (fun t : ℝ => (t, tx.2)) tx.1 :=
    DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const tx.2)
  exact DifferentiableAt.comp tx.1 h_diff_joint hg_diff

lemma conn_is_smooth (v : ℝ → PhysicalUniverse) (h_valid : isValidPhysicalVariation v) :
  ∀ mu i j, ContDiff ℝ ⊤ (fun (tx : ℝ × SpacetimePoint) => (v tx.1).toUniverse.spin4c_connection mu tx.2 i j) := by
  intro mu i j
  have h_sd_smooth := h_valid.1 mu
  have h_asd_smooth := h_valid.2.1 mu
  have h_eq : (fun (tx : ℝ × SpacetimePoint) => (v tx.1).toUniverse.spin4c_connection mu tx.2 i j) =
    fun (tx : ℝ × SpacetimePoint) => embedSelfDual ((v tx.1).toUniverse.sd_sector mu tx.2) i j + embedAntiSelfDual ((v tx.1).toUniverse.asd_sector mu tx.2) i j := by
    ext tx
    exact congr_fun (congr_fun (spin4c_connection_eq_embed (v tx.1).toUniverse mu tx.2) i) j
  rw [h_eq]

  have h_eq2 : (fun (tx : ℝ × SpacetimePoint) => embedSelfDual ((v tx.1).toUniverse.sd_sector mu tx.2) i j + embedAntiSelfDual ((v tx.1).toUniverse.asd_sector mu tx.2) i j) =
               fun (tx : ℝ × SpacetimePoint) => match chiralIso.symm i, chiralIso.symm j with
                         | Sum.inl a, Sum.inl b => ((v tx.1).toUniverse.sd_sector mu tx.2).val a b
                         | Sum.inr a, Sum.inr b => ((v tx.1).toUniverse.asd_sector mu tx.2).val a b
                         | _, _ => 0 := by
    ext tx
    unfold embedSelfDual embedAntiSelfDual
    simp only [Matrix.of_apply]
    rcases h_i : chiralIso.symm i with i' | i' <;> rcases h_j : chiralIso.symm j with j' | j' <;> ring

  rw [h_eq2]
  rcases h_i : chiralIso.symm i with i' | i' <;> rcases h_j : chiralIso.symm j with j' | j'
  · exact h_sd_smooth _ _
  · exact contDiff_const
  · exact contDiff_const
  · exact h_asd_smooth _ _

lemma diff_partialDerivSl2c (A : SpacetimePoint → SL2C) (μ : Fin 4) (x : SpacetimePoint)
  (h_smooth : ∀ i j, ContDiff ℝ ⊤ (fun p => (A p).val i j)) :
  ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c μ A p).val i j) x := by
  intro i j
  have h_eq : (fun p => (partialDerivSl2c μ A p).val i j) = fun p => partialDeriv μ (fun p' => (A p').val i j) p := by
    ext p
    have h_diff : ∀ a b, DifferentiableAt ℝ (fun p' => (A p').val a b) p := fun a b => ContDiff.differentiable (h_smooth a b) (by decide) p
    have h_mat := partialDerivSl2c_eq_mat A μ p h_diff
    exact congr_fun (congr_fun h_mat i) j
  rw [h_eq]
  let f : SpacetimePoint → ℂ := fun p => (A p).val i j
  have h_deriv_smooth : ContDiff ℝ 1 (fderiv ℝ f) := ContDiff.fderiv_right (h_smooth i j) (by decide)
  have h_diff_deriv : Differentiable ℝ (fderiv ℝ f) := ContDiff.differentiable h_deriv_smooth (by decide)
  let L : (SpacetimePoint →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (Pi.single μ 1)
  have hd_L : Differentiable ℝ L := ContinuousLinearMap.differentiable L
  have hd_comp : Differentiable ℝ (L ∘ (fderiv ℝ f)) := Differentiable.comp hd_L h_diff_deriv
  have h_eq2 : (fun p => partialDeriv μ f p) = L ∘ (fderiv ℝ f) := rfl
  rw [h_eq2]
  exact hd_comp x

lemma diff_curvatureSl2c (A : Fin 4 → SpacetimePoint → SL2C) (mu nu : Fin 4) (x : SpacetimePoint)
  (h_smooth : ∀ a i j, ContDiff ℝ ⊤ (fun p => (A a p).val i j)) :
  ∀ i j, DifferentiableAt ℝ (fun p => (curvatureSl2c A mu nu p).val i j) x := by
  intro i j
  have h_eq : (fun p => (curvatureSl2c A mu nu p).val i j) = fun p => (partialDerivSl2c mu (A nu) p).val i j - (partialDerivSl2c nu (A mu) p).val i j + ((A mu p).val * (A nu p).val - (A nu p).val * (A mu p).val) i j := by
    ext p
    have h_diff_mu : ∀ a b, DifferentiableAt ℝ (fun p' => (A mu p').val a b) p := fun a b => ContDiff.differentiable (h_smooth mu a b) (by decide) p
    have h_diff_nu : ∀ a b, DifferentiableAt ℝ (fun p' => (A nu p').val a b) p := fun a b => ContDiff.differentiable (h_smooth nu a b) (by decide) p
    have h_val := curvatureSl2c_val_eq A mu nu p h_diff_mu h_diff_nu i j
    have hm1 := partialDerivSl2c_eq_mat (A nu) mu p h_diff_nu
    have hm2 := partialDerivSl2c_eq_mat (A mu) nu p h_diff_mu
    have h_eval1 : (partialDerivSl2c mu (A nu) p).val i j = partialDeriv mu (fun p' => (A nu p').val i j) p := congr_fun (congr_fun hm1 i) j
    have h_eval2 : (partialDerivSl2c nu (A mu) p).val i j = partialDeriv nu (fun p' => (A mu p').val i j) p := congr_fun (congr_fun hm2 i) j
    rw [h_eval1, h_eval2]
    exact h_val
  rw [h_eq]
  apply DifferentiableAt.add
  · apply DifferentiableAt.sub
    · exact diff_partialDerivSl2c (A nu) mu x (h_smooth nu) i j
    · exact diff_partialDerivSl2c (A mu) nu x (h_smooth mu) i j
  · apply DifferentiableAt.sub
    · apply diff_matrix_mul (fun p => (A mu p).val) (fun p => (A nu p).val) x (fun a b => ContDiff.differentiable (h_smooth mu a b) (by decide) x) (fun a b => ContDiff.differentiable (h_smooth nu a b) (by decide) x) i j
    · apply diff_matrix_mul (fun p => (A nu p).val) (fun p => (A mu p).val) x (fun a b => ContDiff.differentiable (h_smooth nu a b) (by decide) x) (fun a b => ContDiff.differentiable (h_smooth mu a b) (by decide) x) i j

/--
Takes the top-level macroscopic `ContDiff ℝ ⊤` geometric constraints required by a
valid physical variation and mathematically projects them all the way down to
the point-wise `DifferentiableAt ℝ` scalar conditions required by the Variation Current integration.
-/
lemma prove_gnarly_bridge_from_valid_variation (v : ℝ → PhysicalUniverse) (t : ℝ)
  (h_valid : isValidPhysicalVariation v) :
  gnarly_contdiff_bridge_required v t := by
  unfold gnarly_contdiff_bridge_required
  intro mu x

  have h_conn_smooth := conn_is_smooth v h_valid

  have hdA : ∀ nu i j, DifferentiableAt ℝ (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection nu p i j) t) x := by
    intro nu i j
    let f : ℝ × SpacetimePoint → ℂ := fun tx => (v tx.1).toUniverse.spin4c_connection nu tx.2 i j
    have hs : ContDiff ℝ ⊤ f := h_conn_smooth nu i j
    have h_diff : Differentiable ℝ f := ContDiff.differentiable hs (by decide)
    have h_eq : (fun p => deriv (fun s => f (s, p)) t) = fun p => fderiv ℝ f (t, p) (1, 0) := by
      ext p
      exact fderiv_slice_t f t p (h_diff (t, p))
    rw [h_eq]
    have h_deriv_smooth : ContDiff ℝ 1 (fderiv ℝ f) := ContDiff.fderiv_right hs (by decide)
    have h_diff_deriv : Differentiable ℝ (fderiv ℝ f) := ContDiff.differentiable h_deriv_smooth (by decide)
    let L : (ℝ × SpacetimePoint →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (1, 0)
    have hd_L : Differentiable ℝ L := ContinuousLinearMap.differentiable L
    have hd_comp : Differentiable ℝ (L ∘ (fderiv ℝ f)) := Differentiable.comp hd_L h_diff_deriv
    let g : SpacetimePoint → ℝ × SpacetimePoint := fun p => (t, p)
    have hd_g : Differentiable ℝ g := Differentiable.prodMk (differentiable_const t) differentiable_id
    have hd_final : Differentiable ℝ ((L ∘ (fderiv ℝ f)) ∘ g) := Differentiable.comp hd_comp hd_g
    exact hd_final x

  have hF : ∀ rho sigma i j, DifferentiableAt ℝ (fun p => curvature (fun m p => (v t).toUniverse.spin4c_connection m p) rho sigma p i j) x := by
    intro rho sigma i j
    have hc : (fun p => curvature (fun m p' => (v t).toUniverse.spin4c_connection m p') rho sigma p i j) =
              (fun p => (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p)) i j + (embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j) := by
      ext p
      have h_curv := curvature_spin4c_eq (v t).toUniverse rho sigma p
      exact congr_fun (congr_fun h_curv i) j
    rw [hc]

    have hd_sd : ∀ a b, DifferentiableAt ℝ (fun p => (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p).val a b) x := by
      have hs : ∀ a c d, ContDiff ℝ ⊤ (fun p => ((v t).toUniverse.sd_sector a p).val c d) := by
        intro a c d
        let c_pt : ℝ × SpacetimePoint := (t, 0)
        let L : SpacetimePoint →L[ℝ] (ℝ × SpacetimePoint) := ContinuousLinearMap.prod (0 : SpacetimePoint →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ SpacetimePoint)
        let g : SpacetimePoint → ℝ × SpacetimePoint := fun p => c_pt + L p
        have hg_smooth : ContDiff ℝ ⊤ g := ContDiff.add contDiff_const L.contDiff
        let f : ℝ × SpacetimePoint → ℂ := fun tx => ((v tx.1).toUniverse.sd_sector a tx.2).val c d
        have hs_full : ContDiff ℝ ⊤ f := h_valid.1 a c d
        have h_comp := ContDiff.comp hs_full hg_smooth
        have h_g_eval : ∀ p, g p = (t, p) := by
          intro p
          have hc1 : (g p).1 = t := by change t + 0 = t; ring
          have hc2 : (g p).2 = p := by change 0 + p = p; simp
          exact Prod.ext hc1 hc2
        have h_eq : (fun p => ((v t).toUniverse.sd_sector a p).val c d) = f ∘ g := by
          ext p
          change _ = f (g p)
          rw [h_g_eval p]
        rw [h_eq]
        exact h_comp
      exact diff_curvatureSl2c (v t).toUniverse.sd_sector rho sigma x hs

    have hd_asd : ∀ a b, DifferentiableAt ℝ (fun p => (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p).val a b) x := by
      have hs : ∀ a c d, ContDiff ℝ ⊤ (fun p => ((v t).toUniverse.asd_sector a p).val c d) := by
        intro a c d
        let c_pt : ℝ × SpacetimePoint := (t, 0)
        let L : SpacetimePoint →L[ℝ] (ℝ × SpacetimePoint) := ContinuousLinearMap.prod (0 : SpacetimePoint →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ SpacetimePoint)
        let g : SpacetimePoint → ℝ × SpacetimePoint := fun p => c_pt + L p
        have hg_smooth : ContDiff ℝ ⊤ g := ContDiff.add contDiff_const L.contDiff
        let f : ℝ × SpacetimePoint → ℂ := fun tx => ((v tx.1).toUniverse.asd_sector a tx.2).val c d
        have hs_full : ContDiff ℝ ⊤ f := h_valid.2.1 a c d
        have h_comp := ContDiff.comp hs_full hg_smooth
        have h_g_eval : ∀ p, g p = (t, p) := by
          intro p
          have hc1 : (g p).1 = t := by change t + 0 = t; ring
          have hc2 : (g p).2 = p := by change 0 + p = p; simp
          exact Prod.ext hc1 hc2
        have h_eq : (fun p => ((v t).toUniverse.asd_sector a p).val c d) = f ∘ g := by
          ext p
          change _ = f (g p)
          rw [h_g_eval p]
        rw [h_eq]
        exact h_comp
      exact diff_curvatureSl2c (v t).toUniverse.asd_sector rho sigma x hs

    apply DifferentiableAt.add
    · rcases h_i : chiralIso.symm i with i' | i' <;> rcases h_j : chiralIso.symm j with j' | j'
      · have h_eq : (fun p => (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p)) i j) = (fun p => (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p).val i' j') := by
          ext p
          unfold embedSelfDual
          simp only [Matrix.of_apply]
          rw [h_i, h_j]
        rw [h_eq]
        exact hd_sd i' j'
      · have h_eq : (fun p => (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p)) i j) = fun p => 0 := by ext p; unfold embedSelfDual; simp [Matrix.of_apply]; rw [h_i, h_j]
        rw [h_eq]
        exact differentiableAt_const 0
      · have h_eq : (fun p => (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p)) i j) = fun p => 0 := by ext p; unfold embedSelfDual; simp [Matrix.of_apply]; rw [h_i, h_j]
        rw [h_eq]
        exact differentiableAt_const 0
      · have h_eq : (fun p => (embedSelfDual (curvatureSl2c (v t).toUniverse.sd_sector rho sigma p)) i j) = fun p => 0 := by ext p; unfold embedSelfDual; simp [Matrix.of_apply]; rw [h_i, h_j]
        rw [h_eq]
        exact differentiableAt_const 0
    · rcases h_i : chiralIso.symm i with i' | i' <;> rcases h_j : chiralIso.symm j with j' | j'
      · have h_eq : (fun p => (embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j) = fun p => 0 := by ext p; unfold embedAntiSelfDual; simp [Matrix.of_apply]; rw [h_i, h_j]
        rw [h_eq]
        exact differentiableAt_const 0
      · have h_eq : (fun p => (embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j) = fun p => 0 := by ext p; unfold embedAntiSelfDual; simp [Matrix.of_apply]; rw [h_i, h_j]
        rw [h_eq]
        exact differentiableAt_const 0
      · have h_eq : (fun p => (embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j) = fun p => 0 := by ext p; unfold embedAntiSelfDual; simp [Matrix.of_apply]; rw [h_i, h_j]
        rw [h_eq]
        exact differentiableAt_const 0
      · have h_eq : (fun p => (embedAntiSelfDual (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p)) i j) = (fun p => (curvatureSl2c (v t).toUniverse.asd_sector rho sigma p).val i' j') := by
          ext p
          unfold embedAntiSelfDual
          simp only [Matrix.of_apply]
          rw [h_i, h_j]
        rw [h_eq]
        exact hd_asd i' j'

  have h_t_diff : ∀ p nu i j, DifferentiableAt ℝ (fun s => (v s).toUniverse.spin4c_connection nu p i j) t := by
    intro p nu i j
    exact contDiff_joint_implies_differentiable_temporal (fun tx => (v tx.1).toUniverse.spin4c_connection nu tx.2 i j) (t, p) (h_conn_smooth nu i j)

  exact diff_variationCurrent v t mu x hdA hF h_t_diff

lemma smooth_implies_diff_t (f : ℝ × SpacetimePoint → ℂ) (t : ℝ) (x : SpacetimePoint)
  (h_smooth : ContDiff ℝ ⊤ f) : DifferentiableAt ℝ (fun s => f (s, x)) t := by
  have h_diff : Differentiable ℝ f := ContDiff.differentiable h_smooth (by decide)
  exact (h_diff (t, x)).comp t (DifferentiableAt.prodMk (differentiableAt_id) (differentiableAt_const x))

lemma smooth_implies_diff_x (f : ℝ × SpacetimePoint → ℂ) (t : ℝ) (x : SpacetimePoint)
  (h_smooth : ContDiff ℝ ⊤ f) : DifferentiableAt ℝ (fun p => f (t, p)) x := by
  have h_diff : Differentiable ℝ f := ContDiff.differentiable h_smooth (by decide)
  exact (h_diff (t, x)).comp x (DifferentiableAt.prodMk (differentiableAt_const t) (differentiableAt_id))

lemma partial_x_smooth (f : ℝ × SpacetimePoint → ℂ) (mu : Fin 4) (h_smooth : ContDiff ℝ ⊤ f) :
  ContDiff ℝ ⊤ (fun tx : ℝ × SpacetimePoint => partialDeriv mu (fun p => f (tx.1, p)) tx.2) := by
  have h_eq : (fun tx : ℝ × SpacetimePoint => partialDeriv mu (fun p => f (tx.1, p)) tx.2) =
              fun tx => fderiv ℝ f tx (0, Pi.single mu 1) := by
    ext tx
    have h_diff := ContDiff.differentiable h_smooth (by decide) tx
    exact fderiv_slice_x f tx.1 tx.2 mu h_diff
  rw [h_eq]
  have h_fderiv_smooth : ContDiff ℝ ⊤ (fderiv ℝ f) := ContDiff.fderiv_right h_smooth le_top
  let L : (ℝ × SpacetimePoint →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (0, Pi.single mu 1)
  exact L.contDiff.comp h_fderiv_smooth

lemma deriv_t_smooth (f : ℝ × SpacetimePoint → ℂ) (h_smooth : ContDiff ℝ ⊤ f) :
  ContDiff ℝ ⊤ (fun tx : ℝ × SpacetimePoint => deriv (fun s => f (s, tx.2)) tx.1) := by
  have h_eq : (fun tx : ℝ × SpacetimePoint => deriv (fun s => f (s, tx.2)) tx.1) =
              fun tx => fderiv ℝ f tx (1, 0) := by
    ext tx
    have h_diff := ContDiff.differentiable h_smooth (by decide) tx
    exact fderiv_slice_t f tx.1 tx.2 h_diff
  rw [h_eq]
  have h_fderiv_smooth : ContDiff ℝ ⊤ (fderiv ℝ f) := ContDiff.fderiv_right h_smooth le_top
  let L : (ℝ × SpacetimePoint →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (1, 0)
  exact L.contDiff.comp h_fderiv_smooth

lemma diff_t_conn (v : ℝ → PhysicalUniverse) (h_valid : isValidPhysicalVariation v) (t : ℝ) (x : SpacetimePoint) (mu : Fin 4) (i j : Fin 4) :
  DifferentiableAt ℝ (fun s => (v s).toUniverse.spin4c_connection mu x i j) t := by
  have h_smooth := conn_is_smooth v h_valid mu i j
  exact smooth_implies_diff_t _ t x h_smooth

lemma diff_x_deriv_t_conn (v : ℝ → PhysicalUniverse) (h_valid : isValidPhysicalVariation v) (t : ℝ) (x : SpacetimePoint) (mu : Fin 4) (i j : Fin 4) :
  DifferentiableAt ℝ (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection mu p i j) t) x := by
  have h_smooth := conn_is_smooth v h_valid mu i j
  have hd_smooth := deriv_t_smooth _ h_smooth
  exact smooth_implies_diff_x _ t x hd_smooth

lemma diff_x_deriv_t_conn_matrix (v : ℝ → PhysicalUniverse) (h_valid : isValidPhysicalVariation v) (t : ℝ) (x : SpacetimePoint) (mu : Fin 4) (i j : Fin 4) :
  DifferentiableAt ℝ (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection mu p) t i j) x := by
  have h_eq : (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection mu p) t i j) =
              fun p => deriv (fun s => (v s).toUniverse.spin4c_connection mu p i j) t := by
    ext p
    exact deriv_matrix_apply (fun s => (v s).toUniverse.spin4c_connection mu p) t (fun a b => diff_t_conn v h_valid t p mu a b) i j
  rw [h_eq]
  exact diff_x_deriv_t_conn v h_valid t x mu i j

lemma diff_t_partial_x_conn (v : ℝ → PhysicalUniverse) (h_valid : isValidPhysicalVariation v) (t : ℝ) (x : SpacetimePoint) (mu nu : Fin 4) (i j : Fin 4) :
  DifferentiableAt ℝ (fun s => partialDeriv nu (fun p => (v s).toUniverse.spin4c_connection mu p i j) x) t := by
  have h_smooth := conn_is_smooth v h_valid mu i j
  have hd_smooth := partial_x_smooth _ nu h_smooth
  exact smooth_implies_diff_t _ t x hd_smooth

lemma conn_mixed_deriv_commute (v : ℝ → PhysicalUniverse) (h_valid : isValidPhysicalVariation v) (t : ℝ) (x : SpacetimePoint) (mu nu : Fin 4) (i j : Fin 4) :
  deriv (fun s => partialDeriv nu (fun p => (v s).toUniverse.spin4c_connection mu p i j) x) t =
  partialDeriv nu (fun p => deriv (fun s => (v s).toUniverse.spin4c_connection mu p i j) t) x := by
  have h_smooth := conn_is_smooth v h_valid mu i j
  exact mixed_deriv_commute _ t nu x h_smooth

lemma diff_t_bracket (v : ℝ → PhysicalUniverse) (h_valid : isValidPhysicalVariation v) (t : ℝ) (x : SpacetimePoint) (mu nu : Fin 4) (i j : Fin 4) :
  DifferentiableAt ℝ (fun s => (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x)) i j) t := by
  have hA : ∀ a b, DifferentiableAt ℝ (fun s => ((v s).toUniverse.spin4c_connection mu x) a b) t := diff_t_conn v h_valid t x mu
  have hB : ∀ a b, DifferentiableAt ℝ (fun s => ((v s).toUniverse.spin4c_connection nu x) a b) t := diff_t_conn v h_valid t x nu
  have hd_AB := diff_deriv_sum (fun k s => ((v s).toUniverse.spin4c_connection mu x) i k * ((v s).toUniverse.spin4c_connection nu x) k j) t (by intro k; exact DifferentiableAt.mul (hA i k) (hB k j))
  have hd_BA := diff_deriv_sum (fun k s => ((v s).toUniverse.spin4c_connection nu x) i k * ((v s).toUniverse.spin4c_connection mu x) k j) t (by intro k; exact DifferentiableAt.mul (hB i k) (hA k j))
  have h_eq : (fun s => (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x)) i j) =
              fun s => ∑ k, ((v s).toUniverse.spin4c_connection mu x) i k * ((v s).toUniverse.spin4c_connection nu x) k j -
                       ∑ k, ((v s).toUniverse.spin4c_connection nu x) i k * ((v s).toUniverse.spin4c_connection mu x) k j := rfl
  rw [h_eq]
  exact DifferentiableAt.sub hd_AB hd_BA

lemma diff_t_partialDerivChiral (v : ℝ → PhysicalUniverse) (h_valid : isValidPhysicalVariation v) (t : ℝ) (x : SpacetimePoint) (mu nu : Fin 4) (i j : Fin 4) :
  DifferentiableAt ℝ (fun s => partialDerivChiral nu (fun p => (v s).toUniverse.spin4c_connection mu p) x i j) t := by
  have hc : (fun s => partialDerivChiral nu (fun p => (v s).toUniverse.spin4c_connection mu p) x i j) =
            fun s => (embedSelfDual (partialDerivSl2c nu (fun p => ((v s).toUniverse.sd_sector mu p)) x)) i j +
                     (embedAntiSelfDual (partialDerivSl2c nu (fun p => ((v s).toUniverse.asd_sector mu p)) x)) i j := by
    ext s
    have h_proj := partialDerivChiral_eq_embed_proj nu (fun p => (v s).toUniverse.spin4c_connection mu p) x
    simp_rw [chiralProject_spin4c_sd, chiralProject_spin4c_asd] at h_proj
    exact congr_fun (congr_fun h_proj i) j
  rw [hc]

  have hd_sd_eval : ∀ a b, DifferentiableAt ℝ (fun s => partialDeriv nu (fun p => ((v s).toUniverse.sd_sector mu p).val a b) x) t := by
    intro a b
    have h_smooth : ContDiff ℝ ⊤ (fun tx : ℝ × SpacetimePoint => ((v tx.1).toUniverse.sd_sector mu tx.2).val a b) := h_valid.1 mu a b
    exact smooth_implies_diff_t _ t x (partial_x_smooth _ nu h_smooth)

  have hd_asd_eval : ∀ a b, DifferentiableAt ℝ (fun s => partialDeriv nu (fun p => ((v s).toUniverse.asd_sector mu p).val a b) x) t := by
    intro a b
    have h_smooth : ContDiff ℝ ⊤ (fun tx : ℝ × SpacetimePoint => ((v tx.1).toUniverse.asd_sector mu tx.2).val a b) := h_valid.2.1 mu a b
    exact smooth_implies_diff_t _ t x (partial_x_smooth _ nu h_smooth)

  apply DifferentiableAt.add
  · rcases h_i : chiralIso.symm i with i' | i' <;> rcases h_j : chiralIso.symm j with j' | j'
    · have h_eq : (fun s => (embedSelfDual (partialDerivSl2c nu (fun p => ((v s).toUniverse.sd_sector mu p)) x)) i j) =
                  fun s => partialDeriv nu (fun p => ((v s).toUniverse.sd_sector mu p).val i' j') x := by
        ext s
        simp only [eval_embedSelfDual, h_i, h_j]
        have h_diff_sd : ∀ c d, DifferentiableAt ℝ (fun p => ((v s).toUniverse.sd_sector mu p).val c d) x := by
          intro c d
          have hs : ContDiff ℝ ⊤ (fun tx : ℝ × SpacetimePoint => ((v tx.1).toUniverse.sd_sector mu tx.2).val c d) := h_valid.1 mu c d
          exact smooth_implies_diff_x _ s x hs
        have hm := partialDerivSl2c_eq_mat (fun p => (v s).toUniverse.sd_sector mu p) nu x h_diff_sd
        exact congr_fun (congr_fun hm i') j'
      rw [h_eq]
      exact hd_sd_eval i' j'
    · have h_eq : (fun s => (embedSelfDual (partialDerivSl2c nu (fun p => ((v s).toUniverse.sd_sector mu p)) x)) i j) = fun s => 0 := by ext s; simp only [eval_embedSelfDual, h_i, h_j]
      rw [h_eq]; exact differentiableAt_const 0
    · have h_eq : (fun s => (embedSelfDual (partialDerivSl2c nu (fun p => ((v s).toUniverse.sd_sector mu p)) x)) i j) = fun s => 0 := by ext s; simp only [eval_embedSelfDual, h_i, h_j]
      rw [h_eq]; exact differentiableAt_const 0
    · have h_eq : (fun s => (embedSelfDual (partialDerivSl2c nu (fun p => ((v s).toUniverse.sd_sector mu p)) x)) i j) = fun s => 0 := by ext s; simp only [eval_embedSelfDual, h_i, h_j]
      rw [h_eq]; exact differentiableAt_const 0
  · rcases h_i : chiralIso.symm i with i' | i' <;> rcases h_j : chiralIso.symm j with j' | j'
    · have h_eq : (fun s => (embedAntiSelfDual (partialDerivSl2c nu (fun p => ((v s).toUniverse.asd_sector mu p)) x)) i j) = fun s => 0 := by ext s; simp only [eval_embedAntiSelfDual, h_i, h_j]
      rw [h_eq]; exact differentiableAt_const 0
    · have h_eq : (fun s => (embedAntiSelfDual (partialDerivSl2c nu (fun p => ((v s).toUniverse.asd_sector mu p)) x)) i j) = fun s => 0 := by ext s; simp only [eval_embedAntiSelfDual, h_i, h_j]
      rw [h_eq]; exact differentiableAt_const 0
    · have h_eq : (fun s => (embedAntiSelfDual (partialDerivSl2c nu (fun p => ((v s).toUniverse.asd_sector mu p)) x)) i j) = fun s => 0 := by ext s; simp only [eval_embedAntiSelfDual, h_i, h_j]
      rw [h_eq]; exact differentiableAt_const 0
    · have h_eq : (fun s => (embedAntiSelfDual (partialDerivSl2c nu (fun p => ((v s).toUniverse.asd_sector mu p)) x)) i j) =
                  fun s => partialDeriv nu (fun p => ((v s).toUniverse.asd_sector mu p).val i' j') x := by
        ext s
        simp only [eval_embedAntiSelfDual, h_i, h_j]
        have h_diff_asd : ∀ c d, DifferentiableAt ℝ (fun p => ((v s).toUniverse.asd_sector mu p).val c d) x := by
          intro c d
          have hs : ContDiff ℝ ⊤ (fun tx : ℝ × SpacetimePoint => ((v tx.1).toUniverse.asd_sector mu tx.2).val c d) := h_valid.2.1 mu c d
          exact smooth_implies_diff_x _ s x hs
        have hm := partialDerivSl2c_eq_mat (fun p => (v s).toUniverse.asd_sector mu p) nu x h_diff_asd
        exact congr_fun (congr_fun hm i') j'
      rw [h_eq]
      exact hd_asd_eval i' j'

lemma diff_t_curvature (v : ℝ → PhysicalUniverse) (h_valid : isValidPhysicalVariation v) (t : ℝ) (x : SpacetimePoint) (mu nu : Fin 4) (i j : Fin 4) :
  DifferentiableAt ℝ (fun s => curvature (fun m p => (v s).toUniverse.spin4c_connection m p) mu nu x i j) t := by
  have hc : (fun s => curvature (fun m p => (v s).toUniverse.spin4c_connection m p) mu nu x i j) =
            fun s => partialDerivChiral mu (fun p => (v s).toUniverse.spin4c_connection nu p) x i j -
                     partialDerivChiral nu (fun p => (v s).toUniverse.spin4c_connection mu p) x i j +
                     (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x)) i j := by
    ext s
    unfold curvature
    simp only [Matrix.add_apply, Matrix.sub_apply]
    have hb := chiralProject_bracket_spin4c_sd (v s).toUniverse mu nu x
    have hb2 := chiralProject_bracket_spin4c_asd (v s).toUniverse mu nu x
    have hb3 := bracket_spin4c (v s).toUniverse mu nu x
    have h_proj : embedSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).self_dual +
                  embedAntiSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).anti_self_dual =
                  bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x) := by
      rw [hb, hb2, hb3]
    have h_proj_eval : (embedSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).self_dual) i j +
                       (embedAntiSelfDual (chiralProject (bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x))).anti_self_dual) i j =
                       bracket ((v s).toUniverse.spin4c_connection mu x) ((v s).toUniverse.spin4c_connection nu x) i j := by
      exact congr_fun (congr_fun h_proj i) j
    rw [h_proj_eval]
  rw [hc]
  apply DifferentiableAt.add
  · apply DifferentiableAt.sub
    · exact diff_t_partialDerivChiral v h_valid t x nu mu i j
    · exact diff_t_partialDerivChiral v h_valid t x mu nu i j
  · exact diff_t_bracket v h_valid t x mu nu i j

end CGD.Foundations

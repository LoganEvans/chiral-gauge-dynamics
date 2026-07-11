-- FILENAME: CGD/Particles/Electromagnetism.lean

import Litlib.Core
import CGD.Math.Calculus
import CGD.Foundations.Spacetime
import CGD.Foundations.Calculus
import CGD.Axioms.PhysicalUniverse
import CGD.Gravity.Geometry
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

open CGD.Math CGD.Foundations CGD.Axioms CGD.Gravity Complex

namespace CGD.Particles

noncomputable def connectionComponent (pu : PhysicalUniverse) (i j : Fin 4) (μ : Fin 4) (x : SpacetimePoint) : ℂ :=
  pu.toUniverse.spin4c_connection μ x i j

/--
The true topological Abelian field strength tensor defined as a component
of the full non-Abelian curvature. Incorporates both the curl and the commutator,
enabling the dual divergence to measure the non-trivial topological magnetic current.
F_{μν}^{ij} = ∂_μ A_ν^{ij} - ∂_ν A_μ^{ij} + [A_μ, A_ν]^{ij}
-/
noncomputable def abelianFieldStrength (pu : PhysicalUniverse) (i j : Fin 4) (μ ν : Fin 4) (x : SpacetimePoint) : ℂ :=
  (partialDeriv μ (fun p => connectionComponent pu i j ν p) x - partialDeriv ν (fun p => connectionComponent pu i j μ p) x) +
  ∑ k : Fin 4, (connectionComponent pu i k μ x * connectionComponent pu k j ν x - connectionComponent pu i k ν x * connectionComponent pu k j μ x)

/--
The emergent U(1) current based on the Duan-Ge (1979) topological decomposition.
Defined as the dual divergence of the Abelian field strength tensor F_ρσ.
J^μ = ε^{μνρσ} ∂_ν F_ρσ
-/
noncomputable def emergentElectricCurrent
  (F : Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (μ : Fin 4) (x : SpacetimePoint) : ℂ :=
  ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
    epsilon4 μ ν ρ σ * partialDeriv ν (fun p => F ρ σ p) x

/--
Because the emergent current is purely topological (defined via the Levi-Civita symbol),
its divergence strictly vanishes due to the commutativity of partial derivatives,
justified natively via n-dimensional Clairaut theorem on the Abelian field strength.
-/
@[litlib_track "Topological Charge Conservation"]
theorem topologicalChargeConservation
  [clairaut : Litlib.Y1976.rudin1976principles.ClairautTheoremNDimensional]
  (F : Fin 4 → Fin 4 → SpacetimePoint → ℂ)
  (h_smooth_re : ∀ ρ σ, ContDiffOn ℝ 2 (fun p => (F ρ σ p).re) Set.univ)
  (h_smooth_im : ∀ ρ σ, ContDiffOn ℝ 2 (fun p => (F ρ σ p).im) Set.univ)
  (h_diff_F : ∀ ρ σ x, DifferentiableAt ℝ (fun p => F ρ σ p) x)
  (h_diff : ∀ ν ρ σ x, DifferentiableAt ℝ (fun p => partialDeriv ν (fun p' => F ρ σ p') p) x)
  (h_diff_fderiv_re : ∀ ρ σ x, DifferentiableAt ℝ (fderiv ℝ (fun p => (F ρ σ p).re)) x)
  (h_diff_fderiv_im : ∀ ρ σ x, DifferentiableAt ℝ (fderiv ℝ (fun p => (F ρ σ p).im)) x) :
  ∀ x : SpacetimePoint,
    ∑ μ : Fin 4, partialDeriv μ (fun p => emergentElectricCurrent F μ p) x = 0 := by
  intro x
  let S := fun (μ ν : Fin 4) => ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv μ (fun p => partialDeriv ν (fun p' => F ρ σ p') p) x

  have h_diff_smul : ∀ μ ν ρ σ, DifferentiableAt ℝ (fun p => epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x :=
    fun μ ν ρ σ => diff_const_mul (epsilon4 μ ν ρ σ) (fun p => partialDeriv ν (fun p' => F ρ σ p') p) x (h_diff ν ρ σ x)

  have h_diff_sum_sigma : ∀ μ ν ρ, DifferentiableAt ℝ (fun p => ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x :=
    fun μ ν ρ => diff_sum (fun σ p => epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x (fun σ => h_diff_smul μ ν ρ σ)

  have h_diff_sum_rho : ∀ μ ν, DifferentiableAt ℝ (fun p => ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x :=
    fun μ ν => diff_sum (fun ρ p => ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x (fun ρ => h_diff_sum_sigma μ ν ρ)

  have step1 (μ : Fin 4) :
    partialDeriv μ (fun p => emergentElectricCurrent F μ p) x =
    ∑ ν : Fin 4, partialDeriv μ (fun p => ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x :=
    partialDeriv_sum (fun ν p => ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) μ x (fun ν => h_diff_sum_rho μ ν)

  have step2 (μ ν : Fin 4) :
    partialDeriv μ (fun p => ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x =
    ∑ ρ : Fin 4, partialDeriv μ (fun p => ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x :=
    partialDeriv_sum (fun ρ p => ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) μ x (fun ρ => h_diff_sum_sigma μ ν ρ)

  have step3 (μ ν ρ : Fin 4) :
    partialDeriv μ (fun p => ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x =
    ∑ σ : Fin 4, partialDeriv μ (fun p => epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x :=
    partialDeriv_sum (fun σ p => epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) μ x (fun σ => h_diff_smul μ ν ρ σ)

  have step4 (μ ν ρ σ : Fin 4) :
    partialDeriv μ (fun p => epsilon4 μ ν ρ σ * partialDeriv ν (fun p' => F ρ σ p') p) x =
    epsilon4 μ ν ρ σ * partialDeriv μ (fun p => partialDeriv ν (fun p' => F ρ σ p') p) x :=
    partialDeriv_const_smul (epsilon4 μ ν ρ σ) (fun p => partialDeriv ν (fun p' => F ρ σ p') p) μ x (h_diff ν ρ σ x)

  have h_sum :
    ∑ μ : Fin 4, partialDeriv μ (fun p => emergentElectricCurrent F μ p) x =
    ∑ μ : Fin 4, ∑ ν : Fin 4, S μ ν := by
    apply Finset.sum_congr rfl
    intro μ _
    rw [step1 μ]
    apply Finset.sum_congr rfl
    intro ν _
    rw [step2 μ ν]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [step3 μ ν ρ]
    apply Finset.sum_congr rfl
    intro σ _
    rw [step4 μ ν ρ σ]

  have h_S_anti : ∀ μ ν, S μ ν = - S ν μ := by
    intro μ ν
    calc
      S μ ν = ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * partialDeriv μ (fun p => partialDeriv ν (fun p' => F ρ σ p') p) x := rfl
      _ = ∑ ρ : Fin 4, ∑ σ : Fin 4, (- epsilon4 ν μ ρ σ) * partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x := by
        apply Finset.sum_congr rfl
        intro ρ _
        apply Finset.sum_congr rfl
        intro σ _
        have h_eps : epsilon4 μ ν ρ σ = - epsilon4 ν μ ρ σ := (epsilon4_alt μ ν ρ σ).1

        have h_comm : partialDeriv μ (fun p => partialDeriv ν (fun p' => F ρ σ p') p) x = partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x := by
          apply Complex.ext
          · have hr1 := partialDeriv_re (fun p => partialDeriv ν (fun p' => F ρ σ p') p) μ x (h_diff ν ρ σ x)
            have h_inner_re : (fun p => (partialDeriv ν (fun p' => F ρ σ p') p).re) = partialDeriv ν (fun p => (F ρ σ p).re) := by
              ext p
              exact partialDeriv_re (fun p' => F ρ σ p') ν p (h_diff_F ρ σ p)
            rw [h_inner_re] at hr1
            rw [hr1]

            have hr2 := partialDeriv_re (fun p => partialDeriv μ (fun p' => F ρ σ p') p) ν x (h_diff μ ρ σ x)
            have h_inner_re2 : (fun p => (partialDeriv μ (fun p' => F ρ σ p') p).re) = partialDeriv μ (fun p => (F ρ σ p).re) := by
              ext p
              exact partialDeriv_re (fun p' => F ρ σ p') μ p (h_diff_F ρ σ p)
            rw [h_inner_re2] at hr2
            rw [hr2]

            exact partialDeriv_comm_real (fun p => (F ρ σ p).re) (h_smooth_re ρ σ) μ ν x (h_diff_fderiv_re ρ σ x)

          · have hi1 := partialDeriv_im (fun p => partialDeriv ν (fun p' => F ρ σ p') p) μ x (h_diff ν ρ σ x)
            have h_inner_im : (fun p => (partialDeriv ν (fun p' => F ρ σ p') p).im) = partialDeriv ν (fun p => (F ρ σ p).im) := by
              ext p
              exact partialDeriv_im (fun p' => F ρ σ p') ν p (h_diff_F ρ σ p)
            rw [h_inner_im] at hi1
            rw [hi1]

            have hi2 := partialDeriv_im (fun p => partialDeriv μ (fun p' => F ρ σ p') p) ν x (h_diff μ ρ σ x)
            have h_inner_im2 : (fun p => (partialDeriv μ (fun p' => F ρ σ p') p).im) = partialDeriv μ (fun p => (F ρ σ p).im) := by
              ext p
              exact partialDeriv_im (fun p' => F ρ σ p') μ p (h_diff_F ρ σ p)
            rw [h_inner_im2] at hi2
            rw [hi2]

            exact partialDeriv_comm_real (fun p => (F ρ σ p).im) (h_smooth_im ρ σ) μ ν x (h_diff_fderiv_im ρ σ x)

        rw [h_eps, h_comm]
      _ = ∑ ρ : Fin 4, ∑ σ : Fin 4, - (epsilon4 ν μ ρ σ * partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x) := by
        apply Finset.sum_congr rfl
        intro ρ _
        apply Finset.sum_congr rfl
        intro σ _
        ring
      _ = ∑ ρ : Fin 4, - ∑ σ : Fin 4, epsilon4 ν μ ρ σ * partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x := by
        apply Finset.sum_congr rfl
        intro ρ _
        exact sum_neg_extract _ (fun σ => epsilon4 ν μ ρ σ * partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x)
      _ = - ∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 ν μ ρ σ * partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x := by
        exact sum_neg_extract _ (fun ρ => ∑ σ : Fin 4, epsilon4 ν μ ρ σ * partialDeriv ν (fun p => partialDeriv μ (fun p' => F ρ σ p') p) x)
      _ = - S ν μ := rfl

  have h_zero : ∑ μ : Fin 4, ∑ ν : Fin 4, S μ ν = 0 := sum_antisymm_zero S h_S_anti

  rw [h_sum, h_zero]

lemma smooth_embed_sd (pu : PhysicalUniverse) (i j μ : Fin 4) :
  ContDiff ℝ ⊤ (fun x => embedSelfDual (pu.toUniverse.sd_sector.val μ x) i j) := by
  have h : (fun x => embedSelfDual (pu.toUniverse.sd_sector.val μ x) i j) =
    fun x => match chiralIso.symm i, chiralIso.symm j with
             | Sum.inl i', Sum.inl j' => (pu.toUniverse.sd_sector.val μ x).val i' j'
             | _, _ => 0 := rfl
  rw [h]
  cases h_i : chiralIso.symm i <;> cases h_j : chiralIso.symm j
  · dsimp only
    exact pu.toUniverse.sd_sector.is_smooth μ _ _
  · dsimp only
    exact contDiff_const
  · dsimp only
    exact contDiff_const
  · dsimp only
    exact contDiff_const

lemma smooth_embed_asd (pu : PhysicalUniverse) (i j μ : Fin 4) :
  ContDiff ℝ ⊤ (fun x => embedAntiSelfDual (pu.toUniverse.asd_sector.val μ x) i j) := by
  have h : (fun x => embedAntiSelfDual (pu.toUniverse.asd_sector.val μ x) i j) =
    fun x => match chiralIso.symm i, chiralIso.symm j with
             | Sum.inr i', Sum.inr j' => (pu.toUniverse.asd_sector.val μ x).val i' j'
             | _, _ => 0 := rfl
  rw [h]
  cases h_i : chiralIso.symm i <;> cases h_j : chiralIso.symm j
  · dsimp only
    exact contDiff_const
  · dsimp only
    exact contDiff_const
  · dsimp only
    exact contDiff_const
  · dsimp only
    exact pu.toUniverse.asd_sector.is_smooth μ _ _

lemma smooth_connectionComponent (pu : PhysicalUniverse) (i j μ : Fin 4) :
  ContDiff ℝ ⊤ (fun x => connectionComponent pu i j μ x) := by
  unfold connectionComponent Universe.spin4c_connection
  have h_eq : (fun x => pu.toUniverse.val μ x i j) =
    fun x => embedSelfDual (pu.toUniverse.sd_sector.val μ x) i j +
             embedAntiSelfDual (pu.toUniverse.asd_sector.val μ x) i j := by
    ext x
    exact congrFun (congrFun (pu.toUniverse.is_spin4c μ x) i) j
  rw [h_eq]
  exact (smooth_embed_sd pu i j μ).add (smooth_embed_asd pu i j μ)

lemma smooth_abelianFieldStrength (pu : PhysicalUniverse) (i j μ ν : Fin 4) :
  ContDiff ℝ ⊤ (fun x => abelianFieldStrength pu i j μ ν x) := by
  unfold abelianFieldStrength
  have h1 : ContDiff ℝ ⊤ (fun x => partialDeriv μ (fun p => connectionComponent pu i j ν p) x) :=
    contDiff_partialDeriv_complex μ _ (smooth_connectionComponent pu i j ν)
  have h2 : ContDiff ℝ ⊤ (fun x => partialDeriv ν (fun p => connectionComponent pu i j μ p) x) :=
    contDiff_partialDeriv_complex ν _ (smooth_connectionComponent pu i j μ)
  have h_derivs := h1.sub h2
  have h_comm : ContDiff ℝ ⊤ (fun x => ∑ k : Fin 4, (connectionComponent pu i k μ x * connectionComponent pu k j ν x - connectionComponent pu i k ν x * connectionComponent pu k j μ x)) := by
    apply ContDiff.sum
    intro k _
    have h_mul1 := (smooth_connectionComponent pu i k μ).mul (smooth_connectionComponent pu k j ν)
    have h_mul2 := (smooth_connectionComponent pu i k ν).mul (smooth_connectionComponent pu k j μ)
    exact h_mul1.sub h_mul2
  exact h_derivs.add h_comm

lemma smooth_re_afs (pu : PhysicalUniverse) (i j μ ν : Fin 4) :
  ContDiff ℝ ⊤ (fun p => (abelianFieldStrength pu i j μ ν p).re) := by
  let L : ℂ →L[ℝ] ℝ := {
    toFun := Complex.re
    map_add' := Complex.add_re
    map_smul' := fun r c => by simp
    cont := continuous_re
  }
  exact ContDiff.comp (g := Complex.re) (f := fun p => abelianFieldStrength pu i j μ ν p) L.contDiff (smooth_abelianFieldStrength pu i j μ ν)

lemma smooth_im_afs (pu : PhysicalUniverse) (i j μ ν : Fin 4) :
  ContDiff ℝ ⊤ (fun p => (abelianFieldStrength pu i j μ ν p).im) := by
  let L : ℂ →L[ℝ] ℝ := {
    toFun := Complex.im
    map_add' := Complex.add_im
    map_smul' := fun r c => by simp
    cont := continuous_im
  }
  exact ContDiff.comp (g := Complex.im) (f := fun p => abelianFieldStrength pu i j μ ν p) L.contDiff (smooth_abelianFieldStrength pu i j μ ν)

lemma diff_afs (pu : PhysicalUniverse) (i j μ ν : Fin 4) (x : SpacetimePoint) :
  DifferentiableAt ℝ (fun p => abelianFieldStrength pu i j μ ν p) x := by
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by decide
  have h_diff := ContDiff.differentiable (smooth_abelianFieldStrength pu i j μ ν) hn
  exact h_diff x

lemma diff_pd_afs (pu : PhysicalUniverse) (i j α μ ν : Fin 4) (x : SpacetimePoint) :
  DifferentiableAt ℝ (fun p => partialDeriv α (fun p' => abelianFieldStrength pu i j μ ν p') p) x := by
  have h_sm := contDiff_partialDeriv_complex α _ (smooth_abelianFieldStrength pu i j μ ν)
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by decide
  have h_diff := ContDiff.differentiable h_sm hn
  exact h_diff x

lemma diff_fderiv_re_afs (pu : PhysicalUniverse) (i j μ ν : Fin 4) (x : SpacetimePoint) :
  DifferentiableAt ℝ (fderiv ℝ (fun p => (abelianFieldStrength pu i j μ ν p).re)) x := by
  have h_top := smooth_re_afs pu i j μ ν
  have h_fderiv := contDiff_fderiv_of_contDiff_real h_top
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by decide
  have h_diff := ContDiff.differentiable h_fderiv hn
  exact h_diff x

lemma diff_fderiv_im_afs (pu : PhysicalUniverse) (i j μ ν : Fin 4) (x : SpacetimePoint) :
  DifferentiableAt ℝ (fderiv ℝ (fun p => (abelianFieldStrength pu i j μ ν p).im)) x := by
  have h_top := smooth_im_afs pu i j μ ν
  have h_fderiv := contDiff_fderiv_of_contDiff_real h_top
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by decide
  have h_diff := ContDiff.differentiable h_fderiv hn
  exact h_diff x

/--
Because the physical Universe is axiomatically a smooth Spin(4,C) connection,
its emergent Abelian projection natively satisfies the n-dimensional Clairaut theorem,
guaranteeing exact topological charge conservation without further assumptions.
-/
@[litlib_track "Kinematic Charge Conservation"]
theorem kinematicChargeConservation
  [clairaut : Litlib.Y1976.rudin1976principles.ClairautTheoremNDimensional]
  (pu : PhysicalUniverse) (i j : Fin 4) :
  ∀ x : SpacetimePoint,
    ∑ μ : Fin 4, partialDeriv μ (fun p => emergentElectricCurrent (abelianFieldStrength pu i j) μ p) x = 0 := by
  intro x
  apply topologicalChargeConservation (abelianFieldStrength pu i j)
  · intro ρ σ
    have h_top := smooth_re_afs pu i j ρ σ
    have h_2 : ContDiff ℝ 2 (fun p => (abelianFieldStrength pu i j ρ σ p).re) := ContDiff.of_le h_top le_top
    exact ContDiff.contDiffOn h_2
  · intro ρ σ
    have h_top := smooth_im_afs pu i j ρ σ
    have h_2 : ContDiff ℝ 2 (fun p => (abelianFieldStrength pu i j ρ σ p).im) := ContDiff.of_le h_top le_top
    exact ContDiff.contDiffOn h_2
  · intro ρ σ x'
    exact diff_afs pu i j ρ σ x'
  · intro ν ρ σ x'
    exact diff_pd_afs pu i j ν ρ σ x'
  · intro ρ σ x'
    exact diff_fderiv_re_afs pu i j ρ σ x'
  · intro ρ σ x'
    exact diff_fderiv_im_afs pu i j ρ σ x'

end CGD.Particles

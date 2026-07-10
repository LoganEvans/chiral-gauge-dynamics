-- FILENAME: CGD/Foundations/Charge.lean

import Litlib.Core
import CGD.Axioms.PhysicalUniverse
import CGD.Foundations.Spacetime
import CGD.Foundations.Calculus
import CGD.Gravity.Geometry
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Litlib.Y1976.rudin1976principles.Chapter09.Sec08_DerivativesOfHigherOrder

open CGD.Foundations CGD.Gravity CGD.Axioms
open BigOperators Complex

namespace CGD.Foundations

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
Extracts the negative sign from a finite sum.
-/
lemma sum_neg_extract (n : Type*) [Fintype n] (f : n → ℂ) :
  ∑ i : n, - f i = - ∑ i : n, f i := by
  calc
    ∑ i : n, - f i = ∑ i : n, (-1 : ℂ) * f i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (-1 : ℂ) * ∑ i : n, f i := by rw [← Finset.mul_sum]
    _ = - ∑ i : n, f i := by ring

lemma sum_antisymm_zero (S : Fin 4 → Fin 4 → ℂ) (h : ∀ i j, S i j = - S j i) :
  ∑ i : Fin 4, ∑ j : Fin 4, S i j = 0 := by
  have h1 : ∑ i : Fin 4, ∑ j : Fin 4, S i j = - ∑ i : Fin 4, ∑ j : Fin 4, S i j := by
    calc
      ∑ i : Fin 4, ∑ j : Fin 4, S i j = ∑ j : Fin 4, ∑ i : Fin 4, S i j := Finset.sum_comm
      _ = ∑ i : Fin 4, ∑ j : Fin 4, S j i := rfl
      _ = ∑ i : Fin 4, ∑ j : Fin 4, - S i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact h j i
      _ = ∑ i : Fin 4, - ∑ j : Fin 4, S i j := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_neg_extract _ (fun j => S i j)
      _ = - ∑ i : Fin 4, ∑ j : Fin 4, S i j := sum_neg_extract _ (fun i => ∑ j : Fin 4, S i j)
      
  have h2 : (2 : ℂ) * (∑ i : Fin 4, ∑ j : Fin 4, S i j) = 0 := by
    let A := ∑ i : Fin 4, ∑ j : Fin 4, S i j
    have h_add : A + A = -A + A := congrArg (fun x => x + A) h1
    calc
      (2 : ℂ) * A = A + A := by ring
      _ = -A + A := h_add
      _ = 0 := by ring
      
  calc
    ∑ i : Fin 4, ∑ j : Fin 4, S i j = (1 / 2 : ℂ) * ((2 : ℂ) * ∑ i : Fin 4, ∑ j : Fin 4, S i j) := by ring
    _ = (1 / 2 : ℂ) * 0 := by rw [h2]
    _ = 0 := by ring

lemma partialDeriv_re (f : SpacetimePoint → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) :
  (partialDeriv μ f x).re = partialDeriv μ (fun p => (f p).re) x := by
  unfold partialDeriv
  let L : ℂ →L[ℝ] ℝ := {
    toFun := Complex.re
    map_add' := Complex.add_re
    map_smul' := fun r c => by simp
    cont := continuous_re
  }
  have hg : HasFDerivAt L L (f x) := L.hasFDerivAt
  have hf_has : HasFDerivAt f (fderiv ℝ f x) x := hf.hasFDerivAt
  have hc : HasFDerivAt (L ∘ f) (L.comp (fderiv ℝ f x)) x := hg.comp x hf_has
  have h_fderiv : fderiv ℝ (fun p => (f p).re) x = L.comp (fderiv ℝ f x) := hc.fderiv
  rw [h_fderiv]
  rfl

lemma partialDeriv_im (f : SpacetimePoint → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) :
  (partialDeriv μ f x).im = partialDeriv μ (fun p => (f p).im) x := by
  unfold partialDeriv
  let L : ℂ →L[ℝ] ℝ := {
    toFun := Complex.im
    map_add' := Complex.add_im
    map_smul' := fun r c => by simp
    cont := continuous_im
  }
  have hg : HasFDerivAt L L (f x) := L.hasFDerivAt
  have hf_has : HasFDerivAt f (fderiv ℝ f x) x := hf.hasFDerivAt
  have hc : HasFDerivAt (L ∘ f) (L.comp (fderiv ℝ f x)) x := hg.comp x hf_has
  have h_fderiv : fderiv ℝ (fun p => (f p).im) x = L.comp (fderiv ℝ f x) := hc.fderiv
  rw [h_fderiv]
  rfl

lemma partialDeriv_comm_real
  [clairaut : Litlib.Y1976.rudin1976principles.ClairautTheoremNDimensional]
  (f : SpacetimePoint → ℝ)
  (h_smooth : ContDiffOn ℝ 2 f Set.univ)
  (μ ν : Fin 4) (x : SpacetimePoint) 
  (h_diff_fderiv : DifferentiableAt ℝ (fderiv ℝ f) x) :
  partialDeriv μ (partialDeriv ν f) x = partialDeriv ν (partialDeriv μ f) x := by
  let u : Fin 4 → ℝ := (Pi.single ν (1:ℝ) : Fin 4 → ℝ)
  let w : Fin 4 → ℝ := (Pi.single μ (1:ℝ) : Fin 4 → ℝ)
  
  let L_u : ((Fin 4 → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ u
  have hg1 : HasFDerivAt L_u L_u (fderiv ℝ f x) := L_u.hasFDerivAt
  have hf1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x := h_diff_fderiv.hasFDerivAt
  have hc1 : HasFDerivAt (L_u ∘ (fderiv ℝ f)) (L_u.comp (fderiv ℝ (fderiv ℝ f) x)) x := hg1.comp x hf1
  have hc1_fderiv : fderiv ℝ (L_u ∘ (fderiv ℝ f)) x = L_u.comp (fderiv ℝ (fderiv ℝ f) x) := hc1.fderiv
  
  have h_eval1 : partialDeriv μ (partialDeriv ν f) x = fderiv ℝ (fderiv ℝ f) x w u := by
    unfold partialDeriv
    have heq : (fun p => fderiv ℝ f p u) = L_u ∘ (fderiv ℝ f) := rfl
    rw [heq, hc1_fderiv]
    rfl
    
  let L_w : ((Fin 4 → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ w
  have hg2 : HasFDerivAt L_w L_w (fderiv ℝ f x) := L_w.hasFDerivAt
  have hc2 : HasFDerivAt (L_w ∘ (fderiv ℝ f)) (L_w.comp (fderiv ℝ (fderiv ℝ f) x)) x := hg2.comp x hf1
  have hc2_fderiv : fderiv ℝ (L_w ∘ (fderiv ℝ f)) x = L_w.comp (fderiv ℝ (fderiv ℝ f) x) := hc2.fderiv
  
  have h_eval2 : partialDeriv ν (partialDeriv μ f) x = fderiv ℝ (fderiv ℝ f) x u w := by
    unfold partialDeriv
    have heq : (fun p => fderiv ℝ f p w) = L_w ∘ (fderiv ℝ f) := rfl
    rw [heq, hc2_fderiv]
    rfl
    
  rw [h_eval1, h_eval2]
  
  let v : Fin 2 → (Fin 4 → ℝ) := fun i => if i = 0 then u else w
  let sig : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  
  have hc_clairaut := clairaut.symmetry_of_higher_partials 4 2 Set.univ isOpen_univ f h_smooth x (Set.mem_univ x) v sig
  
  have hr1 : iteratedFDeriv ℝ 2 f x v = fderiv ℝ (fderiv ℝ f) x u w := by
    have h : iteratedFDeriv ℝ 2 f x v = fderiv ℝ (fderiv ℝ f) x (v 0) (v 1) := iteratedFDeriv_two_apply f x v
    rw [h]
    rfl
    
  have hr2 : iteratedFDeriv ℝ 2 f x (fun i => v (sig i)) = fderiv ℝ (fderiv ℝ f) x w u := by
    have h : iteratedFDeriv ℝ 2 f x (fun i => v (sig i)) = fderiv ℝ (fderiv ℝ f) x (v (sig 0)) (v (sig 1)) := iteratedFDeriv_two_apply f x (fun i => v (sig i))
    rw [h]
    rfl
    
  rw [hr2, hr1] at hc_clairaut
  exact hc_clairaut

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

noncomputable def connectionComponent (pu : PhysicalUniverse) (i j : Fin 4) (μ : Fin 4) (x : SpacetimePoint) : ℂ :=
  pu.toUniverse.spin4c_connection μ x i j

noncomputable def abelianFieldStrength (pu : PhysicalUniverse) (i j : Fin 4) (μ ν : Fin 4) (x : SpacetimePoint) : ℂ :=
  partialDeriv μ (fun p => connectionComponent pu i j ν p) x - partialDeriv ν (fun p => connectionComponent pu i j μ p) x

lemma contDiff_fderiv_of_contDiff_real {f : SpacetimePoint → ℝ} (hf : ContDiff ℝ ⊤ f) :
  ContDiff ℝ ⊤ (fderiv ℝ f) := by
  let snd_clm : (SpacetimePoint × SpacetimePoint) →L[ℝ] SpacetimePoint := ContinuousLinearMap.snd ℝ SpacetimePoint SpacetimePoint
  have hf_snd : ContDiff ℝ ⊤ (fun p : SpacetimePoint × SpacetimePoint => f p.2) := 
    ContDiff.comp (g := f) (f := Prod.snd) hf snd_clm.contDiff
  let id_clm : SpacetimePoint →L[ℝ] SpacetimePoint := ContinuousLinearMap.id ℝ SpacetimePoint
  exact ContDiff.fderiv (f := fun _ y => f y) (g := fun x => x) hf_snd id_clm.contDiff le_top

lemma contDiff_partialDeriv_complex (μ : Fin 4) (f : SpacetimePoint → ℂ) (hf : ContDiff ℝ ⊤ f) : 
  ContDiff ℝ ⊤ (partialDeriv μ f) := by
  unfold partialDeriv
  let w : Fin 4 → ℝ := Pi.single μ 1
  have h_w : ContDiff ℝ ⊤ (fun (x : SpacetimePoint) => w) := contDiff_const
  let snd_clm : (SpacetimePoint × SpacetimePoint) →L[ℝ] SpacetimePoint := ContinuousLinearMap.snd ℝ SpacetimePoint SpacetimePoint
  have hf_snd : ContDiff ℝ ⊤ (fun (p : SpacetimePoint × SpacetimePoint) => f p.2) := ContDiff.comp (g := f) (f := Prod.snd) hf snd_clm.contDiff
  let id_clm : SpacetimePoint →L[ℝ] SpacetimePoint := ContinuousLinearMap.id ℝ SpacetimePoint
  have h_fderiv : ContDiff ℝ ⊤ (fderiv ℝ f) := ContDiff.fderiv (f := fun _ y => f y) (g := fun x => x) hf_snd id_clm.contDiff le_top
  exact ContDiff.clm_apply h_fderiv h_w

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
  exact h1.sub h2

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

end CGD.Foundations

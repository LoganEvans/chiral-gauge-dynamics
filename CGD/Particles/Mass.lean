-- FILENAME: CGD/Particles/Mass.lean

import CGD.Axioms.PhysicalUniverse
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Spacetime

open CGD.Axioms
open CGD.Foundations

namespace CGD.Particles

noncomputable def inertialMass (pu : PhysicalUniverse) (x : SpacetimePoint) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, - (Matrix.trace ((curvatureSl2c pu.toUniverse.asd_sector.val μ ν x).val * 
                                             (curvatureSl2c pu.toUniverse.asd_sector.val μ ν x).val)).re

/-- Phase 1: Prove that the Cartan-Killing trace for any SU(2) matrix is strictly non-negative. -/
lemma su2_trace_sq_nonneg (M : Matrix (Fin 2) (Fin 2) ℂ) (h : isSu2 M) : 
  -(Matrix.trace (M * M)).re ≥ 0 := by
  rcases h with ⟨h_tr, h_adj⟩
  
  -- Extract trace equation
  have h_tr_eq : M 0 0 + M 1 1 = 0 := by
    have : Matrix.trace M = ∑ i, M i i := rfl
    have eval : ∑ i, M i i = M 0 0 + M 1 1 := Fin.sum_univ_two (fun i => M i i)
    rw [this, eval] at h_tr
    exact h_tr
    
  have h_m11 : M 1 1 = - M 0 0 := by
    calc M 1 1 = (M 0 0 + M 1 1) - M 0 0 := by ring
    _ = 0 - M 0 0 := by rw [h_tr_eq]
    _ = - M 0 0 := by ring

  -- Extract adjoint equations
  have h_adj_00 : star (M 0 0) = - M 0 0 := by
    have : M.conjTranspose 0 0 = (-M) 0 0 := by rw [h_adj]
    have lhs : M.conjTranspose 0 0 = star (M 0 0) := rfl
    have rhs : (-M) 0 0 = - M 0 0 := rfl
    rw [lhs, rhs] at this
    exact this
  
  have h_adj_10 : star (M 0 1) = - M 1 0 := by
    have : M.conjTranspose 1 0 = (-M) 1 0 := by rw [h_adj]
    have lhs : M.conjTranspose 1 0 = star (M 0 1) := rfl
    have rhs : (-M) 1 0 = - M 1 0 := rfl
    rw [lhs, rhs] at this
    exact this
    
  have h_m10 : M 1 0 = - star (M 0 1) := by
    calc M 1 0 = - (- M 1 0) := by ring
    _ = - star (M 0 1) := by rw [←h_adj_10]

  -- Expand trace(M*M)
  have h_tr_M2 : Matrix.trace (M * M) = M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 1 0 * M 0 1 + M 1 1 * M 1 1 := by
    have step1 : Matrix.trace (M * M) = ∑ i, (M * M) i i := rfl
    have step1_eval : ∑ i, (M * M) i i = (M * M) 0 0 + (M * M) 1 1 := Fin.sum_univ_two (fun i => (M * M) i i)
    have step2_0 : (M * M) 0 0 = ∑ j, M 0 j * M j 0 := rfl
    have step2_0_eval : ∑ j, M 0 j * M j 0 = M 0 0 * M 0 0 + M 0 1 * M 1 0 := Fin.sum_univ_two (fun j => M 0 j * M j 0)
    have step2_1 : (M * M) 1 1 = ∑ j, M 1 j * M j 1 := rfl
    have step2_1_eval : ∑ j, M 1 j * M j 1 = M 1 0 * M 0 1 + M 1 1 * M 1 1 := Fin.sum_univ_two (fun j => M 1 j * M j 1)
    rw [step1, step1_eval, step2_0, step2_0_eval, step2_1, step2_1_eval]
    ring
    
  -- Substitute components
  have h_tr_M2_sub : Matrix.trace (M * M) = (2 : ℂ) * (M 0 0 * M 0 0) - (2 : ℂ) * (M 0 1 * star (M 0 1)) := by
    calc Matrix.trace (M * M) = M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 1 0 * M 0 1 + M 1 1 * M 1 1 := h_tr_M2
    _ = M 0 0 * M 0 0 + M 0 1 * (- star (M 0 1)) + (- star (M 0 1)) * M 0 1 + (- M 0 0) * (- M 0 0) := by rw [h_m11, h_m10]
    _ = 2 * (M 0 0 * M 0 0) - 2 * (M 0 1 * star (M 0 1)) := by ring

  -- Analyze M 0 0
  have h_m00_re : (M 0 0).re = 0 := by
    have h1 : (star (M 0 0)).re = (- M 0 0).re := by rw [h_adj_00]
    have h2 : (star (M 0 0)).re = (M 0 0).re := rfl
    have h3 : (- M 0 0).re = - (M 0 0).re := rfl
    linarith [h1, h2, h3]
    
  have h_m00_sq_re : (M 0 0 * M 0 0).re = - ((M 0 0).im * (M 0 0).im) := by
    have : (M 0 0 * M 0 0).re = (M 0 0).re * (M 0 0).re - (M 0 0).im * (M 0 0).im := rfl
    rw [this, h_m00_re]
    ring

  -- Analyze M 0 1
  have h_m01_sq_re : (M 0 1 * star (M 0 1)).re = (M 0 1).re * (M 0 1).re + (M 0 1).im * (M 0 1).im := by
    have : (M 0 1 * star (M 0 1)).re = (M 0 1).re * (star (M 0 1)).re - (M 0 1).im * (star (M 0 1)).im := rfl
    have hre : (star (M 0 1)).re = (M 0 1).re := rfl
    have him : (star (M 0 1)).im = - (M 0 1).im := rfl
    rw [this, hre, him]
    ring

  -- Take real parts
  have h_lin : ∀ A B : ℂ, ((2:ℂ) * A - (2:ℂ) * B).re = 2 * A.re - 2 * B.re := by
    intro A B
    have eqA : ((2:ℂ) * A).re = 2 * A.re := by 
      have : ((2:ℂ) * A).re = (2 : ℂ).re * A.re - (2 : ℂ).im * A.im := rfl
      have re2 : (2 : ℂ).re = 2 := rfl
      have im2 : (2 : ℂ).im = 0 := rfl
      rw [this, re2, im2]
      ring
    have eqB : ((2:ℂ) * B).re = 2 * B.re := by 
      have : ((2:ℂ) * B).re = (2 : ℂ).re * B.re - (2 : ℂ).im * B.im := rfl
      have re2 : (2 : ℂ).re = 2 := rfl
      have im2 : (2 : ℂ).im = 0 := rfl
      rw [this, re2, im2]
      ring
    have eqSub : ((2:ℂ) * A - (2:ℂ) * B).re = ((2:ℂ) * A).re - ((2:ℂ) * B).re := rfl
    rw [eqSub, eqA, eqB]

  have h_final_re : (Matrix.trace (M * M)).re = 2 * (M 0 0 * M 0 0).re - 2 * (M 0 1 * star (M 0 1)).re := by
    calc (Matrix.trace (M * M)).re = ((2:ℂ) * (M 0 0 * M 0 0) - (2:ℂ) * (M 0 1 * star (M 0 1))).re := by rw [h_tr_M2_sub]
    _ = 2 * (M 0 0 * M 0 0).re - 2 * (M 0 1 * star (M 0 1)).re := by rw [h_lin]

  -- Conclude
  have h_LHS : -(Matrix.trace (M * M)).re = 2 * ((M 0 0).im * (M 0 0).im) + 2 * ((M 0 1).re * (M 0 1).re) + 2 * ((M 0 1).im * (M 0 1).im) := by
    calc -(Matrix.trace (M * M)).re = - (2 * (M 0 0 * M 0 0).re - 2 * (M 0 1 * star (M 0 1)).re) := by rw [h_final_re]
    _ = - (2 * (- ((M 0 0).im * (M 0 0).im)) - 2 * ((M 0 1).re * (M 0 1).re + (M 0 1).im * (M 0 1).im)) := by rw [h_m00_sq_re, h_m01_sq_re]
    _ = 2 * ((M 0 0).im * (M 0 0).im) + 2 * ((M 0 1).re * (M 0 1).re) + 2 * ((M 0 1).im * (M 0 1).im) := by ring

  rw [h_LHS]
  
  have p1 : 0 ≤ (M 0 0).im * (M 0 0).im := mul_self_nonneg _
  have p2 : 0 ≤ (M 0 1).re * (M 0 1).re := mul_self_nonneg _
  have p3 : 0 ≤ (M 0 1).im * (M 0 1).im := mul_self_nonneg _
  linarith

/-- Phase 2: Establish the strict positivity bound if the SU(2) matrix is non-zero. -/
lemma su2_trace_sq_pos (M : Matrix (Fin 2) (Fin 2) ℂ) (h1 : isSu2 M) (h2 : M ≠ 0) : 
  -(Matrix.trace (M * M)).re > 0 := by
  rcases h1 with ⟨h_tr, h_adj⟩
  
  have h_tr_eq : M 0 0 + M 1 1 = 0 := by
    have : Matrix.trace M = ∑ i, M i i := rfl
    have eval : ∑ i, M i i = M 0 0 + M 1 1 := Fin.sum_univ_two (fun i => M i i)
    rw [this, eval] at h_tr
    exact h_tr
    
  have h_m11 : M 1 1 = - M 0 0 := by
    calc M 1 1 = (M 0 0 + M 1 1) - M 0 0 := by ring
    _ = 0 - M 0 0 := by rw [h_tr_eq]
    _ = - M 0 0 := by ring

  have h_adj_00 : star (M 0 0) = - M 0 0 := by
    have : M.conjTranspose 0 0 = (-M) 0 0 := by rw [h_adj]
    exact this
  
  have h_adj_10 : star (M 0 1) = - M 1 0 := by
    have : M.conjTranspose 1 0 = (-M) 1 0 := by rw [h_adj]
    exact this
    
  have h_m10 : M 1 0 = - star (M 0 1) := by
    calc M 1 0 = - (- M 1 0) := by ring
    _ = - star (M 0 1) := by rw [←h_adj_10]

  have h_tr_M2 : Matrix.trace (M * M) = M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 1 0 * M 0 1 + M 1 1 * M 1 1 := by
    have step1 : Matrix.trace (M * M) = ∑ i, (M * M) i i := rfl
    have step1_eval : ∑ i, (M * M) i i = (M * M) 0 0 + (M * M) 1 1 := Fin.sum_univ_two (fun i => (M * M) i i)
    have step2_0 : (M * M) 0 0 = M 0 0 * M 0 0 + M 0 1 * M 1 0 := Fin.sum_univ_two (fun j => M 0 j * M j 0)
    have step2_1 : (M * M) 1 1 = M 1 0 * M 0 1 + M 1 1 * M 1 1 := Fin.sum_univ_two (fun j => M 1 j * M j 1)
    rw [step1, step1_eval, step2_0, step2_1]
    ring
    
  have h_tr_M2_sub : Matrix.trace (M * M) = (2 : ℂ) * (M 0 0 * M 0 0) - (2 : ℂ) * (M 0 1 * star (M 0 1)) := by
    calc Matrix.trace (M * M) = M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 1 0 * M 0 1 + M 1 1 * M 1 1 := h_tr_M2
    _ = M 0 0 * M 0 0 + M 0 1 * (- star (M 0 1)) + (- star (M 0 1)) * M 0 1 + (- M 0 0) * (- M 0 0) := by rw [h_m11, h_m10]
    _ = 2 * (M 0 0 * M 0 0) - 2 * (M 0 1 * star (M 0 1)) := by ring

  have h_m00_re : (M 0 0).re = 0 := by
    have h1 : (star (M 0 0)).re = (- M 0 0).re := by rw [h_adj_00]
    have h2 : (star (M 0 0)).re = (M 0 0).re := rfl
    have h3 : (- M 0 0).re = - (M 0 0).re := rfl
    linarith [h1, h2, h3]
    
  have h_m00_sq_re : (M 0 0 * M 0 0).re = - ((M 0 0).im * (M 0 0).im) := by
    have : (M 0 0 * M 0 0).re = (M 0 0).re * (M 0 0).re - (M 0 0).im * (M 0 0).im := rfl
    rw [this, h_m00_re]
    ring

  have h_m01_sq_re : (M 0 1 * star (M 0 1)).re = (M 0 1).re * (M 0 1).re + (M 0 1).im * (M 0 1).im := by
    have : (M 0 1 * star (M 0 1)).re = (M 0 1).re * (star (M 0 1)).re - (M 0 1).im * (star (M 0 1)).im := rfl
    have hre : (star (M 0 1)).re = (M 0 1).re := rfl
    have him : (star (M 0 1)).im = - (M 0 1).im := rfl
    rw [this, hre, him]
    ring

  have h_lin : ∀ A B : ℂ, ((2:ℂ) * A - (2:ℂ) * B).re = 2 * A.re - 2 * B.re := by
    intro A B
    have eqA : ((2:ℂ) * A).re = 2 * A.re := by 
      have : ((2:ℂ) * A).re = (2 : ℂ).re * A.re - (2 : ℂ).im * A.im := rfl
      have re2 : (2 : ℂ).re = 2 := rfl
      have im2 : (2 : ℂ).im = 0 := rfl
      rw [this, re2, im2]
      ring
    have eqB : ((2:ℂ) * B).re = 2 * B.re := by 
      have : ((2:ℂ) * B).re = (2 : ℂ).re * B.re - (2 : ℂ).im * B.im := rfl
      have re2 : (2 : ℂ).re = 2 := rfl
      have im2 : (2 : ℂ).im = 0 := rfl
      rw [this, re2, im2]
      ring
    have eqSub : ((2:ℂ) * A - (2:ℂ) * B).re = ((2:ℂ) * A).re - ((2:ℂ) * B).re := rfl
    rw [eqSub, eqA, eqB]

  have h_final_re : (Matrix.trace (M * M)).re = 2 * (M 0 0 * M 0 0).re - 2 * (M 0 1 * star (M 0 1)).re := by
    calc (Matrix.trace (M * M)).re = ((2:ℂ) * (M 0 0 * M 0 0) - (2:ℂ) * (M 0 1 * star (M 0 1))).re := by rw [h_tr_M2_sub]
    _ = 2 * (M 0 0 * M 0 0).re - 2 * (M 0 1 * star (M 0 1)).re := by rw [h_lin]

  have h_LHS : -(Matrix.trace (M * M)).re = 2 * ((M 0 0).im * (M 0 0).im) + 2 * ((M 0 1).re * (M 0 1).re) + 2 * ((M 0 1).im * (M 0 1).im) := by
    calc -(Matrix.trace (M * M)).re = - (2 * (M 0 0 * M 0 0).re - 2 * (M 0 1 * star (M 0 1)).re) := by rw [h_final_re]
    _ = - (2 * (- ((M 0 0).im * (M 0 0).im)) - 2 * ((M 0 1).re * (M 0 1).re + (M 0 1).im * (M 0 1).im)) := by rw [h_m00_sq_re, h_m01_sq_re]
    _ = 2 * ((M 0 0).im * (M 0 0).im) + 2 * ((M 0 1).re * (M 0 1).re) + 2 * ((M 0 1).im * (M 0 1).im) := by ring

  rw [h_LHS]

  have p1 : 0 ≤ (M 0 0).im * (M 0 0).im := mul_self_nonneg _
  have p2 : 0 ≤ (M 0 1).re * (M 0 1).re := mul_self_nonneg _
  have p3 : 0 ≤ (M 0 1).im * (M 0 1).im := mul_self_nonneg _

  -- Proof by contradiction: if the sum of non-negative squares is NOT > 0, it must be ≤ 0.
  -- Since it's a sum of squares, it must be exactly 0, which forces all terms to be 0.
  by_contra h_not_pos
  push_neg at h_not_pos
  
  have h_sum_zero : 2 * ((M 0 0).im * (M 0 0).im) + 2 * ((M 0 1).re * (M 0 1).re) + 2 * ((M 0 1).im * (M 0 1).im) = 0 := by
    linarith [h_not_pos, p1, p2, p3]

  have z1 : (M 0 0).im = 0 := by
    have : 2 * ((M 0 0).im * (M 0 0).im) ≤ 0 := by linarith [p2, p3, h_sum_zero]
    have sq_zero : (M 0 0).im * (M 0 0).im = 0 := by linarith [p1]
    exact mul_self_eq_zero.mp sq_zero

  have z2 : (M 0 1).re = 0 := by
    have : 2 * ((M 0 1).re * (M 0 1).re) ≤ 0 := by linarith [p1, p3, h_sum_zero]
    have sq_zero : (M 0 1).re * (M 0 1).re = 0 := by linarith [p2]
    exact mul_self_eq_zero.mp sq_zero

  have z3 : (M 0 1).im = 0 := by
    have : 2 * ((M 0 1).im * (M 0 1).im) ≤ 0 := by linarith [p1, p2, h_sum_zero]
    have sq_zero : (M 0 1).im * (M 0 1).im = 0 := by linarith [p3]
    exact mul_self_eq_zero.mp sq_zero

  have hz_00 : M 0 0 = 0 := Complex.ext h_m00_re z1
  have hz_01 : M 0 1 = 0 := Complex.ext z2 z3
  have hz_11 : M 1 1 = 0 := by rw [h_m11, hz_00, neg_zero]
  
  have hz_10 : M 1 0 = 0 := by 
    calc M 1 0 = - star (M 0 1) := h_m10
    _ = - star (0 : ℂ) := by rw [hz_01]
    _ = 0 := by simp

  have hM_zero : M = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact hz_00
    · exact hz_01
    · exact hz_10
    · exact hz_11
    
  exact h2 hM_zero

lemma partialDeriv_star (f : SpacetimePoint → ℂ) (μ : Fin 4) (x : SpacetimePoint)
  (hf : DifferentiableAt ℝ f x) :
  partialDeriv μ (fun p => star (f p)) x = star (partialDeriv μ f x) := by
  let L : ℂ →L[ℝ] ℂ :=
    { toFun := star
      map_add' := star_add
      map_smul' := fun r c => by
        simp only [RingHom.id_apply]
        have h_conj : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
        change star ((r : ℂ) * c) = (r : ℂ) * star c
        rw [star_mul, mul_comm, h_conj]
      cont := continuous_star }
  have h_eq : (fun p => star (f p)) = L ∘ f := rfl
  rw [h_eq]
  have h_has := hf.hasFDerivAt
  have h_L_has : HasFDerivAt L L (f x) := L.hasFDerivAt
  have h_comp := h_L_has.comp x h_has
  unfold partialDeriv
  rw [h_comp.fderiv]
  rfl

/-- Phase 3: Prove that because partial derivatives commute and the Lie bracket of SU(2) remains in SU(2), the curvature tensor natively belongs to the SU(2) Lie algebra. -/
lemma curvature_is_su2 (pu : PhysicalUniverse) (x : SpacetimePoint) (μ ν : Fin 4) 
  (h_su2 : ∀ μ p, isSu2 (pu.toUniverse.asd_sector.val μ p).val) : 
  isSu2 (curvatureSl2c pu.toUniverse.asd_sector.val μ ν x).val := by
  let A := pu.toUniverse.asd_sector.val

  have hAμ : ∀ i j, DifferentiableAt ℝ (fun p => (A μ p).val i j) x := by
    intro i j
    exact (pu.toUniverse.asd_sector.is_smooth μ i j).differentiable (by decide) x
    
  have hAν : ∀ i j, DifferentiableAt ℝ (fun p => (A ν p).val i j) x := by
    intro i j
    exact (pu.toUniverse.asd_sector.is_smooth ν i j).differentiable (by decide) x

  unfold isSu2
  constructor
  · -- Trace is 0
    exact (curvatureSl2c A μ ν x).property
  · -- Adjoint is -F
    ext i j
    let F := (curvatureSl2c A μ ν x).val
    have h_lhs : F.conjTranspose i j = star (F j i) := rfl
    have h_rhs : (- F) i j = - F i j := rfl
    rw [h_lhs, h_rhs]

    have h_F_ji : F j i = partialDeriv μ (fun p => (A ν p).val j i) x - partialDeriv ν (fun p => (A μ p).val j i) x + ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) j i := by
      exact curvatureSl2c_val_eq A μ ν x hAμ hAν j i
    
    have h_F_ij : F i j = partialDeriv μ (fun p => (A ν p).val i j) x - partialDeriv ν (fun p => (A μ p).val i j) x + ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) i j := by
      exact curvatureSl2c_val_eq A μ ν x hAμ hAν i j

    rw [h_F_ji, h_F_ij]
    
    have h_star_add : ∀ a b : ℂ, star (a + b) = star a + star b := star_add
    have h_star_sub : ∀ a b : ℂ, star (a - b) = star a - star b := star_sub
    rw [h_star_add, h_star_sub]

    have h_star_A_nu : (fun p => star ((A ν p).val j i)) = fun p => - (A ν p).val i j := by
      ext p
      have h_eq : (A ν p).val.conjTranspose i j = (- (A ν p).val) i j := by rw [(h_su2 ν p).2]
      exact h_eq

    have h_star_A_mu : (fun p => star ((A μ p).val j i)) = fun p => - (A μ p).val i j := by
      ext p
      have h_eq : (A μ p).val.conjTranspose i j = (- (A μ p).val) i j := by rw [(h_su2 μ p).2]
      exact h_eq

    have hd_nu : star (partialDeriv μ (fun p => (A ν p).val j i) x) = - partialDeriv μ (fun p => (A ν p).val i j) x := by
      rw [← partialDeriv_star _ _ _ (hAν j i)]
      rw [h_star_A_nu]
      have h_neg : (fun p => - (A ν p).val i j) = fun p => (-1 : ℂ) * (A ν p).val i j := by ext p; ring
      rw [h_neg]
      rw [partialDeriv_const_smul (-1) _ μ x (hAν i j)]
      ring

    have hd_mu : star (partialDeriv ν (fun p => (A μ p).val j i) x) = - partialDeriv ν (fun p => (A μ p).val i j) x := by
      rw [← partialDeriv_star _ _ _ (hAμ j i)]
      rw [h_star_A_mu]
      have h_neg : (fun p => - (A μ p).val i j) = fun p => (-1 : ℂ) * (A μ p).val i j := by ext p; ring
      rw [h_neg]
      rw [partialDeriv_const_smul (-1) _ ν x (hAμ i j)]
      ring

    have h_comm_su2 : ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val).conjTranspose = - ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) := by
      have h1 : ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val).conjTranspose = ((A μ x).val * (A ν x).val).conjTranspose - ((A ν x).val * (A μ x).val).conjTranspose := star_sub _ _
      have h2 : ((A μ x).val * (A ν x).val).conjTranspose = (A ν x).val.conjTranspose * (A μ x).val.conjTranspose := star_mul _ _
      have h3 : ((A ν x).val * (A μ x).val).conjTranspose = (A μ x).val.conjTranspose * (A ν x).val.conjTranspose := star_mul _ _
      rw [h1, h2, h3, (h_su2 ν x).2, (h_su2 μ x).2]
      simp only [neg_mul_neg]
      exact neg_sub _ _ |>.symm

    have h_comm : star (((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) j i) = - ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) i j := by
      have h1 : star (((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val) j i) = ((A μ x).val * (A ν x).val - (A ν x).val * (A μ x).val).conjTranspose i j := rfl
      rw [h1, h_comm_su2]
      rfl

    rw [hd_nu, hd_mu, h_comm]
    ring

/-- By applying the positive definite trace property to the SU(2) curvature defect, we prove the topological origin of strictly positive inertial mass. -/
@[litlib_track "Topological Mass Gap"]
theorem topologicalMassGap (pu : PhysicalUniverse) :
  ∀ (x : SpacetimePoint),
  (∀ μ p, isSu2 (pu.toUniverse.asd_sector.val μ p).val) →
  (∃ μ ν, curvatureSl2c pu.toUniverse.asd_sector.val μ ν x ≠ 0) →
  inertialMass pu x > 0 := by
  intro x h_su2 h_defect
  unfold inertialMass
  rcases h_defect with ⟨μ0, ν0, hF_neq⟩
  apply Finset.sum_pos'
  · intro μ _
    apply Finset.sum_nonneg
    intro ν _
    have hF_su2 : isSu2 (curvatureSl2c pu.toUniverse.asd_sector.val μ ν x).val := curvature_is_su2 pu x μ ν h_su2
    exact su2_trace_sq_nonneg _ hF_su2
  · use μ0
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · intro ν _
      have hF_su2 : isSu2 (curvatureSl2c pu.toUniverse.asd_sector.val μ0 ν x).val := curvature_is_su2 pu x μ0 ν h_su2
      exact su2_trace_sq_nonneg _ hF_su2
    · use ν0
      refine ⟨Finset.mem_univ _, ?_⟩
      have hF0_su2 : isSu2 (curvatureSl2c pu.toUniverse.asd_sector.val μ0 ν0 x).val := curvature_is_su2 pu x μ0 ν0 h_su2
      have hF0_neq : (curvatureSl2c pu.toUniverse.asd_sector.val μ0 ν0 x).val ≠ 0 := fun h => hF_neq (Subtype.ext h)
      exact su2_trace_sq_pos _ hF0_su2 hF0_neq

end CGD.Particles

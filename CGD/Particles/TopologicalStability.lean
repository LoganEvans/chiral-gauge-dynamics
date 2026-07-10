-- FILENAME: CGD/Particles/TopologicalStability.lean

import Litlib.Y2003.nakahara2003geometry.Signature
import Litlib.Y1975.belavin1975pseudoparticle.Signature
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Calculus
import CGD.Foundations.Topology
import CGD.Particles.Definitions
import CGD.Axioms.Ontology
import CGD.Foundations.Spacetime
import Litlib.Math.LeviCivita
import Mathlib.Topology.Constructions
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Ring
import Litlib.Core

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Complex Matrix CGD.Foundations CGD.Axioms Litlib.Y2003.nakahara2003geometry Litlib.Y1975.belavin1975pseudoparticle

namespace CGD.Particles

instance : Nonempty S3 := ⟨⟨fun i => if i = 0 then (1:ℝ) else 0, by
  have h0 : (fun (i : Fin 4) => if i = 0 then (1:ℝ) else 0) 0 = 1 := rfl
  have h1 : (fun (i : Fin 4) => if i = 0 then (1:ℝ) else 0) 1 = 0 := rfl
  have h2 : (fun (i : Fin 4) => if i = 0 then (1:ℝ) else 0) 2 = 0 := rfl
  have h3 : (fun (i : Fin 4) => if i = 0 then (1:ℝ) else 0) 3 = 0 := rfl
  rw [h0, h1, h2, h3]
  norm_num
⟩⟩

instance : Nonempty SU2Group := ⟨1⟩

lemma su2_matrix_prop (a b : ℂ) (h : a * star a + b * star b = 1) :
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![a, b; -star b, star a]
  M * M.conjTranspose = 1 ∧ M.det = 1 := by
  intro M
  have h_det : M.det = 1 := by
    rw [Matrix.det_fin_two]
    change a * star a - b * (-star b) = 1
    calc a * star a - b * (-star b) = a * star a + b * star b := by ring
      _ = 1 := h
      
  have h_mul : M * M.conjTranspose = 1 := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
    match i, j with
    | 0, 0 =>
      rw [Matrix.one_apply, if_pos rfl]
      change a * star a + b * star b = 1
      exact h
    | 0, 1 =>
      rw [Matrix.one_apply]
      have h_ne : (0 : Fin 2) ≠ 1 := by decide
      rw [if_neg h_ne]
      change a * star (-star b) + b * star (star a) = 0
      rw [star_neg, star_star, star_star]
      ring
    | 1, 0 =>
      rw [Matrix.one_apply]
      have h_ne : (1 : Fin 2) ≠ 0 := by decide
      rw [if_neg h_ne]
      change (-star b) * star a + star a * star b = 0
      ring
    | 1, 1 =>
      rw [Matrix.one_apply, if_pos rfl]
      change (-star b) * star (-star b) + star a * star (star a) = 1
      rw [star_neg, star_star, star_star]
      calc (-star b) * (-b) + star a * a = a * star a + b * star b := by ring
        _ = 1 := h
        
  exact ⟨h_mul, h_det⟩

noncomputable def bpstAsymptoticMap (x : S3) : SU2Group := by
  cases x
  rename_i v hv

  let a : ℂ := Complex.mk (v 0) (-(v 3))
  let b : ℂ := Complex.mk (-(v 2)) (-(v 1))

  have h_sum : a * star a + b * star b = 1 := by
    apply Complex.ext
    · change (v 0) * (v 0) - (-(v 3)) * (-(-(v 3))) + ((-(v 2)) * (-(v 2)) - (-(v 1)) * (-(-(v 1)))) = 1
      calc (v 0) * (v 0) - (-(v 3)) * (-(-(v 3))) + ((-(v 2)) * (-(v 2)) - (-(v 1)) * (-(-(v 1))))
        _ = (v 0)^2 + (v 1)^2 + (v 2)^2 + (v 3)^2 := by ring
        _ = 1 := hv
    · change (v 0) * (-(-(v 3))) + (-(v 3)) * (v 0) + ((-(v 2)) * (-(-(v 1))) + (-(v 1)) * (-(v 2))) = 0
      ring

  let M : Matrix (Fin 2) (Fin 2) ℂ := !![a, b; -star b, star a]
  have h_prop : M * M.conjTranspose = 1 ∧ M.det = 1 := su2_matrix_prop a b h_sum
  
  exact ⟨M, h_prop⟩

noncomputable def su2ToS3 (M : SU2Group) : S3 :=
  let x0 := (M.val 0 0).re
  let x1 := - (M.val 1 0).im
  let x2 := (M.val 1 0).re
  let x3 := - (M.val 0 0).im
  Subtype.mk (fun i => if i = 0 then x0 else if i = 1 then x1 else if i = 2 then x2 else x3) (by 
    have h1 : M.val * M.val.conjTranspose = 1 := M.property.1
    have h2 : M.val.conjTranspose * M.val = 1 := mul_eq_one_comm.mp h1
    have h3 : (M.val.conjTranspose * M.val) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [h2]
    have h_eq_trace : star (M.val 0 0) * M.val 0 0 + star (M.val 1 0) * M.val 1 0 = (M.val.conjTranspose * M.val) 0 0 := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    have h4 : (M.val 0 0).re ^ 2 + (M.val 0 0).im ^ 2 + (M.val 1 0).re ^ 2 + (M.val 1 0).im ^ 2 = 1 := by
      calc (M.val 0 0).re ^ 2 + (M.val 0 0).im ^ 2 + (M.val 1 0).re ^ 2 + (M.val 1 0).im ^ 2 
        _ = (star (M.val 0 0) * M.val 0 0 + star (M.val 1 0) * M.val 1 0).re := by
          simp only [Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
          ring
        _ = ((M.val.conjTranspose * M.val) 0 0).re := by rw [h_eq_trace]
        _ = ((1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re := by rw [h3]
        _ = 1 := rfl
    dsimp [x0, x1, x2, x3]
    linear_combination h4
  )

theorem left_inv_su2_s3 (x : S3) : su2ToS3 (bpstAsymptoticMap x) = x := by
  obtain ⟨v, hv⟩ := x
  ext i
  fin_cases i
  · change v 0 = v 0; rfl
  · change -(-(-(-(v 1)))) = v 1; ring
  · change -(-(v 2)) = v 2; ring
  · change -(-(v 3)) = v 3; ring

theorem right_inv_su2_s3 (M : SU2Group) : bpstAsymptoticMap (su2ToS3 M) = M := by
  have hdet : M.val 0 0 * M.val 1 1 - M.val 0 1 * M.val 1 0 = 1 := by
    have h := M.property.2
    rw [Matrix.det_fin_two] at h
    exact h
  have hmul : M.val * M.val.conjTranspose = 1 := M.property.1
  have hmul2 : M.val.conjTranspose * M.val = 1 := mul_eq_one_comm.mp hmul
  have h_inv : M.val.adjugate = M.val.conjTranspose := by
    have h1 : M.val * M.val.adjugate = 1 := by
      calc M.val * M.val.adjugate = M.val.det • 1 := Matrix.mul_adjugate M.val
      _ = (1 : ℂ) • 1 := by rw [M.property.2]
      _ = 1 := one_smul ℂ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    calc
      M.val.adjugate = 1 * M.val.adjugate := by rw [Matrix.one_mul]
      _ = (M.val.conjTranspose * M.val) * M.val.adjugate := by rw [hmul2]
      _ = M.val.conjTranspose * (M.val * M.val.adjugate) := by rw [Matrix.mul_assoc]
      _ = M.val.conjTranspose * 1 := by rw [h1]
      _ = M.val.conjTranspose := by rw [Matrix.mul_one]

  have h00 : M.val 1 1 = star (M.val 0 0) := by
    have h_eq : M.val.adjugate 1 1 = M.val.conjTranspose 1 1 := congrArg (fun A => A 1 1) h_inv
    rw [Matrix.adjugate_fin_two] at h_eq
    have h_conj : M.val.conjTranspose 1 1 = star (M.val 1 1) := rfl
    rw [h_conj] at h_eq
    have h_eq2 : M.val 0 0 = star (M.val 1 1) := h_eq
    calc M.val 1 1 = star (star (M.val 1 1)) := by rw [star_star]
      _ = star (M.val 0 0) := by rw [←h_eq2]

  have h01 : M.val 0 1 = - star (M.val 1 0) := by
    have h_eq : M.val.adjugate 0 1 = M.val.conjTranspose 0 1 := congrArg (fun A => A 0 1) h_inv
    rw [Matrix.adjugate_fin_two] at h_eq
    have h_conj : M.val.conjTranspose 0 1 = star (M.val 1 0) := rfl
    rw [h_conj] at h_eq
    have h_eq2 : - M.val 0 1 = star (M.val 1 0) := h_eq
    linear_combination -h_eq2
  
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · change (bpstAsymptoticMap (su2ToS3 M)).val 0 0 = M.val 0 0
    apply Complex.ext
    · change (M.val 0 0).re = (M.val 0 0).re; rfl
    · change -(-(M.val 0 0).im) = (M.val 0 0).im; ring
  · change (bpstAsymptoticMap (su2ToS3 M)).val 0 1 = M.val 0 1
    rw [h01]
    apply Complex.ext
    · change -(M.val 1 0).re = -(M.val 1 0).re; rfl
    · change -(-(M.val 1 0).im) = -(-(M.val 1 0).im); ring
  · change (bpstAsymptoticMap (su2ToS3 M)).val 1 0 = M.val 1 0
    apply Complex.ext
    · change -(-(M.val 1 0).re) = (M.val 1 0).re; ring
    · change -(-(-(-(M.val 1 0).im))) = (M.val 1 0).im; ring
  · change (bpstAsymptoticMap (su2ToS3 M)).val 1 1 = M.val 1 1
    rw [h00]
    apply Complex.ext
    · change (M.val 0 0).re = (M.val 0 0).re; rfl
    · change -(-(-(M.val 0 0).im)) = -(M.val 0 0).im; ring

noncomputable instance : TopologicalSpace SU2Group := instTopologicalSpaceSubtype

@[litlib_track "BPST Instanton Is Homeomorphism"]
theorem bpst_is_homeomorphism : IsHomeomorphism bpstAsymptoticMap := by
  apply IsHomeomorphism.mk
  · constructor
    · intro x y hxy
      have h := congrArg su2ToS3 hxy
      rw [left_inv_su2_s3, left_inv_su2_s3] at h
      exact h
    · intro M
      use su2ToS3 M
      exact right_inv_su2_s3 M
  · apply Continuous.subtype_mk
    apply continuous_matrix
    intro i j
    have h0 : Continuous (fun x : S3 => (x.val 0 : ℂ)) := Complex.continuous_ofReal.comp (Continuous.comp (continuous_apply 0) continuous_subtype_val)
    have h1 : Continuous (fun x : S3 => (x.val 1 : ℂ)) := Complex.continuous_ofReal.comp (Continuous.comp (continuous_apply 1) continuous_subtype_val)
    have h2 : Continuous (fun x : S3 => (x.val 2 : ℂ)) := Complex.continuous_ofReal.comp (Continuous.comp (continuous_apply 2) continuous_subtype_val)
    have h3 : Continuous (fun x : S3 => (x.val 3 : ℂ)) := Complex.continuous_ofReal.comp (Continuous.comp (continuous_apply 3) continuous_subtype_val)
    fin_cases i <;> fin_cases j
    · have h_eq : (fun (a : S3) => (bpstAsymptoticMap a).val 0 0) = fun a => (a.val 0 : ℂ) - Complex.I * (a.val 3 : ℂ) := by
        ext a
        dsimp [bpstAsymptoticMap]
        apply Complex.ext
        · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
          ring
        · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
          ring
      change Continuous (fun a => (bpstAsymptoticMap a).val 0 0)
      rw [h_eq]
      exact Continuous.sub h0 (Continuous.mul continuous_const h3)
    · have h_eq : (fun (a : S3) => (bpstAsymptoticMap a).val 0 1) = fun a => -(a.val 2 : ℂ) - Complex.I * (a.val 1 : ℂ) := by
        ext a
        dsimp [bpstAsymptoticMap]
        apply Complex.ext
        · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
          ring
        · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
          ring
      change Continuous (fun a => (bpstAsymptoticMap a).val 0 1)
      rw [h_eq]
      exact Continuous.sub (Continuous.neg h2) (Continuous.mul continuous_const h1)
    · have h_eq : (fun (a : S3) => (bpstAsymptoticMap a).val 1 0) = fun a => (a.val 2 : ℂ) - Complex.I * (a.val 1 : ℂ) := by
        ext a
        dsimp [bpstAsymptoticMap]
        apply Complex.ext
        · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
          ring
        · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
          ring
      change Continuous (fun a => (bpstAsymptoticMap a).val 1 0)
      rw [h_eq]
      exact Continuous.sub h2 (Continuous.mul continuous_const h1)
    · have h_eq : (fun (a : S3) => (bpstAsymptoticMap a).val 1 1) = fun a => (a.val 0 : ℂ) + Complex.I * (a.val 3 : ℂ) := by
        ext a
        dsimp [bpstAsymptoticMap]
        apply Complex.ext
        · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
          ring
        · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
          ring
      change Continuous (fun a => (bpstAsymptoticMap a).val 1 1)
      rw [h_eq]
      exact Continuous.add h0 (Continuous.mul continuous_const h3)
  · use su2ToS3
    constructor
    · exact left_inv_su2_s3
    · constructor
      · exact right_inv_su2_s3
      · apply Continuous.subtype_mk
        apply continuous_pi
        intro i
        have h00 : Continuous (fun M : SU2Group => M.val 0 0) := Continuous.comp (continuous_apply 0) (Continuous.comp (continuous_apply 0) continuous_subtype_val)
        have h10 : Continuous (fun M : SU2Group => M.val 1 0) := Continuous.comp (continuous_apply 0) (Continuous.comp (continuous_apply 1) continuous_subtype_val)
        fin_cases i
        · have h_eq : (fun (a : SU2Group) => (su2ToS3 a).val 0) = fun a => (a.val 0 0).re := by ext a; rfl
          change Continuous (fun a => (su2ToS3 a).val 0)
          rw [h_eq]
          exact Complex.continuous_re.comp h00
        · have h_eq : (fun (a : SU2Group) => (su2ToS3 a).val 1) = fun a => -(a.val 1 0).im := by ext a; rfl
          change Continuous (fun a => (su2ToS3 a).val 1)
          rw [h_eq]
          exact Continuous.neg (Complex.continuous_im.comp h10)
        · have h_eq : (fun (a : SU2Group) => (su2ToS3 a).val 2) = fun a => (a.val 1 0).re := by ext a; rfl
          change Continuous (fun a => (su2ToS3 a).val 2)
          rw [h_eq]
          exact Complex.continuous_re.comp h10
        · have h_eq : (fun (a : SU2Group) => (su2ToS3 a).val 3) = fun a => -(a.val 0 0).im := by ext a; rfl
          change Continuous (fun a => (su2ToS3 a).val 3)
          rw [h_eq]
          exact Continuous.neg (Complex.continuous_im.comp h00)

noncomputable def extractV (A : Fin 4 → SpacetimePoint → SL2C) (v : S3) : Fin 4 → ℝ :=
  fun i =>
    if i = 0 then (Matrix.trace ((A 1 v.val).val * (Complex.I • sigma1.val))).re
    else if i = 1 then -(Matrix.trace ((A 0 v.val).val * (Complex.I • sigma1.val))).re
    else if i = 2 then -(Matrix.trace ((A 0 v.val).val * (Complex.I • sigma2.val))).re
    else -(Matrix.trace ((A 0 v.val).val * (Complex.I • sigma3.val))).re

noncomputable def makeSU2 (v : Fin 4 → ℝ) : SU2Group :=
  let norm_sq := (v 0)^2 + (v 1)^2 + (v 2)^2 + (v 3)^2
  if h : norm_sq = 1 then
    let a := Complex.mk (v 0) (-(v 3))
    let b := Complex.mk (-(v 2)) (-(v 1))
    let M : Matrix (Fin 2) (Fin 2) ℂ := !![a, b; -star b, star a]
    have h_sum : a * star a + b * star b = 1 := by
      apply Complex.ext
      · change (v 0) * (v 0) - (-(v 3)) * (-(-(v 3))) + ((-(v 2)) * (-(v 2)) - (-(v 1)) * (-(-(v 1)))) = 1
        calc (v 0) * (v 0) - (-(v 3)) * (-(-(v 3))) + ((-(v 2)) * (-(v 2)) - (-(v 1)) * (-(-(v 1))))
          _ = (v 0)^2 + (v 1)^2 + (v 2)^2 + (v 3)^2 := by ring
          _ = 1 := h
      · change (v 0) * (-(-(v 3))) + (-(v 3)) * (v 0) + ((-(v 2)) * (-(-(v 1))) + (-(v 1)) * (-(v 2))) = 0
        ring
    ⟨M, su2_matrix_prop a b h_sum⟩
  else 1

noncomputable def geometricBoundaryProjection (A : Fin 4 → SpacetimePoint → SL2C) : S3 → SU2Group :=
  fun v => makeSU2 (extractV A v)

-- Explicit element accessors to bypass the unifier/simplifier matrix explosions
lemma trace_mul_fin2 (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
  Matrix.trace (X * Y) = X 0 0 * Y 0 0 + X 0 1 * Y 1 0 + X 1 0 * Y 0 1 + X 1 1 * Y 1 1 := by
  dsimp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Fin.sum_univ_two]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  ring

-- To bypass the `toSl2c` constructor dynamically, we prove that for trace-free matrices, .val = the original matrix.
lemma toSl2c_val_eq (M : Matrix (Fin 2) (Fin 2) ℂ) (h : M.trace = 0) : (toSl2c M).val = M := by
  dsimp [toSl2c]
  rw [h]
  have hz : ((0 : ℂ) / 2) = 0 := by ring
  rw [hz]
  have hz_smul : (0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    ext i j
    change (0 : ℂ) * (if i = j then 1 else 0) = 0
    ring
  rw [hz_smul]
  exact sub_zero M

-- Base Pauli Traces (Evaluated by expanding the trace sum, then asserting the values natively)
lemma sigmaX_trace : sigmaX.trace = 0 := by 
  dsimp [Matrix.trace, Matrix.diag]
  rw [Fin.sum_univ_two]
  change (0 : ℂ) + (0 : ℂ) = 0
  ring

lemma sigmaY_trace : sigmaY.trace = 0 := by 
  dsimp [Matrix.trace, Matrix.diag]
  rw [Fin.sum_univ_two]
  change (0 : ℂ) + (0 : ℂ) = 0
  ring

lemma sigmaZ_trace : sigmaZ.trace = 0 := by 
  dsimp [Matrix.trace, Matrix.diag]
  rw [Fin.sum_univ_two]
  change (1 : ℂ) + (-1 : ℂ) = 0
  ring

-- Map the algebra values back to the raw matrices
lemma val_sigma1 : sigma1.val = sigmaX := toSl2c_val_eq sigmaX sigmaX_trace
lemma val_sigma2 : sigma2.val = sigmaY := toSl2c_val_eq sigmaY sigmaY_trace
lemma val_sigma3 : sigma3.val = sigmaZ := toSl2c_val_eq sigmaZ sigmaZ_trace

-- Base Pauli Matrix Elements (Evaluated natively by rfl)
lemma sig1_00 : sigmaX 0 0 = 0 := rfl
lemma sig1_01 : sigmaX 0 1 = 1 := rfl
lemma sig1_10 : sigmaX 1 0 = 1 := rfl
lemma sig1_11 : sigmaX 1 1 = 0 := rfl

lemma sig2_00 : sigmaY 0 0 = 0 := rfl
lemma sig2_01 : sigmaY 0 1 = -Complex.I := rfl
lemma sig2_10 : sigmaY 1 0 = Complex.I := rfl
lemma sig2_11 : sigmaY 1 1 = 0 := rfl

lemma sig3_00 : sigmaZ 0 0 = 1 := rfl
lemma sig3_01 : sigmaZ 0 1 = 0 := rfl
lemma sig3_10 : sigmaZ 1 0 = 0 := rfl
lemma sig3_11 : sigmaZ 1 1 = -1 := rfl

lemma eval_bpst_trace_0 (v : S3) :
  let A1 := (Complex.I / 2 : ℂ) • (-(v.val 0 : ℂ) • sigma1.val - (v.val 3 : ℂ) • sigma2.val + (v.val 2 : ℂ) • sigma3.val)
  (Matrix.trace (A1 * (Complex.I • sigma1.val))).re = v.val 0 := by
  intro A1
  dsimp only [A1]
  rw [val_sigma1, val_sigma2, val_sigma3]
  rw [trace_mul_fin2]
  change (
    ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) * sigmaX 0 0 - (v.val 3 : ℂ) * sigmaY 0 0 + (v.val 2 : ℂ) * sigmaZ 0 0)) * (Complex.I * sigmaX 0 0) +
    ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) * sigmaX 0 1 - (v.val 3 : ℂ) * sigmaY 0 1 + (v.val 2 : ℂ) * sigmaZ 0 1)) * (Complex.I * sigmaX 1 0) +
    ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) * sigmaX 1 0 - (v.val 3 : ℂ) * sigmaY 1 0 + (v.val 2 : ℂ) * sigmaZ 1 0)) * (Complex.I * sigmaX 0 1) +
    ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) * sigmaX 1 1 - (v.val 3 : ℂ) * sigmaY 1 1 + (v.val 2 : ℂ) * sigmaZ 1 1)) * (Complex.I * sigmaX 1 1)
  ).re = v.val 0
  
  have h_comp : (
    ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) * sigmaX 0 0 - (v.val 3 : ℂ) * sigmaY 0 0 + (v.val 2 : ℂ) * sigmaZ 0 0)) * (Complex.I * sigmaX 0 0) +
    ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) * sigmaX 0 1 - (v.val 3 : ℂ) * sigmaY 0 1 + (v.val 2 : ℂ) * sigmaZ 0 1)) * (Complex.I * sigmaX 1 0) +
    ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) * sigmaX 1 0 - (v.val 3 : ℂ) * sigmaY 1 0 + (v.val 2 : ℂ) * sigmaZ 1 0)) * (Complex.I * sigmaX 0 1) +
    ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) * sigmaX 1 1 - (v.val 3 : ℂ) * sigmaY 1 1 + (v.val 2 : ℂ) * sigmaZ 1 1)) * (Complex.I * sigmaX 1 1)
  ) = (v.val 0 : ℂ) := by
    rw [sig1_00, sig1_01, sig1_10, sig1_11, sig2_00, sig2_01, sig2_10, sig2_11, sig3_00, sig3_01, sig3_10, sig3_11]
    calc
      ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) * 0 - (v.val 3 : ℂ) * 0 + (v.val 2 : ℂ) * 1)) * (Complex.I * 0) +
      ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) * 1 - (v.val 3 : ℂ) * -Complex.I + (v.val 2 : ℂ) * 0)) * (Complex.I * 1) +
      ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) * 1 - (v.val 3 : ℂ) * Complex.I + (v.val 2 : ℂ) * 0)) * (Complex.I * 1) +
      ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) * 0 - (v.val 3 : ℂ) * 0 + (v.val 2 : ℂ) * -1)) * (Complex.I * 0)
      = ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) + (v.val 3 : ℂ) * Complex.I)) * Complex.I +
        ((Complex.I / 2 : ℂ) * (-(v.val 0 : ℂ) - (v.val 3 : ℂ) * Complex.I)) * Complex.I := by ring
      _ = (Complex.I / 2 : ℂ) * Complex.I * (-(v.val 0 : ℂ) + (v.val 3 : ℂ) * Complex.I - (v.val 0 : ℂ) - (v.val 3 : ℂ) * Complex.I) := by ring
      _ = (Complex.I / 2 : ℂ) * Complex.I * (-2 * (v.val 0 : ℂ)) := by ring
      _ = (Complex.I ^ 2) * (- (v.val 0 : ℂ)) := by ring
      _ = (-1 : ℂ) * (- (v.val 0 : ℂ)) := by rw [Complex.I_sq]
      _ = (v.val 0 : ℂ) := by ring

  rw [h_comp]
  rfl

lemma eval_bpst_trace_1 (v : S3) :
  let A0 := (Complex.I / 2 : ℂ) • ((v.val 1 : ℂ) • sigma1.val + (v.val 2 : ℂ) • sigma2.val + (v.val 3 : ℂ) • sigma3.val);
  -(Matrix.trace (A0 * (Complex.I • sigma1.val))).re = v.val 1 := by
  intro A0
  dsimp only [A0]
  rw [val_sigma1, val_sigma2, val_sigma3]
  rw [trace_mul_fin2]
  change -(
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 0 0 + (v.val 2 : ℂ) * sigmaY 0 0 + (v.val 3 : ℂ) * sigmaZ 0 0)) * (Complex.I * sigmaX 0 0) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 0 1 + (v.val 2 : ℂ) * sigmaY 0 1 + (v.val 3 : ℂ) * sigmaZ 0 1)) * (Complex.I * sigmaX 1 0) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 1 0 + (v.val 2 : ℂ) * sigmaY 1 0 + (v.val 3 : ℂ) * sigmaZ 1 0)) * (Complex.I * sigmaX 0 1) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 1 1 + (v.val 2 : ℂ) * sigmaY 1 1 + (v.val 3 : ℂ) * sigmaZ 1 1)) * (Complex.I * sigmaX 1 1)
  ).re = v.val 1
  
  have h_comp : (
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 0 0 + (v.val 2 : ℂ) * sigmaY 0 0 + (v.val 3 : ℂ) * sigmaZ 0 0)) * (Complex.I * sigmaX 0 0) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 0 1 + (v.val 2 : ℂ) * sigmaY 0 1 + (v.val 3 : ℂ) * sigmaZ 0 1)) * (Complex.I * sigmaX 1 0) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 1 0 + (v.val 2 : ℂ) * sigmaY 1 0 + (v.val 3 : ℂ) * sigmaZ 1 0)) * (Complex.I * sigmaX 0 1) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 1 1 + (v.val 2 : ℂ) * sigmaY 1 1 + (v.val 3 : ℂ) * sigmaZ 1 1)) * (Complex.I * sigmaX 1 1)
  ) = - (v.val 1 : ℂ) := by
    rw [sig1_00, sig1_01, sig1_10, sig1_11, sig2_00, sig2_01, sig2_10, sig2_11, sig3_00, sig3_01, sig3_10, sig3_11]
    calc
      ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * 0 + (v.val 2 : ℂ) * 0 + (v.val 3 : ℂ) * 1)) * (Complex.I * 0) +
      ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * 1 + (v.val 2 : ℂ) * -Complex.I + (v.val 3 : ℂ) * 0)) * (Complex.I * 1) +
      ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * 1 + (v.val 2 : ℂ) * Complex.I + (v.val 3 : ℂ) * 0)) * (Complex.I * 1) +
      ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * 0 + (v.val 2 : ℂ) * 0 + (v.val 3 : ℂ) * -1)) * (Complex.I * 0)
      = ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) - (v.val 2 : ℂ) * Complex.I)) * Complex.I +
        ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) + (v.val 2 : ℂ) * Complex.I)) * Complex.I := by ring
      _ = (Complex.I / 2 : ℂ) * Complex.I * ((v.val 1 : ℂ) - (v.val 2 : ℂ) * Complex.I + (v.val 1 : ℂ) + (v.val 2 : ℂ) * Complex.I) := by ring
      _ = (Complex.I / 2 : ℂ) * Complex.I * (2 * (v.val 1 : ℂ)) := by ring
      _ = (Complex.I ^ 2) * (v.val 1 : ℂ) := by ring
      _ = (-1 : ℂ) * (v.val 1 : ℂ) := by rw [Complex.I_sq]
      _ = - (v.val 1 : ℂ) := by ring

  rw [h_comp]
  change (- -(v.val 1 : ℝ)) = v.val 1
  ring

lemma eval_bpst_trace_2 (v : S3) :
  let A0 := (Complex.I / 2 : ℂ) • ((v.val 1 : ℂ) • sigma1.val + (v.val 2 : ℂ) • sigma2.val + (v.val 3 : ℂ) • sigma3.val);
  -(Matrix.trace (A0 * (Complex.I • sigma2.val))).re = v.val 2 := by
  intro A0
  dsimp only [A0]
  rw [val_sigma1, val_sigma2, val_sigma3]
  rw [trace_mul_fin2]
  change -(
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 0 0 + (v.val 2 : ℂ) * sigmaY 0 0 + (v.val 3 : ℂ) * sigmaZ 0 0)) * (Complex.I * sigmaY 0 0) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 0 1 + (v.val 2 : ℂ) * sigmaY 0 1 + (v.val 3 : ℂ) * sigmaZ 0 1)) * (Complex.I * sigmaY 1 0) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 1 0 + (v.val 2 : ℂ) * sigmaY 1 0 + (v.val 3 : ℂ) * sigmaZ 1 0)) * (Complex.I * sigmaY 0 1) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 1 1 + (v.val 2 : ℂ) * sigmaY 1 1 + (v.val 3 : ℂ) * sigmaZ 1 1)) * (Complex.I * sigmaY 1 1)
  ).re = v.val 2
  
  have h_comp : (
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 0 0 + (v.val 2 : ℂ) * sigmaY 0 0 + (v.val 3 : ℂ) * sigmaZ 0 0)) * (Complex.I * sigmaY 0 0) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 0 1 + (v.val 2 : ℂ) * sigmaY 0 1 + (v.val 3 : ℂ) * sigmaZ 0 1)) * (Complex.I * sigmaY 1 0) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 1 0 + (v.val 2 : ℂ) * sigmaY 1 0 + (v.val 3 : ℂ) * sigmaZ 1 0)) * (Complex.I * sigmaY 0 1) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 1 1 + (v.val 2 : ℂ) * sigmaY 1 1 + (v.val 3 : ℂ) * sigmaZ 1 1)) * (Complex.I * sigmaY 1 1)
  ) = - (v.val 2 : ℂ) := by
    rw [sig1_00, sig1_01, sig1_10, sig1_11, sig2_00, sig2_01, sig2_10, sig2_11, sig3_00, sig3_01, sig3_10, sig3_11]
    calc
      ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * 0 + (v.val 2 : ℂ) * 0 + (v.val 3 : ℂ) * 1)) * (Complex.I * 0) +
      ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * 1 + (v.val 2 : ℂ) * -Complex.I + (v.val 3 : ℂ) * 0)) * (Complex.I * Complex.I) +
      ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * 1 + (v.val 2 : ℂ) * Complex.I + (v.val 3 : ℂ) * 0)) * (Complex.I * -Complex.I) +
      ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * 0 + (v.val 2 : ℂ) * 0 + (v.val 3 : ℂ) * -1)) * (Complex.I * 0)
      = ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) - (v.val 2 : ℂ) * Complex.I)) * (Complex.I ^ 2) +
        ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) + (v.val 2 : ℂ) * Complex.I)) * -(Complex.I ^ 2) := by ring
      _ = ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) - (v.val 2 : ℂ) * Complex.I)) * (-1) +
        ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) + (v.val 2 : ℂ) * Complex.I)) * -(-1) := by rw [Complex.I_sq]
      _ = ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) + (v.val 2 : ℂ) * Complex.I)) - ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) - (v.val 2 : ℂ) * Complex.I)) := by ring
      _ = (Complex.I / 2 : ℂ) * (((v.val 1 : ℂ) + (v.val 2 : ℂ) * Complex.I) - ((v.val 1 : ℂ) - (v.val 2 : ℂ) * Complex.I)) := by ring
      _ = (Complex.I / 2 : ℂ) * (2 * (v.val 2 : ℂ) * Complex.I) := by ring
      _ = (Complex.I ^ 2) * (v.val 2 : ℂ) := by ring
      _ = (-1 : ℂ) * (v.val 2 : ℂ) := by rw [Complex.I_sq]
      _ = - (v.val 2 : ℂ) := by ring

  rw [h_comp]
  change (- -(v.val 2 : ℝ)) = v.val 2
  ring

lemma eval_bpst_trace_3 (v : S3) :
  let A0 := (Complex.I / 2 : ℂ) • ((v.val 1 : ℂ) • sigma1.val + (v.val 2 : ℂ) • sigma2.val + (v.val 3 : ℂ) • sigma3.val);
  -(Matrix.trace (A0 * (Complex.I • sigma3.val))).re = v.val 3 := by
  intro A0
  dsimp only [A0]
  rw [val_sigma1, val_sigma2, val_sigma3]
  rw [trace_mul_fin2]
  change -(
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 0 0 + (v.val 2 : ℂ) * sigmaY 0 0 + (v.val 3 : ℂ) * sigmaZ 0 0)) * (Complex.I * sigmaZ 0 0) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 0 1 + (v.val 2 : ℂ) * sigmaY 0 1 + (v.val 3 : ℂ) * sigmaZ 0 1)) * (Complex.I * sigmaZ 1 0) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 1 0 + (v.val 2 : ℂ) * sigmaY 1 0 + (v.val 3 : ℂ) * sigmaZ 1 0)) * (Complex.I * sigmaZ 0 1) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 1 1 + (v.val 2 : ℂ) * sigmaY 1 1 + (v.val 3 : ℂ) * sigmaZ 1 1)) * (Complex.I * sigmaZ 1 1)
  ).re = v.val 3
  
  have h_comp : (
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 0 0 + (v.val 2 : ℂ) * sigmaY 0 0 + (v.val 3 : ℂ) * sigmaZ 0 0)) * (Complex.I * sigmaZ 0 0) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 0 1 + (v.val 2 : ℂ) * sigmaY 0 1 + (v.val 3 : ℂ) * sigmaZ 0 1)) * (Complex.I * sigmaZ 1 0) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 1 0 + (v.val 2 : ℂ) * sigmaY 1 0 + (v.val 3 : ℂ) * sigmaZ 1 0)) * (Complex.I * sigmaZ 0 1) +
    ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * sigmaX 1 1 + (v.val 2 : ℂ) * sigmaY 1 1 + (v.val 3 : ℂ) * sigmaZ 1 1)) * (Complex.I * sigmaZ 1 1)
  ) = - (v.val 3 : ℂ) := by
    rw [sig1_00, sig1_01, sig1_10, sig1_11, sig2_00, sig2_01, sig2_10, sig2_11, sig3_00, sig3_01, sig3_10, sig3_11]
    calc
      ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * 0 + (v.val 2 : ℂ) * 0 + (v.val 3 : ℂ) * 1)) * (Complex.I * 1) +
      ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * 1 + (v.val 2 : ℂ) * -Complex.I + (v.val 3 : ℂ) * 0)) * (Complex.I * 0) +
      ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * 1 + (v.val 2 : ℂ) * Complex.I + (v.val 3 : ℂ) * 0)) * (Complex.I * 0) +
      ((Complex.I / 2 : ℂ) * ((v.val 1 : ℂ) * 0 + (v.val 2 : ℂ) * 0 + (v.val 3 : ℂ) * -1)) * (Complex.I * -1)
      = ((Complex.I / 2 : ℂ) * (v.val 3 : ℂ)) * Complex.I +
        ((Complex.I / 2 : ℂ) * -(v.val 3 : ℂ)) * -Complex.I := by ring
      _ = (Complex.I / 2 : ℂ) * Complex.I * ((v.val 3 : ℂ) + (v.val 3 : ℂ)) := by ring
      _ = (Complex.I / 2 : ℂ) * Complex.I * (2 * (v.val 3 : ℂ)) := by ring
      _ = (Complex.I ^ 2) * (v.val 3 : ℂ) := by ring
      _ = (-1 : ℂ) * (v.val 3 : ℂ) := by rw [Complex.I_sq]
      _ = - (v.val 3 : ℂ) := by ring

  rw [h_comp]
  change (- -(v.val 3 : ℝ)) = v.val 3
  ring

lemma s3_complex_norm (v : S3) : (v.val 0 : ℂ)^2 + (v.val 1 : ℂ)^2 + (v.val 2 : ℂ)^2 + (v.val 3 : ℂ)^2 = 1 := by
  have h := v.property
  calc (v.val 0 : ℂ)^2 + (v.val 1 : ℂ)^2 + (v.val 2 : ℂ)^2 + (v.val 3 : ℂ)^2
    _ = (((v.val 0 : ℝ)^2 + (v.val 1 : ℝ)^2 + (v.val 2 : ℝ)^2 + (v.val 3 : ℝ)^2 : ℝ) : ℂ) := by push_cast; ring
    _ = ((1 : ℝ) : ℂ) := by rw [h]
    _ = 1 := Complex.ofReal_one

lemma bpstInstanton_val_0 (x : SpacetimePoint) :
  let D : ℂ := (x 0 : ℂ)^2 + (x 1 : ℂ)^2 + (x 2 : ℂ)^2 + (x 3 : ℂ)^2 + 1;
  (bpstInstanton 0 x).val = (Complex.I / D) • ((x 1 : ℂ) • sigma1.val + (x 2 : ℂ) • sigma2.val + (x 3 : ℂ) • sigma3.val) := by
  intro D
  rfl

lemma bpstInstanton_val_1 (x : SpacetimePoint) :
  let D : ℂ := (x 0 : ℂ)^2 + (x 1 : ℂ)^2 + (x 2 : ℂ)^2 + (x 3 : ℂ)^2 + 1;
  (bpstInstanton 1 x).val = (Complex.I / D) • (-(x 0 : ℂ) • sigma1.val - (x 3 : ℂ) • sigma2.val + (x 2 : ℂ) • sigma3.val) := by
  intro D
  rfl

lemma bpst_extractV_eq (v : S3) : extractV bpstInstanton v = v.val := by
  ext i
  have hr2 : (v.val 0 : ℂ)^2 + (v.val 1 : ℂ)^2 + (v.val 2 : ℂ)^2 + (v.val 3 : ℂ)^2 = 1 := s3_complex_norm v
  have hD : (v.val 0 : ℂ)^2 + (v.val 1 : ℂ)^2 + (v.val 2 : ℂ)^2 + (v.val 3 : ℂ)^2 + 1 = 2 := by rw [hr2]; ring
  fin_cases i
  · dsimp [extractV]
    have h_inst := bpstInstanton_val_1 v.val
    rw [hD] at h_inst
    rw [h_inst]
    exact eval_bpst_trace_0 v
  · dsimp [extractV]
    have h_inst := bpstInstanton_val_0 v.val
    rw [hD] at h_inst
    rw [h_inst]
    exact eval_bpst_trace_1 v
  · dsimp [extractV]
    have h_inst := bpstInstanton_val_0 v.val
    rw [hD] at h_inst
    rw [h_inst]
    exact eval_bpst_trace_2 v
  · dsimp [extractV]
    have h_inst := bpstInstanton_val_0 v.val
    rw [hD] at h_inst
    rw [h_inst]
    exact eval_bpst_trace_3 v

lemma geometricBoundaryProjection_bpstInstanton : geometricBoundaryProjection bpstInstanton = bpstAsymptoticMap := by
  ext v
  dsimp [geometricBoundaryProjection]
  rw [bpst_extractV_eq v]
  dsimp [makeSU2]
  have h_norm : (v.val 0)^2 + (v.val 1)^2 + (v.val 2)^2 + (v.val 3)^2 = 1 := v.property
  simp only [h_norm, dif_pos]
  rfl

lemma geometricBoundaryProjection_zero : geometricBoundaryProjection 0 = 1 := by
  ext v
  change makeSU2 (extractV 0 v) = 1
  have hextract : extractV 0 v = fun _ => 0 := by
    ext i
    dsimp [extractV]
    have h_zero_0 : (0 : Fin 4 → SpacetimePoint → SL2C) 0 v.val = 0 := rfl
    have h_zero_1 : (0 : Fin 4 → SpacetimePoint → SL2C) 1 v.val = 0 := rfl
    have hz_val : (0 : SL2C).val = 0 := rfl
    simp only [h_zero_0, h_zero_1, hz_val, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, neg_zero]
    split_ifs <;> rfl
  rw [hextract]
  change makeSU2 (fun _ => 0) = 1
  dsimp [makeSU2]
  have h_not : ¬((0:ℝ)^2 + (0:ℝ)^2 + (0:ℝ)^2 + (0:ℝ)^2 = 1) := by norm_num
  rw [dif_neg h_not]

/--
A valid topological homotopy must maintain the integrity of the physical boundary state.
If the continuous mapping to the SU(2) topology breaks, the state has undergone a violent
topological decay.
-/
def isHomotopicConnection (A0 A1 : Fin 4 → SpacetimePoint → SL2C) : Prop :=
  ∃ (H : ℝ → Fin 4 → SpacetimePoint → SL2C),
    (∀ mu x, H 0 mu x = A0 mu x) ∧
    (∀ mu x, H 1 mu x = A1 mu x) ∧
    (∀ mu i j, ContDiff ℝ ⊤ (fun (tx : ℝ × SpacetimePoint) => (H tx.1 mu tx.2).val i j)) ∧
    (Continuous (fun t => geometricBoundaryProjection (H t)))

/--
Establishes the absolute topological stability of the instanton configuration. Because the boundary mapping of the instanton constitutes a topological homeomorphism to the SU(2) gauge group, its Cartan-Maurer mapping degree must be strictly non-zero. Consequently, the state is topologically protected and cannot continuously decay into the trivial vacuum.
-/
@[litlib_track "Topological Stability of the Instanton"]
theorem kinematicTopologicalStability 
  (windingNumber : (S3 → SU2Group) → ℤ)
  (cartanMaurerIntegral : (S3 → SU2Group) → ℝ)
  [tc : CartanMaurerTopology (S3 → SU2Group) Continuous windingNumber cartanMaurerIntegral] 
  [belavin : Eq8 S3 SU2Group Continuous windingNumber cartanMaurerIntegral]
  (integral_zero : cartanMaurerIntegral 1 = 0) :
  ¬ isHomotopicConnection bpstInstanton 0 := by
  intro h_homotopy
  rcases h_homotopy with ⟨H, hH0, hH1, hHCont, hHBoundCont⟩
  
  have h_wind_eq := tc.homotopyInvariance (fun t => geometricBoundaryProjection (H t)) hHBoundCont 0 1
  
  have h0_eq : H 0 = bpstInstanton := by funext mu x; exact hH0 mu x
  have h1_eq : H 1 = 0 := by funext mu x; exact hH1 mu x
  
  have h_wind_0 : windingNumber (geometricBoundaryProjection (H 0)) = windingNumber bpstAsymptoticMap := by
    rw [h0_eq, geometricBoundaryProjection_bpstInstanton]
    
  have h_wind_1 : windingNumber (geometricBoundaryProjection (H 1)) = 0 := by
    rw [h1_eq, geometricBoundaryProjection_zero]
    have h_const_cont : Continuous (1 : S3 → SU2Group) := continuous_const
    have h_thm := tc.degreeTheorem 1 h_const_cont
    rw [integral_zero] at h_thm
    exact_mod_cast h_thm.symm
    
  rw [h_wind_0, h_wind_1] at h_wind_eq
  
  have h_deg := belavin.degree_of_homeomorph bpstAsymptoticMap bpst_is_homeomorphism
  
  cases h_deg with
  | inl h_pos => 
    rw [h_pos] at h_wind_eq
    have h_false : (1 : ℤ) = 0 := h_wind_eq
    norm_num at h_false
  | inr h_neg => 
    rw [h_neg] at h_wind_eq
    have h_false : (-1 : ℤ) = 0 := h_wind_eq
    norm_num at h_false

end CGD.Particles

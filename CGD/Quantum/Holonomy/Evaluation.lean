-- FILENAME: CGD/Quantum/Holonomy/Evaluation.lean

import Litlib.Core
import CGD.Quantum.Holonomy.Geometric
import CGD.Quantum.Holonomy.Euler
import CGD.Quantum.Definitions
import CGD.Axioms.PhysicalUniverse
import Litlib.Y2000.hall2000elementary.Signature

set_option linter.unusedSimpArgs false

namespace CGD.Quantum

open CGD.Foundations CGD.Math CGD.Axioms Complex Matrix Litlib.Y2000.hall2000elementary

noncomputable def straightLinePath (t : ℝ) : SpacetimePoint := fun _ => t

noncomputable def obsM (alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let R := Matrix.of ![![Complex.cos (alpha/2), -Complex.sin (alpha/2)], ![Complex.sin (alpha/2), Complex.cos (alpha/2)]]
  let rInv := Matrix.of ![![Complex.cos (alpha/2), Complex.sin (alpha/2)], ![-Complex.sin (alpha/2), Complex.cos (alpha/2)]]
  R * sigma3.val * rInv

@[litlib_track "Geometric Holonomy"]
-- NATIVE EVALUATION: The exact path-ordered exponential for a constant field
noncomputable def holonomy (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (A : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (t0 t1 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  matrixExp ((t1 - t0 : ℂ) • A t0)

@[litlib_track "Macroscopic Observable"]
noncomputable def macroscopicObservable
  (holonomy : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
  (A : Fin 4 → SpacetimePoint → SL2C)
  (mu : Fin 4) (L : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  holonomy (fun t => (A mu (straightLinePath t)).val) 0 L

lemma rInvREqOne (alpha : ℝ) :
  (Matrix.of ![![Complex.cos (alpha/2), Complex.sin (alpha/2)], ![-Complex.sin (alpha/2), Complex.cos (alpha/2)]] : Matrix (Fin 2) (Fin 2) ℂ) *
  Matrix.of ![![Complex.cos (alpha/2), -Complex.sin (alpha/2)], ![Complex.sin (alpha/2), Complex.cos (alpha/2)]] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h : Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
    calc Complex.cos (alpha / 2 : ℂ) * Complex.cos (alpha / 2 : ℂ) + Complex.sin (alpha / 2 : ℂ) * Complex.sin (alpha / 2 : ℂ)
      = Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 := by ring
      _ = 1 := h
  · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h : Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
    calc Complex.sin (alpha / 2 : ℂ) * Complex.sin (alpha / 2 : ℂ) + Complex.cos (alpha / 2 : ℂ) * Complex.cos (alpha / 2 : ℂ)
      = Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 := by ring
      _ = 1 := h

lemma rRInvEqOne (alpha : ℝ) :
  (Matrix.of ![![Complex.cos (alpha/2), -Complex.sin (alpha/2)], ![Complex.sin (alpha/2), Complex.cos (alpha/2)]] : Matrix (Fin 2) (Fin 2) ℂ) *
  Matrix.of ![![Complex.cos (alpha/2), Complex.sin (alpha/2)], ![-Complex.sin (alpha/2), Complex.cos (alpha/2)]] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h : Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
    calc Complex.cos (alpha / 2 : ℂ) * Complex.cos (alpha / 2 : ℂ) + Complex.sin (alpha / 2 : ℂ) * Complex.sin (alpha / 2 : ℂ)
      = Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 := by ring
      _ = 1 := h
  · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h : Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
    calc Complex.sin (alpha / 2 : ℂ) * Complex.sin (alpha / 2 : ℂ) + Complex.cos (alpha / 2 : ℂ) * Complex.cos (alpha / 2 : ℂ)
      = Complex.sin (alpha / 2 : ℂ) ^ 2 + Complex.cos (alpha / 2 : ℂ) ^ 2 := by ring
      _ = 1 := h

lemma hSum2 (f : Fin 2 → ℂ) : ∑ i : Fin 2, f i = f 0 + f 1 := Fin.sum_univ_two f

lemma obsMSq (alpha : ℝ) : obsM alpha * obsM alpha = 1 := by
  dsimp [obsM]
  have hInv := rInvREqOne alpha
  have hR := rRInvEqOne alpha
  let R : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![Complex.cos (alpha/2), -Complex.sin (alpha/2)], ![Complex.sin (alpha/2), Complex.cos (alpha/2)]]
  let rInv : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![Complex.cos (alpha/2), Complex.sin (alpha/2)], ![-Complex.sin (alpha/2), Complex.cos (alpha/2)]]

  have hSig : sigma3.val * sigma3.val = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals {
      simp [sigma3, toSl2c, sigmaZ, mkMat, Matrix.mul_apply, Matrix.trace, Matrix.diag, hSum2]
    }

  calc (R * sigma3.val * rInv) * (R * sigma3.val * rInv)
    = R * (sigma3.val * (rInv * (R * (sigma3.val * rInv)))) := by simp only [Matrix.mul_assoc]
    _ = R * (sigma3.val * ((rInv * R) * (sigma3.val * rInv))) := by rw [← Matrix.mul_assoc rInv R (sigma3.val * rInv)]
    _ = R * (sigma3.val * (1 * (sigma3.val * rInv))) := by rw [hInv]
    _ = R * (sigma3.val * (sigma3.val * rInv)) := by rw [Matrix.one_mul]
    _ = R * ((sigma3.val * sigma3.val) * rInv) := by rw [← Matrix.mul_assoc sigma3.val sigma3.val rInv]
    _ = R * (1 * rInv) := by rw [hSig]
    _ = R * rInv := by rw [Matrix.one_mul]
    _ = 1 := hR

lemma iObsMTraceZero (alpha : ℝ) : Matrix.trace (Complex.I • obsM alpha) = 0 := by
  dsimp [obsM]
  simp [Matrix.trace, Matrix.diag, sigma3, toSl2c, sigmaZ, mkMat, Matrix.smul_apply, hSum2]
  ring

lemma iObsMToSl2c (alpha : ℝ) : (toSl2c (Complex.I • obsM alpha)).val = Complex.I • obsM alpha := by
  ext i j
  dsimp [toSl2c]
  have hz := iObsMTraceZero alpha
  rw [hz]
  simp

lemma fluxTubeFrameOneVal (t : ℝ) : (fluxTubeFrame 1 (straightLinePath t)).val = Complex.I • sigma3.val := by
  dsimp [fluxTubeFrame]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    simp [toSl2c, sigma3, sigmaZ, mkMat, Matrix.trace, Matrix.diag, Matrix.smul_apply, hSum2]
  }

lemma rConjTranspose (alpha : ℝ) :
  (Matrix.of ![![Complex.cos (alpha/2), -Complex.sin (alpha/2)], ![Complex.sin (alpha/2), Complex.cos (alpha/2)]] : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose =
  Matrix.of ![![Complex.cos (alpha/2), Complex.sin (alpha/2)], ![-Complex.sin (alpha/2), Complex.cos (alpha/2)]] := by
  ext i j
  have hz : (alpha / 2 : ℂ) = ↑(alpha / 2 : ℝ) := by push_cast; ring
  have hc : star (Complex.cos (alpha / 2 : ℂ)) = Complex.cos (alpha / 2 : ℂ) := by rw [hz, starCosReal]
  have hs : star (Complex.sin (alpha / 2 : ℂ)) = Complex.sin (alpha / 2 : ℂ) := by rw [hz, starSinReal]
  fin_cases i <;> fin_cases j
  · dsimp [Matrix.conjTranspose_apply, Matrix.of_apply]; exact hc
  · dsimp [Matrix.conjTranspose_apply, Matrix.of_apply]; exact hs
  · dsimp [Matrix.conjTranspose_apply, Matrix.of_apply]; change star (-Complex.sin (alpha / 2 : ℂ)) = -Complex.sin (alpha / 2 : ℂ); rw [star_neg, hs]
  · dsimp [Matrix.conjTranspose_apply, Matrix.of_apply]; exact hc

lemma rInvConjTranspose (alpha : ℝ) :
  (Matrix.of ![![Complex.cos (alpha/2), Complex.sin (alpha/2)], ![-Complex.sin (alpha/2), Complex.cos (alpha/2)]] : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose =
  Matrix.of ![![Complex.cos (alpha/2), -Complex.sin (alpha/2)], ![Complex.sin (alpha/2), Complex.cos (alpha/2)]] := by
  ext i j
  have hz : (alpha / 2 : ℂ) = ↑(alpha / 2 : ℝ) := by push_cast; ring
  have hc : star (Complex.cos (alpha / 2 : ℂ)) = Complex.cos (alpha / 2 : ℂ) := by rw [hz, starCosReal]
  have hs : star (Complex.sin (alpha / 2 : ℂ)) = Complex.sin (alpha / 2 : ℂ) := by rw [hz, starSinReal]
  fin_cases i <;> fin_cases j
  · dsimp [Matrix.conjTranspose_apply, Matrix.of_apply]; exact hc
  · dsimp [Matrix.conjTranspose_apply, Matrix.of_apply]; change star (-Complex.sin (alpha / 2 : ℂ)) = -Complex.sin (alpha / 2 : ℂ); rw [star_neg, hs]
  · dsimp [Matrix.conjTranspose_apply, Matrix.of_apply]; exact hs
  · dsimp [Matrix.conjTranspose_apply, Matrix.of_apply]; exact hc

lemma sigma3ConjTranspose : (sigma3.val).conjTranspose = sigma3.val := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    dsimp [Matrix.conjTranspose_apply, sigma3, toSl2c, sigmaZ, mkMat, Matrix.trace, Matrix.diag, hSum2]
    norm_num
  }

/-- Proves the macroscopic spatial observable matrix is strictly Hermitian -/
lemma obsMConjTranspose (alpha : ℝ) : (obsM alpha).conjTranspose = obsM alpha := by
  dsimp [obsM]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  rw [rInvConjTranspose alpha]
  rw [sigma3ConjTranspose]
  rw [rConjTranspose alpha]
  rw [Matrix.mul_assoc]

@[litlib_track "Macroscopic Observable is Unitary"]
lemma obsHolonomyIsUnitary (alpha L : ℝ) :
  let U := (Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Complex.sin (L:ℂ)) • obsM alpha;
  U * U.conjTranspose = 1 := by
  intro U
  
  have hMSq := obsMSq alpha
  
  have hUH : U.conjTranspose = (Complex.cos (L:ℂ)) • 1 - (Complex.I * Complex.sin (L:ℂ)) • obsM alpha := by
    dsimp [U]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul]
    rw [Matrix.conjTranspose_one, obsMConjTranspose alpha]
    have hStarCos : star (Complex.cos (L:ℂ)) = Complex.cos (L:ℂ) := starCosReal L
    have hStarIsin : star (Complex.I * Complex.sin (L:ℂ)) = - (Complex.I * Complex.sin (L:ℂ)) := by
      calc star (Complex.I * Complex.sin (L:ℂ))
        = star (Complex.sin (L:ℂ)) * star Complex.I := StarMul.star_mul Complex.I (Complex.sin (L:ℂ))
        _ = Complex.sin (L:ℂ) * (-Complex.I) := by rw [starSinReal L, star_def, conj_I]
        _ = - (Complex.I * Complex.sin (L:ℂ)) := by ring
    rw [hStarCos, hStarIsin]
    change Complex.cos (L:ℂ) • 1 + -(Complex.I * Complex.sin (L:ℂ)) • obsM alpha = _
    rw [neg_smul, sub_eq_add_neg]

  rw [hUH]
  dsimp [U]
  rw [add_mul, mul_sub, mul_sub]
  have h1 : ((Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((Complex.cos (L:ℂ)) • 1) = (Complex.cos (L:ℂ) ^ 2) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, smul_smul, sq]
  have h2 : ((Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((Complex.I * Complex.sin (L:ℂ)) • obsM alpha) = (Complex.cos (L:ℂ) * (Complex.I * Complex.sin (L:ℂ))) • obsM alpha := by
    rw [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, smul_smul]
  have h3 : ((Complex.I * Complex.sin (L:ℂ)) • obsM alpha) * ((Complex.cos (L:ℂ)) • 1) = ((Complex.I * Complex.sin (L:ℂ)) * Complex.cos (L:ℂ)) • obsM alpha := by
    rw [smul_mul_assoc, mul_smul_comm, Matrix.mul_one, smul_smul]
  have h4 : ((Complex.I * Complex.sin (L:ℂ)) • obsM alpha) * ((Complex.I * Complex.sin (L:ℂ)) • obsM alpha) = (-Complex.sin (L:ℂ) ^ 2) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, hMSq, smul_smul]
    congr 1
    calc Complex.I * Complex.sin (L:ℂ) * (Complex.I * Complex.sin (L:ℂ))
      = (Complex.I * Complex.I) * Complex.sin (L:ℂ) ^ 2 := by ring
      _ = -1 * Complex.sin (L:ℂ) ^ 2 := by rw [Complex.I_mul_I]
      _ = -Complex.sin (L:ℂ) ^ 2 := by ring
  rw [h1, h2, h3, h4]
  have hz : Complex.cos (L:ℂ) * (Complex.I * Complex.sin (L:ℂ)) = Complex.I * Complex.sin (L:ℂ) * Complex.cos (L:ℂ) := by ring
  rw [hz]
  have hSimp : ∀ A B C : Matrix (Fin 2) (Fin 2) ℂ, A - B + (B - C) = A - C := by intro A B C; abel
  rw [hSimp]
  rw [← sub_smul]
  have hTrig : Complex.cos (L:ℂ) ^ 2 - (-Complex.sin (L:ℂ) ^ 2) = 1 := by
    calc Complex.cos (L:ℂ) ^ 2 - (-Complex.sin (L:ℂ) ^ 2)
      = Complex.sin (L:ℂ) ^ 2 + Complex.cos (L:ℂ) ^ 2 := by ring
      _ = 1 := Complex.sin_sq_add_cos_sq (L:ℂ)
  rw [hTrig, one_smul]

@[litlib_track "Macroscopic Observable is Unimodular"]
lemma obsHolonomyIsUnimodular (alpha L : ℝ) :
  let U := (Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Complex.sin (L:ℂ)) • obsM alpha;
  Matrix.det U = 1 := by
  intro U
  dsimp [U]
  
  have hTraceDef : Matrix.trace (Complex.I • obsM alpha) = (Complex.I • obsM alpha) 0 0 + (Complex.I • obsM alpha) 1 1 := by
    change ∑ i, (Complex.I • obsM alpha) i i = _
    rw [hSum2]
  have hI := iObsMTraceZero alpha
  rw [hTraceDef] at hI
  
  have hc : Complex.I * (obsM alpha 0 0 + obsM alpha 1 1) = 0 := by
    calc Complex.I * (obsM alpha 0 0 + obsM alpha 1 1)
      = Complex.I * obsM alpha 0 0 + Complex.I * obsM alpha 1 1 := by ring
      _ = (Complex.I • obsM alpha) 0 0 + (Complex.I • obsM alpha) 1 1 := rfl
      _ = 0 := hI
      
  have ht : obsM alpha 0 0 + obsM alpha 1 1 = 0 := by
    cases mul_eq_zero.mp hc with
    | inl h => exfalso; exact Complex.I_ne_zero h
    | inr h => exact h
    
  have hTComm : obsM alpha 1 1 + obsM alpha 0 0 = 0 := by rw [add_comm, ht]
  have hTr : obsM alpha 1 1 = - obsM alpha 0 0 := eq_neg_iff_add_eq_zero.mpr hTComm
  
  have hMSq := obsMSq alpha
  have hSqExpand : obsM alpha 0 0 * obsM alpha 0 0 + obsM alpha 0 1 * obsM alpha 1 0 = 1 := by
    calc obsM alpha 0 0 * obsM alpha 0 0 + obsM alpha 0 1 * obsM alpha 1 0
      = (obsM alpha * obsM alpha) 0 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
      _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [hMSq]
      _ = 1 := rfl
      
  have hDetM : obsM alpha 0 0 * -obsM alpha 0 0 - obsM alpha 0 1 * obsM alpha 1 0 = -1 := by
    calc obsM alpha 0 0 * -obsM alpha 0 0 - obsM alpha 0 1 * obsM alpha 1 0
      = - (obsM alpha 0 0 * obsM alpha 0 0 + obsM alpha 0 1 * obsM alpha 1 0) := by ring
      _ = -1 := by rw [hSqExpand]
      
  have hU00 : ((Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Complex.sin (L:ℂ)) • obsM alpha) 0 0 = Complex.cos (L:ℂ) + Complex.I * Complex.sin (L:ℂ) * obsM alpha 0 0 := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    change Complex.cos (L:ℂ) * 1 + (Complex.I * Complex.sin (L:ℂ)) * obsM alpha 0 0 = _
    ring
  have hU11 : ((Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Complex.sin (L:ℂ)) • obsM alpha) 1 1 = Complex.cos (L:ℂ) + Complex.I * Complex.sin (L:ℂ) * obsM alpha 1 1 := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    change Complex.cos (L:ℂ) * 1 + (Complex.I * Complex.sin (L:ℂ)) * obsM alpha 1 1 = _
    ring
  have hU01 : ((Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Complex.sin (L:ℂ)) • obsM alpha) 0 1 = Complex.I * Complex.sin (L:ℂ) * obsM alpha 0 1 := by
    have hNe : (0 : Fin 2) ≠ 1 := by decide
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hNe]
    change Complex.cos (L:ℂ) * 0 + (Complex.I * Complex.sin (L:ℂ)) * obsM alpha 0 1 = _
    ring
  have hU10 : ((Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Complex.sin (L:ℂ)) • obsM alpha) 1 0 = Complex.I * Complex.sin (L:ℂ) * obsM alpha 1 0 := by
    have hNe : (1 : Fin 2) ≠ 0 := by decide
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hNe]
    change Complex.cos (L:ℂ) * 0 + (Complex.I * Complex.sin (L:ℂ)) * obsM alpha 1 0 = _
    ring

  calc Matrix.det ((Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Complex.sin (L:ℂ)) • obsM alpha)
    = ((Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Complex.sin (L:ℂ)) • obsM alpha) 0 0 * ((Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Complex.sin (L:ℂ)) • obsM alpha) 1 1 - ((Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Complex.sin (L:ℂ)) • obsM alpha) 0 1 * ((Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Complex.sin (L:ℂ)) • obsM alpha) 1 0 := by rw [Matrix.det_fin_two]
    _ = (Complex.cos (L:ℂ) + Complex.I * Complex.sin (L:ℂ) * obsM alpha 0 0) * (Complex.cos (L:ℂ) + Complex.I * Complex.sin (L:ℂ) * obsM alpha 1 1) - (Complex.I * Complex.sin (L:ℂ) * obsM alpha 0 1) * (Complex.I * Complex.sin (L:ℂ) * obsM alpha 1 0) := by rw [hU00, hU11, hU01, hU10]
    _ = (Complex.cos (L:ℂ) + Complex.I * Complex.sin (L:ℂ) * obsM alpha 0 0) * (Complex.cos (L:ℂ) + Complex.I * Complex.sin (L:ℂ) * -obsM alpha 0 0) - (Complex.I * Complex.sin (L:ℂ) * obsM alpha 0 1) * (Complex.I * Complex.sin (L:ℂ) * obsM alpha 1 0) := by rw [hTr]
    _ = Complex.cos (L:ℂ)^2 - (Complex.I * Complex.sin (L:ℂ))^2 * (obsM alpha 0 0 * -(-obsM alpha 0 0) + obsM alpha 0 1 * obsM alpha 1 0) := by ring
    _ = Complex.cos (L:ℂ)^2 - (-Complex.sin (L:ℂ)^2) * (- (obsM alpha 0 0 * -obsM alpha 0 0 - obsM alpha 0 1 * obsM alpha 1 0)) := by
      congr 2
      · calc (Complex.I * Complex.sin (L:ℂ))^2 = Complex.I^2 * Complex.sin (L:ℂ)^2 := by ring
          _ = -1 * Complex.sin (L:ℂ)^2 := by rw [Complex.I_sq]
          _ = -Complex.sin (L:ℂ)^2 := by ring
      · ring
    _ = Complex.cos (L:ℂ)^2 - (-Complex.sin (L:ℂ)^2) * (- (-1)) := by rw [hDetM]
    _ = Complex.cos (L:ℂ)^2 + Complex.sin (L:ℂ)^2 := by ring
    _ = Complex.sin (L:ℂ)^2 + Complex.cos (L:ℂ)^2 := by ring
    _ = 1 := Complex.sin_sq_add_cos_sq (L:ℂ)

@[litlib_track "Macroscopic Observable is SU(2)"]
lemma obsHolonomyIsSu2 (alpha L : ℝ) :
  let U := (Complex.cos (L:ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Complex.sin (L:ℂ)) • obsM alpha;
  U * U.conjTranspose = 1 ∧ Matrix.det U = 1 := by
  intro U
  exact ⟨obsHolonomyIsUnitary alpha L, obsHolonomyIsUnimodular alpha L⟩

section HolonomyEvaluation

variable (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
variable [DerivativeExponential (Fin 2) matrixExp]
variable (pu : PhysicalUniverse)

@[litlib_track "Macroscopic Spin State Witness"]
theorem fluxTubeHolonomyEvaluation
  (alpha L : ℝ)
  (hField : ∀ t, pu.toUniverse.sd_sector 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t)) :
  macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha mu p) 1 L =
  (Complex.cos (L:ℂ)) • 1 + (Complex.I * Complex.sin (L:ℂ)) • obsM alpha := by

  dsimp [macroscopicObservable, holonomy]

  have hf : (pu.toUniverse.sd_sector 1 (straightLinePath 0)).val = (fluxTubeFrame 1 (straightLinePath 0)).val :=
    congr_arg Subtype.val (hField 0)

  have hEval : (rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha 1 (straightLinePath 0)).val =
                Complex.I • obsM alpha := by
    dsimp [rotateYAxis]
    rw [hf]
    have hFlux := fluxTubeFrameOneVal 0
    rw [hFlux]

    have hAssoc : Matrix.of ![![Complex.cos (alpha / 2 : ℂ), -Complex.sin (alpha / 2 : ℂ)], ![Complex.sin (alpha / 2 : ℂ), Complex.cos (alpha / 2 : ℂ)]] *
                   (Complex.I • sigma3.val) *
                   Matrix.of ![![Complex.cos (alpha / 2 : ℂ), Complex.sin (alpha / 2 : ℂ)], ![-Complex.sin (alpha / 2 : ℂ), Complex.cos (alpha / 2 : ℂ)]] =
                   Complex.I • obsM alpha := by
      dsimp [obsM]
      rw [Matrix.mul_smul, Matrix.smul_mul]

    rw [hAssoc]
    exact iObsMToSl2c alpha

  rw [hEval]

  have hz : ((L : ℂ) - (0 : ℂ)) = (L : ℂ) := sub_zero _
  rw [hz]

  have hArg : (L : ℂ) • Complex.I • obsM alpha = (Complex.I * (L : ℂ)) • obsM alpha := by
    rw [smul_smul]
    congr 1
    ring
  rw [hArg]

  exact matrixEulerFormula matrixExp (obsM alpha) L (obsMSq alpha)

lemma cosEqHalf (a : ℂ) : Complex.cos a = Complex.cos (a/2) * Complex.cos (a/2) - Complex.sin (a/2) * Complex.sin (a/2) := by
  have H := Complex.cos_add (a/2) (a/2)
  have hAdd : a/2 + a/2 = a := by ring
  rw [hAdd] at H
  exact H

lemma sinEqHalf (a : ℂ) : Complex.sin a = Complex.sin (a/2) * Complex.cos (a/2) + Complex.cos (a/2) * Complex.sin (a/2) := by
  have H := Complex.sin_add (a/2) (a/2)
  have hAdd : a/2 + a/2 = a := by ring
  rw [hAdd] at H
  exact H

lemma obsMEq (a : ℝ) : obsM a = Matrix.of ![![Complex.cos (a : ℂ), Complex.sin (a : ℂ)], ![Complex.sin (a : ℂ), -Complex.cos (a : ℂ)]] := by
  dsimp [obsM]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, sigma3, toSl2c, sigmaZ, mkMat, Matrix.trace, Matrix.diag]
    rw [cosEqHalf (a : ℂ)]
    try ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, sigma3, toSl2c, sigmaZ, mkMat, Matrix.trace, Matrix.diag]
    rw [sinEqHalf (a : ℂ)]
    try ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, sigma3, toSl2c, sigmaZ, mkMat, Matrix.trace, Matrix.diag]
    rw [sinEqHalf (a : ℂ)]
    try ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, sigma3, toSl2c, sigmaZ, mkMat, Matrix.trace, Matrix.diag]
    rw [cosEqHalf (a : ℂ)]
    try ring

lemma traceObsMMul (a b : ℝ) : Matrix.trace (obsM a * obsM b) = 2 * (Complex.cos (a : ℂ) * Complex.cos (b : ℂ) + Complex.sin (a : ℂ) * Complex.sin (b : ℂ)) := by
  rw [obsMEq a, obsMEq b]
  dsimp [Matrix.trace, Matrix.diag]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma corrPiDivTwo (a b : ℝ) :
  let A : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • obsM a
  let B : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • obsM b
  (1 / 2 : ℂ) * Matrix.trace (A * B.conjTranspose) = Complex.cos (a : ℂ) * Complex.cos (b : ℂ) + Complex.sin (a : ℂ) * Complex.sin (b : ℂ) := by
  intro A B
  have hBConj : B.conjTranspose = -Complex.I • obsM b := by
    change (Complex.I • obsM b).conjTranspose = -Complex.I • obsM b
    rw [Matrix.conjTranspose_smul, obsMConjTranspose b]
    have hc : star Complex.I = -Complex.I := by rw [star_def, conj_I]
    rw [hc]
  have hMul : A * B.conjTranspose = obsM a * obsM b := by
    change (Complex.I • obsM a) * B.conjTranspose = obsM a * obsM b
    rw [hBConj]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hz : Complex.I * -Complex.I = 1 := by
      calc Complex.I * -Complex.I = - (Complex.I * Complex.I) := by ring
        _ = - (-1) := by rw [Complex.I_mul_I]
        _ = 1 := by ring
    rw [hz, one_smul]
  rw [hMul]
  rw [traceObsMMul a b]
  ring

lemma realCorrEval (a b : ℝ) : 
  (Complex.cos (a : ℂ) * Complex.cos (b : ℂ) + Complex.sin (a : ℂ) * Complex.sin (b : ℂ)).re = Real.cos a * Real.cos b + Real.sin a * Real.sin b := by
  have H : Complex.cos (a : ℂ) * Complex.cos (b : ℂ) + Complex.sin (a : ℂ) * Complex.sin (b : ℂ) = Complex.cos (a - b : ℂ) := by
    have hc := Complex.cos_sub (a : ℂ) (b : ℂ)
    rw [hc]
  rw [H]
  have hz : (a - b : ℂ) = ((a - b : ℝ) : ℂ) := by push_cast; ring
  rw [hz]
  rw [← Complex.ofReal_cos]
  rw [Complex.ofReal_re]
  exact Real.cos_sub a b

@[litlib_track "Static Flux Tube Maximal CHSH Violation - Value"]
theorem staticFluxTubeMaximalViolationValue
  (L : ℝ)
  (hL : L = Real.pi / 2)
  (hField : ∀ t, pu.toUniverse.sd_sector 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t)) :
  
  let alphaA1 : ℝ := 0;
  let alphaA2 : ℝ := Real.pi / 2;
  let alphaB1 : ℝ := Real.pi / 4;
  let alphaB2 : ℝ := -(Real.pi / 4);

  let A1 : SU2Group := ⟨macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaA1 mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alphaA1 L hField]; exact obsHolonomyIsSu2 alphaA1 L⟩;
  let A2 : SU2Group := ⟨macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaA2 mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alphaA2 L hField]; exact obsHolonomyIsSu2 alphaA2 L⟩;
  let B1 : SU2Group := ⟨macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaB1 mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alphaB1 L hField]; exact obsHolonomyIsSu2 alphaB1 L⟩;
  let B2 : SU2Group := ⟨macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaB2 mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alphaB2 L hField]; exact obsHolonomyIsSu2 alphaB2 L⟩;
    
  let chsh := geometricBellCorrelation A1 B1 + geometricBellCorrelation A1 B2 +
              geometricBellCorrelation A2 B1 - geometricBellCorrelation A2 B2;
  
  (chsh.re)^2 = 8 := by
  
  intro alphaA1 alphaA2 alphaB1 alphaB2 A1 A2 B1 B2 chsh

  have hz : (L : ℂ).im = 0 := by rw [hL]; exact Complex.ofReal_im _
  have hLCos : Complex.cos L = 0 := by 
    rw [hL, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]

  have hLSin : Complex.sin L = 1 := by 
    rw [hL, ← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one]

  have hA1 : A1.val = Complex.I • obsM alphaA1 := by
    calc A1.val = macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaA1 mu p) 1 L := rfl
      _ = (Complex.cos (L:ℂ)) • 1 + (Complex.I * Complex.sin (L:ℂ)) • obsM alphaA1 := fluxTubeHolonomyEvaluation matrixExp pu alphaA1 L hField
      _ = (0 : ℂ) • 1 + (Complex.I * 1) • obsM alphaA1 := by rw [hLCos, hLSin]
      _ = Complex.I • obsM alphaA1 := by rw [zero_smul, zero_add, mul_one]
  
  have hA2 : A2.val = Complex.I • obsM alphaA2 := by
    calc A2.val = macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaA2 mu p) 1 L := rfl
      _ = (Complex.cos (L:ℂ)) • 1 + (Complex.I * Complex.sin (L:ℂ)) • obsM alphaA2 := fluxTubeHolonomyEvaluation matrixExp pu alphaA2 L hField
      _ = (0 : ℂ) • 1 + (Complex.I * 1) • obsM alphaA2 := by rw [hLCos, hLSin]
      _ = Complex.I • obsM alphaA2 := by rw [zero_smul, zero_add, mul_one]
    
  have hB1 : B1.val = Complex.I • obsM alphaB1 := by
    calc B1.val = macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaB1 mu p) 1 L := rfl
      _ = (Complex.cos (L:ℂ)) • 1 + (Complex.I * Complex.sin (L:ℂ)) • obsM alphaB1 := fluxTubeHolonomyEvaluation matrixExp pu alphaB1 L hField
      _ = (0 : ℂ) • 1 + (Complex.I * 1) • obsM alphaB1 := by rw [hLCos, hLSin]
      _ = Complex.I • obsM alphaB1 := by rw [zero_smul, zero_add, mul_one]
    
  have hB2 : B2.val = Complex.I • obsM alphaB2 := by
    calc B2.val = macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaB2 mu p) 1 L := rfl
      _ = (Complex.cos (L:ℂ)) • 1 + (Complex.I * Complex.sin (L:ℂ)) • obsM alphaB2 := fluxTubeHolonomyEvaluation matrixExp pu alphaB2 L hField
      _ = (0 : ℂ) • 1 + (Complex.I * 1) • obsM alphaB2 := by rw [hLCos, hLSin]
      _ = Complex.I • obsM alphaB2 := by rw [zero_smul, zero_add, mul_one]

  have hCorr (a b : ℝ) (A B : SU2Group) 
    (hA : A.val = Complex.I • obsM a) (hB : B.val = Complex.I • obsM b) :
    (geometricBellCorrelation A B).re = Real.cos a * Real.cos b + Real.sin a * Real.sin b := by
    have hTrace : (1 / 2 : ℂ) * Matrix.trace (A.val * B.val.conjTranspose) = 
      Complex.cos (a : ℂ) * Complex.cos (b : ℂ) + Complex.sin (a : ℂ) * Complex.sin (b : ℂ) := by
      rw [hA, hB]
      exact corrPiDivTwo a b
    have hGeom : geometricBellCorrelation A B = Complex.cos (a : ℂ) * Complex.cos (b : ℂ) + Complex.sin (a : ℂ) * Complex.sin (b : ℂ) := hTrace
    rw [hGeom]
    exact realCorrEval a b

  have hc1 : (geometricBellCorrelation A1 B1).re = Real.sqrt 2 / 2 := by
    rw [hCorr alphaA1 alphaB1 A1 B1 hA1 hB1]
    dsimp [alphaA1, alphaB1]
    have hCos0 : Real.cos 0 = 1 := Real.cos_zero
    have hSin0 : Real.sin 0 = 0 := Real.sin_zero
    have hCos4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    have hSin4 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    rw [hCos0, hSin0, hCos4, hSin4]
    ring
    
  have hc2 : (geometricBellCorrelation A1 B2).re = Real.sqrt 2 / 2 := by
    rw [hCorr alphaA1 alphaB2 A1 B2 hA1 hB2]
    dsimp [alphaA1, alphaB2]
    have hCos0 : Real.cos 0 = 1 := Real.cos_zero
    have hSin0 : Real.sin 0 = 0 := Real.sin_zero
    have hCos4 : Real.cos (-(Real.pi / 4)) = Real.sqrt 2 / 2 := by rw [Real.cos_neg, Real.cos_pi_div_four]
    have hSin4 : Real.sin (-(Real.pi / 4)) = -(Real.sqrt 2 / 2) := by rw [Real.sin_neg, Real.sin_pi_div_four]
    rw [hCos0, hSin0, hCos4, hSin4]
    ring
    
  have hc3 : (geometricBellCorrelation A2 B1).re = Real.sqrt 2 / 2 := by
    rw [hCorr alphaA2 alphaB1 A2 B1 hA2 hB1]
    dsimp [alphaA2, alphaB1]
    have hCos2 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
    have hSin2 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have hCos4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    have hSin4 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    rw [hCos2, hSin2, hCos4, hSin4]
    ring
    
  have hc4 : (geometricBellCorrelation A2 B2).re = - (Real.sqrt 2 / 2) := by
    rw [hCorr alphaA2 alphaB2 A2 B2 hA2 hB2]
    dsimp [alphaA2, alphaB2]
    have hCos2 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
    have hSin2 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have hCos4 : Real.cos (-(Real.pi / 4)) = Real.sqrt 2 / 2 := by rw [Real.cos_neg, Real.cos_pi_div_four]
    have hSin4 : Real.sin (-(Real.pi / 4)) = -(Real.sqrt 2 / 2) := by rw [Real.sin_neg, Real.sin_pi_div_four]
    rw [hCos2, hSin2, hCos4, hSin4]
    ring

  have hChshRe : chsh.re = 2 * Real.sqrt 2 := by
    dsimp [chsh]
    rw [hc1, hc2, hc3, hc4]
    ring

  rw [hChshRe]
  calc (2 * Real.sqrt 2) ^ 2
    = 4 * (Real.sqrt 2) ^ 2 := by ring
    _ = 4 * 2 := by rw [Real.sq_sqrt (by positivity)]
    _ = 8 := by norm_num

@[litlib_track "Static Flux Tube Maximal CHSH Violation - Inequality"]
theorem staticFluxTubeMaximalViolationInequality : (8 : ℝ) > 4 := by norm_num

@[litlib_track "Static Flux Tube Tsirelson Bound (CHSH) - Real"]
theorem staticFluxTubeTsirelsonBoundReal
  (L : ℝ)
  (alphaA1 alphaA2 alphaB1 alphaB2 : ℝ)
  (hField : ∀ t, pu.toUniverse.sd_sector 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t)) :
  let A1 : SU2Group := ⟨macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaA1 mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alphaA1 L hField]; exact obsHolonomyIsSu2 alphaA1 L⟩;
  let A2 : SU2Group := ⟨macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaA2 mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alphaA2 L hField]; exact obsHolonomyIsSu2 alphaA2 L⟩;
  let B1 : SU2Group := ⟨macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaB1 mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alphaB1 L hField]; exact obsHolonomyIsSu2 alphaB1 L⟩;
  let B2 : SU2Group := ⟨macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaB2 mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alphaB2 L hField]; exact obsHolonomyIsSu2 alphaB2 L⟩;
  let chsh := geometricBellCorrelation A1 B1 + geometricBellCorrelation A1 B2 +
              geometricBellCorrelation A2 B1 - geometricBellCorrelation A2 B2;
  (chsh.re)^2 ≤ 8 := by
  intro A1 A2 B1 B2 chsh
  exact universalHolonomyTsirelsonBoundReal A1 A2 B1 B2

@[litlib_track "Static Flux Tube Tsirelson Bound (CHSH) - Imaginary"]
theorem staticFluxTubeTsirelsonBoundImag
  (L : ℝ)
  (alphaA1 alphaA2 alphaB1 alphaB2 : ℝ)
  (hField : ∀ t, pu.toUniverse.sd_sector 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t)) :
  let A1 : SU2Group := ⟨macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaA1 mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alphaA1 L hField]; exact obsHolonomyIsSu2 alphaA1 L⟩;
  let A2 : SU2Group := ⟨macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaA2 mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alphaA2 L hField]; exact obsHolonomyIsSu2 alphaA2 L⟩;
  let B1 : SU2Group := ⟨macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaB1 mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alphaB1 L hField]; exact obsHolonomyIsSu2 alphaB1 L⟩;
  let B2 : SU2Group := ⟨macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alphaB2 mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alphaB2 L hField]; exact obsHolonomyIsSu2 alphaB2 L⟩;
  let chsh := geometricBellCorrelation A1 B1 + geometricBellCorrelation A1 B2 +
              geometricBellCorrelation A2 B1 - geometricBellCorrelation A2 B2;
  chsh.im = 0 := by
  intro A1 A2 B1 B2 chsh
  exact universalHolonomyTsirelsonBoundImag A1 A2 B1 B2

end HolonomyEvaluation

end CGD.Quantum

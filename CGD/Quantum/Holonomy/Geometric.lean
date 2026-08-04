-- FILENAME: CGD/Quantum/Holonomy/Geometric.lean

import Litlib.Core
import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace CGD.Quantum

open CGD.Axioms CGD.Foundations CGD.Math Complex Matrix

lemma embedMulEqZero (L R : SL2C) : embedSelfDual L * embedAntiSelfDual R = 0 := by
  ext i j
  simp only [embedSelfDual, embedAntiSelfDual, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  cases chiralIso.symm i <;> cases chiralIso.symm j <;> cases chiralIso.symm k <;> simp

/--
Demonstrates that the self-dual and anti-self-dual spin connection components
natively mathematically decouple under the geometric trace metric because their
underlying 4x4 matrix embeddings occupy perfectly disjoint sub-blocks.
The geometry requires no artificial truncation to separate chiral sectors.
-/
@[litlib_track "Algebraic Chiral Orthogonalization"]
theorem algebraicChiralOrthogonalization (pu : PhysicalUniverse) (x : SpacetimePoint) (μ ν ρ σ : Fin 4) :
  Matrix.trace (embedSelfDual (CGD.Foundations.curvatureSl2c pu.toUniverse.sd_sector μ ν x) *
                embedAntiSelfDual (CGD.Foundations.curvatureSl2c pu.toUniverse.asd_sector ρ σ x)) = 0 := by
  have hMul := embedMulEqZero (CGD.Foundations.curvatureSl2c pu.toUniverse.sd_sector μ ν x) (CGD.Foundations.curvatureSl2c pu.toUniverse.asd_sector ρ σ x)
  rw [hMul]
  simp [Matrix.trace]

lemma starCosReal (x : ℝ) : star (Complex.cos (x:ℂ)) = Complex.cos (x:ℂ) := by
  rw [← Complex.ofReal_cos]
  apply Complex.ext
  · rfl
  · exact neg_zero

lemma starSinReal (x : ℝ) : star (Complex.sin (x:ℂ)) = Complex.sin (x:ℂ) := by
  rw [← Complex.ofReal_sin]
  apply Complex.ext
  · rfl
  · exact neg_zero

section GeometricHolonomyIntegration

variable (θ : ℝ)

@[litlib_track "Geometric Holonomy Integration - Unitary"]
theorem geometricHolonomyIntegrationUnitary :
  let U := Matrix.of ![![Complex.cos (θ/2), -Complex.sin (θ/2)], ![Complex.sin (θ/2), Complex.cos (θ/2)]];
  U * U.conjTranspose = 1 := by
  intro U
  have hz : (θ / 2 : ℂ) = ↑(θ / 2 : ℝ) := by push_cast; ring
  have hStarCos : star (Complex.cos (θ / 2 : ℂ)) = Complex.cos (θ / 2 : ℂ) := by
    rw [hz, starCosReal]
  have hStarSin : star (Complex.sin (θ / 2 : ℂ)) = Complex.sin (θ / 2 : ℂ) := by
    rw [hz, starSinReal]
  have hTrig : Complex.sin (θ / 2 : ℂ) ^ 2 + Complex.cos (θ / 2 : ℂ) ^ 2 = 1 :=
    Complex.sin_sq_add_cos_sq (θ / 2 : ℂ)
  dsimp [U]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.one_apply]
    change Complex.cos (θ / 2 : ℂ) * star (Complex.cos (θ / 2 : ℂ)) + (-Complex.sin (θ / 2 : ℂ)) * star (-Complex.sin (θ / 2 : ℂ)) = 1
    rw [star_neg, hStarCos, hStarSin]
    calc
      Complex.cos (θ / 2 : ℂ) * Complex.cos (θ / 2 : ℂ) + -Complex.sin (θ / 2 : ℂ) * -Complex.sin (θ / 2 : ℂ)
        = Complex.sin (θ / 2 : ℂ) ^ 2 + Complex.cos (θ / 2 : ℂ) ^ 2 := by ring
      _ = 1 := hTrig
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.zero_apply]
    change Complex.cos (θ / 2 : ℂ) * star (Complex.sin (θ / 2 : ℂ)) + (-Complex.sin (θ / 2 : ℂ)) * star (Complex.cos (θ / 2 : ℂ)) = 0
    rw [hStarCos, hStarSin]
    ring
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.zero_apply]
    change Complex.sin (θ / 2 : ℂ) * star (Complex.cos (θ / 2 : ℂ)) + Complex.cos (θ / 2 : ℂ) * star (-Complex.sin (θ / 2 : ℂ)) = 0
    rw [star_neg, hStarCos, hStarSin]
    ring
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.one_apply]
    change Complex.sin (θ / 2 : ℂ) * star (Complex.sin (θ / 2 : ℂ)) + Complex.cos (θ / 2 : ℂ) * star (Complex.cos (θ / 2 : ℂ)) = 1
    rw [hStarCos, hStarSin]
    calc
      Complex.sin (θ / 2 : ℂ) * Complex.sin (θ / 2 : ℂ) + Complex.cos (θ / 2 : ℂ) * Complex.cos (θ / 2 : ℂ)
        = Complex.sin (θ / 2 : ℂ) ^ 2 + Complex.cos (θ / 2 : ℂ) ^ 2 := by ring
      _ = 1 := hTrig

@[litlib_track "Geometric Holonomy Integration - Determinant"]
theorem geometricHolonomyIntegrationDet :
  let U := Matrix.of ![![Complex.cos (θ/2), -Complex.sin (θ/2)], ![Complex.sin (θ/2), Complex.cos (θ/2)]];
  Matrix.det U = 1 := by
  intro U
  have hTrig : Complex.sin (θ / 2 : ℂ) ^ 2 + Complex.cos (θ / 2 : ℂ) ^ 2 = 1 :=
    Complex.sin_sq_add_cos_sq (θ / 2 : ℂ)
  dsimp [U]
  rw [Matrix.det_fin_two]
  change Complex.cos (θ / 2 : ℂ) * Complex.cos (θ / 2 : ℂ) - (-Complex.sin (θ / 2 : ℂ)) * Complex.sin (θ / 2 : ℂ) = 1
  calc
    Complex.cos (θ / 2 : ℂ) * Complex.cos (θ / 2 : ℂ) - (-Complex.sin (θ / 2 : ℂ)) * Complex.sin (θ / 2 : ℂ)
      = Complex.sin (θ / 2 : ℂ) ^ 2 + Complex.cos (θ / 2 : ℂ) ^ 2 := by ring
    _ = 1 := hTrig

end GeometricHolonomyIntegration

/--
The exact quantum correlation natively emerges from the Cartan-Killing metric
of the SU(2) group. For unitary SU(2) elements, 1/2 Tr(A B†) perfectly recovers
the cosine of the angle between them.
-/
@[litlib_track "Geometric Bell Correlation"]
noncomputable def geometricBellCorrelation (A B : SU2Group) : ℂ :=
  (1 / 2 : ℂ) * Matrix.trace (A.val * B.val.conjTranspose)

lemma su2Components (A : Matrix (Fin 2) (Fin 2) ℂ)
  (hUnit : A * A.conjTranspose = 1) (hDet : Matrix.det A = 1) :
  A 1 1 = star (A 0 0) ∧ A 0 1 = - star (A 1 0) := by
  have h00 : (A * A.conjTranspose) 0 0 = 1 := by rw [hUnit]; rfl
  have h10 : (A * A.conjTranspose) 1 0 = 0 := by rw [hUnit]; rfl
  have hEq00 : A 0 0 * star (A 0 0) + A 0 1 * star (A 0 1) = 1 := by
    calc A 0 0 * star (A 0 0) + A 0 1 * star (A 0 1) = (A * A.conjTranspose) 0 0 := by simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    _ = 1 := h00
  have hEq10 : A 1 0 * star (A 0 0) + A 1 1 * star (A 0 1) = 0 := by
    calc A 1 0 * star (A 0 0) + A 1 1 * star (A 0 1) = (A * A.conjTranspose) 1 0 := by simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    _ = 0 := h10
  have hDetExp : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    calc A 0 0 * A 1 1 - A 0 1 * A 1 0 = Matrix.det A := by simp [Matrix.det_fin_two]
    _ = 1 := hDet
  have hA11 : A 1 1 = star (A 0 0) := by
    calc A 1 1 = 1 * A 1 1 := by ring
      _ = (A 0 0 * star (A 0 0) + A 0 1 * star (A 0 1)) * A 1 1 := by rw [hEq00]
      _ = star (A 0 0) * (A 0 0 * A 1 1) + A 0 1 * (A 1 1 * star (A 0 1)) := by ring
      _ = star (A 0 0) * (1 + A 0 1 * A 1 0) + A 0 1 * (A 1 1 * star (A 0 1)) := by
        have hSub : A 0 0 * A 1 1 = 1 + A 0 1 * A 1 0 := by
          calc A 0 0 * A 1 1 = (A 0 0 * A 1 1 - A 0 1 * A 1 0) + A 0 1 * A 1 0 := by ring
            _ = 1 + A 0 1 * A 1 0 := by rw [hDetExp]
        rw [hSub]
      _ = star (A 0 0) + A 0 1 * (A 1 0 * star (A 0 0) + A 1 1 * star (A 0 1)) := by ring
      _ = star (A 0 0) + A 0 1 * 0 := by rw [hEq10]
      _ = star (A 0 0) := by ring
  have hStep1 : A 0 0 * star (A 0 0) - A 0 1 * A 1 0 = 1 := by
    calc A 0 0 * star (A 0 0) - A 0 1 * A 1 0 = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by rw [hA11]
    _ = 1 := hDetExp
  have hStep2 : - A 0 1 * A 1 0 = A 0 1 * star (A 0 1) := by
    calc - A 0 1 * A 1 0 = (A 0 0 * star (A 0 0) - A 0 1 * A 1 0) - A 0 0 * star (A 0 0) := by ring
      _ = 1 - A 0 0 * star (A 0 0) := by rw [hStep1]
      _ = (A 0 0 * star (A 0 0) + A 0 1 * star (A 0 1)) - A 0 0 * star (A 0 0) := by rw [← hEq00]
      _ = A 0 1 * star (A 0 1) := by ring
  have hStep3 : star (A 0 0) * (A 1 0 + star (A 0 1)) = 0 := by
    calc star (A 0 0) * (A 1 0 + star (A 0 1)) = A 1 0 * star (A 0 0) + star (A 0 0) * star (A 0 1) := by ring
    _ = A 1 0 * star (A 0 0) + A 1 1 * star (A 0 1) := by rw [hA11]
    _ = 0 := hEq10
  have hStep4 : A 0 0 * star (A 0 0) * (A 1 0 + star (A 0 1)) = 0 := by
    calc A 0 0 * star (A 0 0) * (A 1 0 + star (A 0 1)) = A 0 0 * (star (A 0 0) * (A 1 0 + star (A 0 1))) := by ring
    _ = A 0 0 * 0 := by rw [hStep3]
    _ = 0 := mul_zero _
  have hA01Final : A 1 0 + star (A 0 1) = 0 := by
    calc A 1 0 + star (A 0 1) = 1 * (A 1 0 + star (A 0 1)) := by ring
    _ = (A 0 0 * star (A 0 0) + A 0 1 * star (A 0 1)) * (A 1 0 + star (A 0 1)) := by rw [hEq00]
    _ = A 0 0 * star (A 0 0) * (A 1 0 + star (A 0 1)) + A 0 1 * star (A 0 1) * A 1 0 + A 0 1 * star (A 0 1) * star (A 0 1) := by ring
    _ = 0 + A 0 1 * star (A 0 1) * A 1 0 + A 0 1 * star (A 0 1) * star (A 0 1) := by rw [hStep4]
    _ = star (A 0 1) * (A 0 1 * A 1 0) + A 0 1 * star (A 0 1) * star (A 0 1) := by ring
    _ = star (A 0 1) * (- (A 0 1 * star (A 0 1))) + A 0 1 * star (A 0 1) * star (A 0 1) := by
      have hs : A 0 1 * A 1 0 = - (A 0 1 * star (A 0 1)) := by
        calc A 0 1 * A 1 0 = - (- A 0 1 * A 1 0) := by ring
          _ = - (A 0 1 * star (A 0 1)) := by rw [hStep2]
      rw [hs]
    _ = 0 := by ring
  have hLast : A 0 1 = - star (A 1 0) := by
    have hStar : star (A 1 0 + star (A 0 1)) = star 0 := by rw [hA01Final]
    simp only [star_add, star_star, star_zero] at hStar
    calc A 0 1 = (star (A 1 0) + A 0 1) - star (A 1 0) := by ring
      _ = 0 - star (A 1 0) := by rw [hStar]
      _ = - star (A 1 0) := by ring
  exact ⟨hA11, hLast⟩

lemma complexMulStarAddStarMul (z w : ℂ) : z * star w + star z * w = (2:ℂ) * (z.re * w.re + z.im * w.im) := by
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
    ring
  · simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
    ring

lemma complexNormSqEq (z : ℂ) : z * star z = (z.re^2 + z.im^2 : ℂ) := by
  have rhsEq : (z.re^2 + z.im^2 : ℂ) = ↑(z.re^2 + z.im^2 : ℝ) := by push_cast; ring
  rw [rhsEq]
  apply Complex.ext
  · change z.re * z.re - z.im * (-z.im) = z.re^2 + z.im^2
    ring
  · change z.re * (-z.im) + z.im * z.re = 0
    ring

lemma su2TraceReduction (A B : Matrix (Fin 2) (Fin 2) ℂ)
  (hAUnit : A * A.conjTranspose = 1) (hADet : Matrix.det A = 1)
  (hBUnit : B * B.conjTranspose = 1) (hBDet : Matrix.det B = 1) :
  Matrix.trace (A * B.conjTranspose) = (2:ℂ) * ((A 0 0).re * (B 0 0).re + (A 0 0).im * (B 0 0).im + (A 1 0).re * (B 1 0).re + (A 1 0).im * (B 1 0).im) := by
  have hA := su2Components A hAUnit hADet
  have hB := su2Components B hBUnit hBDet
  have hTr : Matrix.trace (A * B.conjTranspose) =
    A 0 0 * star (B 0 0) + A 0 1 * star (B 0 1) + A 1 0 * star (B 1 0) + A 1 1 * star (B 1 1) := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply]
    ring
  rw [hTr, hA.1, hA.2, hB.1, hB.2]
  have hStarNeg : (- star (A 1 0)) * star (- star (B 1 0)) = star (A 1 0) * B 1 0 := by
    rw [star_neg, star_star]
    ring
  rw [hStarNeg]
  have hStarStar : star (A 0 0) * star (star (B 0 0)) = star (A 0 0) * B 0 0 := by
    rw [star_star]
  rw [hStarStar]
  have hRearrange : A 0 0 * star (B 0 0) + star (A 1 0) * B 1 0 + A 1 0 * star (B 1 0) + star (A 0 0) * B 0 0 =
    (A 0 0 * star (B 0 0) + star (A 0 0) * B 0 0) + (A 1 0 * star (B 1 0) + star (A 1 0) * B 1 0) := by ring
  rw [hRearrange]
  rw [complexMulStarAddStarMul, complexMulStarAddStarMul]
  ring

lemma su2NormEqOne (A : Matrix (Fin 2) (Fin 2) ℂ)
  (hAUnit : A * A.conjTranspose = 1) (hADet : Matrix.det A = 1) :
  (A 0 0).re^2 + (A 0 0).im^2 + (A 1 0).re^2 + (A 1 0).im^2 = 1 := by
  have hA := su2Components A hAUnit hADet
  have h00 : (A * A.conjTranspose) 0 0 = 1 := by rw [hAUnit]; rfl
  have hEq : A 0 0 * star (A 0 0) + A 0 1 * star (A 0 1) = 1 := by
    have hMul : (A * A.conjTranspose) 0 0 = A 0 0 * star (A 0 0) + A 0 1 * star (A 0 1) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    rw [← hMul, h00]
  rw [hA.2] at hEq
  have hNegStar : (- star (A 1 0)) * star (- star (A 1 0)) = A 1 0 * star (A 1 0) := by
    rw [star_neg, star_star]
    ring
  rw [hNegStar] at hEq
  rw [complexNormSqEq, complexNormSqEq] at hEq
  have hReassoc : ((A 0 0).re^2 + (A 0 0).im^2 + (A 1 0).re^2 + (A 1 0).im^2 : ℂ) = 1 := by
    calc ((A 0 0).re^2 + (A 0 0).im^2 + (A 1 0).re^2 + (A 1 0).im^2 : ℂ)
      = ((A 0 0).re^2 + (A 0 0).im^2 : ℂ) + ((A 1 0).re^2 + (A 1 0).im^2 : ℂ) := by ring
    _ = 1 := hEq
  exact_mod_cast hReassoc

lemma sqAddSqIneq (A B : ℝ) : (A + B)^2 ≤ 2*A^2 + 2*B^2 := by
  have h : 2*A^2 + 2*B^2 - (A + B)^2 = (A - B)^2 := by ring
  linarith [sq_nonneg (A - B)]

lemma r4CauchySchwarz (x1 x2 x3 x4 u1 u2 u3 u4 : ℝ) :
  (x1*u1 + x2*u2 + x3*u3 + x4*u4)^2 ≤ (x1^2 + x2^2 + x3^2 + x4^2) * (u1^2 + u2^2 + u3^2 + u4^2) := by
  have h : (x1^2 + x2^2 + x3^2 + x4^2) * (u1^2 + u2^2 + u3^2 + u4^2) - (x1*u1 + x2*u2 + x3*u3 + x4*u4)^2 =
    (x1*u2 - x2*u1)^2 + (x1*u3 - x3*u1)^2 + (x1*u4 - x4*u1)^2 +
    (x2*u3 - x3*u2)^2 + (x2*u4 - x4*u2)^2 + (x3*u4 - x4*u3)^2 := by ring
  linarith [sq_nonneg (x1*u2 - x2*u1), sq_nonneg (x1*u3 - x3*u1), sq_nonneg (x1*u4 - x4*u1),
            sq_nonneg (x2*u3 - x3*u2), sq_nonneg (x2*u4 - x4*u2), sq_nonneg (x3*u4 - x4*u3)]

lemma r4CauchySchwarzUnit (x1 x2 x3 x4 u1 u2 u3 u4 : ℝ) (hx : x1^2 + x2^2 + x3^2 + x4^2 = 1) :
  (x1*u1 + x2*u2 + x3*u3 + x4*u4)^2 ≤ u1^2 + u2^2 + u3^2 + u4^2 := by
  have h := r4CauchySchwarz x1 x2 x3 x4 u1 u2 u3 u4
  rw [hx, one_mul] at h
  exact h

lemma chshRealBound (x1 x2 x3 x4 z1 z2 z3 z4 y11 y12 y13 y14 y21 y22 y23 y24 : ℝ)
  (hx : x1^2 + x2^2 + x3^2 + x4^2 = 1)
  (hz : z1^2 + z2^2 + z3^2 + z4^2 = 1)
  (hy1 : y11^2 + y12^2 + y13^2 + y14^2 = 1)
  (hy2 : y21^2 + y22^2 + y23^2 + y24^2 = 1) :
  ( (x1*y11 + x2*y12 + x3*y13 + x4*y14) +
    (x1*y21 + x2*y22 + x3*y23 + x4*y24) +
    (z1*y11 + z2*y12 + z3*y13 + z4*y14) -
    (z1*y21 + z2*y22 + z3*y23 + z4*y24) )^2 ≤ 8 := by
  let U1 := y11 + y21; let U2 := y12 + y22; let U3 := y13 + y23; let U4 := y14 + y24
  let V1 := y11 - y21; let V2 := y12 - y22; let V3 := y13 - y23; let V4 := y14 - y24

  have hSum : (x1*y11 + x2*y12 + x3*y13 + x4*y14) + (x1*y21 + x2*y22 + x3*y23 + x4*y24) +
               (z1*y11 + z2*y12 + z3*y13 + z4*y14) - (z1*y21 + z2*y22 + z3*y23 + z4*y24) =
               (x1*U1 + x2*U2 + x3*U3 + x4*U4) + (z1*V1 + z2*V2 + z3*V3 + z4*V4) := by
    dsimp [U1, U2, U3, U4, V1, V2, V3, V4]
    ring

  rw [hSum]

  have hSq := sqAddSqIneq (x1*U1 + x2*U2 + x3*U3 + x4*U4) (z1*V1 + z2*V2 + z3*V3 + z4*V4)

  have hX := r4CauchySchwarzUnit x1 x2 x3 x4 U1 U2 U3 U4 hx
  have hZ := r4CauchySchwarzUnit z1 z2 z3 z4 V1 V2 V3 V4 hz

  have hBound : 2 * (x1*U1 + x2*U2 + x3*U3 + x4*U4)^2 + 2 * (z1*V1 + z2*V2 + z3*V3 + z4*V4)^2 ≤
                 2 * (U1^2 + U2^2 + U3^2 + U4^2) + 2 * (V1^2 + V2^2 + V3^2 + V4^2) := by
    linarith

  have hUV : 2 * (U1^2 + U2^2 + U3^2 + U4^2) + 2 * (V1^2 + V2^2 + V3^2 + V4^2) =
              4 * (y11^2 + y12^2 + y13^2 + y14^2) + 4 * (y21^2 + y22^2 + y23^2 + y24^2) := by
    dsimp [U1, U2, U3, U4, V1, V2, V3, V4]
    ring

  rw [hUV, hy1, hy2] at hBound
  linarith

section UniversalHolonomyTsirelsonBound

variable (A1 A2 B1 B2 : SU2Group)

@[litlib_track "Universal Geometric Tsirelson Bound - Real Bound"]
theorem universalHolonomyTsirelsonBoundReal :
  let chsh := geometricBellCorrelation A1 B1 + geometricBellCorrelation A1 B2 +
              geometricBellCorrelation A2 B1 - geometricBellCorrelation A2 B2;
  (chsh.re)^2 ≤ 8 := by
  intro chsh
  have hA1Unit : A1.val * A1.val.conjTranspose = 1 := A1.property.1
  have hA1Det : Matrix.det A1.val = 1 := A1.property.2
  have hA2Unit : A2.val * A2.val.conjTranspose = 1 := A2.property.1
  have hA2Det : Matrix.det A2.val = 1 := A2.property.2
  have hB1Unit : B1.val * B1.val.conjTranspose = 1 := B1.property.1
  have hB1Det : Matrix.det B1.val = 1 := B1.property.2
  have hB2Unit : B2.val * B2.val.conjTranspose = 1 := B2.property.1
  have hB2Det : Matrix.det B2.val = 1 := B2.property.2
  have hA1B1 := su2TraceReduction A1.val B1.val hA1Unit hA1Det hB1Unit hB1Det
  have hA1B2 := su2TraceReduction A1.val B2.val hA1Unit hA1Det hB2Unit hB2Det
  have hA2B1 := su2TraceReduction A2.val B1.val hA2Unit hA2Det hB1Unit hB1Det
  have hA2B2 := su2TraceReduction A2.val B2.val hA2Unit hA2Det hB2Unit hB2Det
  have hChshReVal : chsh.re =
    ((A1.val 0 0).re * (B1.val 0 0).re + (A1.val 0 0).im * (B1.val 0 0).im + (A1.val 1 0).re * (B1.val 1 0).re + (A1.val 1 0).im * (B1.val 1 0).im) +
    ((A1.val 0 0).re * (B2.val 0 0).re + (A1.val 0 0).im * (B2.val 0 0).im + (A1.val 1 0).re * (B2.val 1 0).re + (A1.val 1 0).im * (B2.val 1 0).im) +
    ((A2.val 0 0).re * (B1.val 0 0).re + (A2.val 0 0).im * (B1.val 0 0).im + (A2.val 1 0).re * (B1.val 1 0).re + (A2.val 1 0).im * (B1.val 1 0).im) -
    ((A2.val 0 0).re * (B2.val 0 0).re + (A2.val 0 0).im * (B2.val 0 0).im + (A2.val 1 0).re * (B2.val 1 0).re + (A2.val 1 0).im * (B2.val 1 0).im) := by
    dsimp [chsh, geometricBellCorrelation]
    rw [hA1B1, hA1B2, hA2B1, hA2B2]
    simp
  have hA1Norm := su2NormEqOne A1.val hA1Unit hA1Det
  have hA2Norm := su2NormEqOne A2.val hA2Unit hA2Det
  have hB1Norm := su2NormEqOne B1.val hB1Unit hB1Det
  have hB2Norm := su2NormEqOne B2.val hB2Unit hB2Det
  have hBound := chshRealBound
    (A1.val 0 0).re (A1.val 0 0).im (A1.val 1 0).re (A1.val 1 0).im
    (A2.val 0 0).re (A2.val 0 0).im (A2.val 1 0).re (A2.val 1 0).im
    (B1.val 0 0).re (B1.val 0 0).im (B1.val 1 0).re (B1.val 1 0).im
    (B2.val 0 0).re (B2.val 0 0).im (B2.val 1 0).re (B2.val 1 0).im
    hA1Norm hA2Norm hB1Norm hB2Norm
  rw [hChshReVal]
  exact hBound

@[litlib_track "Universal Geometric Tsirelson Bound - Imaginary Zero"]
theorem universalHolonomyTsirelsonBoundImag :
  let chsh := geometricBellCorrelation A1 B1 + geometricBellCorrelation A1 B2 +
              geometricBellCorrelation A2 B1 - geometricBellCorrelation A2 B2;
  chsh.im = 0 := by
  intro chsh
  have hA1Unit : A1.val * A1.val.conjTranspose = 1 := A1.property.1
  have hA1Det : Matrix.det A1.val = 1 := A1.property.2
  have hA2Unit : A2.val * A2.val.conjTranspose = 1 := A2.property.1
  have hA2Det : Matrix.det A2.val = 1 := A2.property.2
  have hB1Unit : B1.val * B1.val.conjTranspose = 1 := B1.property.1
  have hB1Det : Matrix.det B1.val = 1 := B1.property.2
  have hB2Unit : B2.val * B2.val.conjTranspose = 1 := B2.property.1
  have hB2Det : Matrix.det B2.val = 1 := B2.property.2
  have hA1B1 := su2TraceReduction A1.val B1.val hA1Unit hA1Det hB1Unit hB1Det
  have hA1B2 := su2TraceReduction A1.val B2.val hA1Unit hA1Det hB2Unit hB2Det
  have hA2B1 := su2TraceReduction A2.val B1.val hA2Unit hA2Det hB1Unit hB1Det
  have hA2B2 := su2TraceReduction A2.val B2.val hA2Unit hA2Det hB2Unit hB2Det
  dsimp [chsh, geometricBellCorrelation]
  rw [hA1B1, hA1B2, hA2B1, hA2B2]
  simp

end UniversalHolonomyTsirelsonBound

end CGD.Quantum

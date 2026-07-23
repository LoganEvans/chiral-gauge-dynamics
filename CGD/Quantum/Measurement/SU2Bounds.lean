-- FILENAME: CGD/Quantum/Measurement/SU2Bounds.lean

import CGD.Foundations.GaugeGroup
import CGD.Quantum.Holonomy.Geometric
import Litlib.Core
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Field.Basic

open CGD.Foundations CGD.Quantum

/-- Scalar Helper: Upper Bound via completing the square -/
lemma complex_upper_bound (z w : ℂ) : 2 * (z * star w).re ≤ Complex.normSq z + Complex.normSq w := by
  have h1 : 0 ≤ (z.re - w.re)^2 := sq_nonneg (z.re - w.re)
  have h2 : 0 ≤ (z.im - w.im)^2 := sq_nonneg (z.im - w.im)
  have h_re : (z * star w).re = z.re * w.re + z.im * w.im := by simp [Complex.mul_re, star]
  have h_nz : (Complex.normSq z : ℝ) = z.re^2 + z.im^2 := by
    simp [Complex.normSq]
    ring
  have h_nw : (Complex.normSq w : ℝ) = w.re^2 + w.im^2 := by
    simp [Complex.normSq]
    ring
  linarith

/-- Scalar Helper: Lower Bound via completing the square -/
lemma complex_lower_bound (z w : ℂ) : -(Complex.normSq z + Complex.normSq w) ≤ 2 * (z * star w).re := by
  have h1 : 0 ≤ (z.re + w.re)^2 := sq_nonneg (z.re + w.re)
  have h2 : 0 ≤ (z.im + w.im)^2 := sq_nonneg (z.im + w.im)
  have h_re : (z * star w).re = z.re * w.re + z.im * w.im := by simp [Complex.mul_re, star]
  have h_nz : (Complex.normSq z : ℝ) = z.re^2 + z.im^2 := by
    simp [Complex.normSq]
    ring
  have h_nw : (Complex.normSq w : ℝ) = w.re^2 + w.im^2 := by
    simp [Complex.normSq]
    ring
  linarith

/-- Trace Expansion: Explicit unrolling of the 2x2 matrix inner product -/
lemma trace_expansion (M N : Matrix (Fin 2) (Fin 2) ℂ) :
  (Matrix.trace (M * N.conjTranspose)).re =
  (M 0 0 * star (N 0 0)).re + (M 0 1 * star (N 0 1)).re +
  (M 1 0 * star (N 1 0)).re + (M 1 1 * star (N 1 1)).re := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose, Fin.sum_univ_two, Complex.add_re]
  ring_nf

/-- Self-Trace Identity: For an SU(2) matrix A, Tr(A * A^H) = 2 -/
lemma su2_norm_sq_sum (A : SU2Group) :
  (Complex.normSq (A.val 0 0) : ℝ) + Complex.normSq (A.val 0 1) +
  Complex.normSq (A.val 1 0) + Complex.normSq (A.val 1 1) = 2 := by
  have h1 : A.val * A.val.conjTranspose = 1 := A.property.1
  have h2 : (Matrix.trace (A.val * A.val.conjTranspose)).re = (Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ)).re := by rw [h1]
  
  have h3 : (Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ)).re = 2 := by
    simp [Matrix.trace]
    
  have h4 : (Matrix.trace (A.val * A.val.conjTranspose)).re =
    (Complex.normSq (A.val 0 0) : ℝ) + Complex.normSq (A.val 0 1) +
    Complex.normSq (A.val 1 0) + Complex.normSq (A.val 1 1) := by
    rw [trace_expansion A.val A.val]
    have hz (z : ℂ) : (z * star z).re = Complex.normSq z := by
      simp [Complex.mul_re, star, Complex.normSq]
    rw [hz, hz, hz, hz]
    
  rw [h4, h3] at h2
  exact h2

/--
Pure Math Lemma: The trace of the product of two SU(2) matrices is strictly 
bounded by [-1, 1]. This is a standard geometric property of the SU(2) Killing form.
-/
@[litlib_track "SU(2) Geometric Correlation Bound"]
lemma su2_correlation_bounds (A B : SU2Group) :
  -1 ≤ (geometricBellCorrelation A B).re ∧ (geometricBellCorrelation A B).re ≤ 1 := by
  -- 1. Unfold the geometric correlation definition
  have h_def : (geometricBellCorrelation A B).re = (1 / 2 : ℝ) * (Matrix.trace (A.val * B.val.conjTranspose)).re := by
    unfold geometricBellCorrelation
    simp [Complex.mul_re]

  -- 2. Expand the trace algebraically
  have h_trace : (Matrix.trace (A.val * B.val.conjTranspose)).re =
    (A.val 0 0 * star (B.val 0 0)).re + (A.val 0 1 * star (B.val 0 1)).re +
    (A.val 1 0 * star (B.val 1 0)).re + (A.val 1 1 * star (B.val 1 1)).re := trace_expansion A.val B.val

  -- 3. Apply the scalar upper and lower bounds to each element
  have hu1 := complex_upper_bound (A.val 0 0) (B.val 0 0)
  have hu2 := complex_upper_bound (A.val 0 1) (B.val 0 1)
  have hu3 := complex_upper_bound (A.val 1 0) (B.val 1 0)
  have hu4 := complex_upper_bound (A.val 1 1) (B.val 1 1)

  have hl1 := complex_lower_bound (A.val 0 0) (B.val 0 0)
  have hl2 := complex_lower_bound (A.val 0 1) (B.val 0 1)
  have hl3 := complex_lower_bound (A.val 1 0) (B.val 1 0)
  have hl4 := complex_lower_bound (A.val 1 1) (B.val 1 1)

  -- 4. Bring in the SU(2) unity constraints
  have hA := su2_norm_sq_sum A
  have hB := su2_norm_sq_sum B

  -- 5. Linarith destroys the algebra
  constructor
  · linarith
  · linarith

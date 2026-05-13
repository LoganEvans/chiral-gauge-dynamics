-- FILENAME: CGD/Quantum/Holonomy/Basic.lean

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Matrix.Normed
import CGD.Foundations.Spacetime
import CGD.Foundations.Math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations Matrix Complex BigOperators

namespace CGD.Quantum

def straightLinePath (t : ℝ) : SpacetimePoint := fun i => if i = 1 then t else 0

lemma straightLinePath_prop (t : ℝ) : straightLinePath t 1 = t ∧ straightLinePath t 0 = 0 ∧ straightLinePath t 2 = 0 ∧ straightLinePath t 3 = 0 := by
  unfold straightLinePath
  have h0 : (0 : Fin 4) ≠ 1 := by decide
  have h1 : (1 : Fin 4) = 1 := rfl
  have h2 : (2 : Fin 4) ≠ 1 := by decide
  have h3 : (3 : Fin 4) ≠ 1 := by decide
  simp [h0, h1, h2, h3]

lemma complex_double_angle_cos (θ : ℝ) : Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) = Complex.cos ↑θ := by
  have h_add : Real.cos (θ / 2 + θ / 2) = Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2) := Real.cos_add (θ / 2) (θ / 2)
  have hz : θ / 2 + θ / 2 = θ := by ring
  have h_subst : Real.cos (θ / 2 + θ / 2) = Real.cos θ := congr_arg Real.cos hz
  have h_real : Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2) = Real.cos θ := Eq.trans (Eq.symm h_add) h_subst
  
  have c1 : (↑(Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) = 
            (↑(Real.cos (θ / 2) * Real.cos (θ / 2)) : ℂ) - (↑(Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) := Complex.ofReal_sub _ _
  have c2 : (↑(Real.cos (θ / 2) * Real.cos (θ / 2)) : ℂ) = (↑(Real.cos (θ / 2)) : ℂ) * (↑(Real.cos (θ / 2)) : ℂ) := Complex.ofReal_mul _ _
  have c3 : (↑(Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) = (↑(Real.sin (θ / 2)) : ℂ) * (↑(Real.sin (θ / 2)) : ℂ) := Complex.ofReal_mul _ _
  
  have c4 : (↑(Real.cos (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) := Complex.ofReal_cos _
  have c4_mul : (↑(Real.cos (θ / 2)) : ℂ) * (↑(Real.cos (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) := congr_arg₂ (· * ·) c4 c4
  have c5 : (↑(Real.sin (θ / 2)) : ℂ) = Complex.sin ↑(θ / 2) := Complex.ofReal_sin _
  have c5_mul : (↑(Real.sin (θ / 2)) : ℂ) * (↑(Real.sin (θ / 2)) : ℂ) = Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) := congr_arg₂ (· * ·) c5 c5
  
  have c6 : (↑(Real.cos (θ / 2) * Real.cos (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) := Eq.trans c2 c4_mul
  have c7 : (↑(Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) = Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) := Eq.trans c3 c5_mul
  
  have c8 : (↑(Real.cos (θ / 2) * Real.cos (θ / 2)) : ℂ) - (↑(Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) := congr_arg₂ (· - ·) c6 c7
  
  have c9 : (↑(Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) := Eq.trans c1 c8
  have c10 : (↑(Real.cos θ) : ℂ) = Complex.cos ↑θ := Complex.ofReal_cos _
  
  have h_complex : (↑(Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) = ↑(Real.cos θ) := congr_arg Complex.ofReal h_real
  have h_final1 : Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) = (↑(Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2)) : ℂ) := Eq.symm c9
  have h_final2 : Complex.cos ↑(θ / 2) * Complex.cos ↑(θ / 2) - Complex.sin ↑(θ / 2) * Complex.sin ↑(θ / 2) = ↑(Real.cos θ) := Eq.trans h_final1 h_complex
  exact Eq.trans h_final2 c10

lemma complex_double_angle_sin (θ : ℝ) : Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) = Complex.sin ↑θ := by
  have h_add : Real.sin (θ / 2 + θ / 2) = Real.sin (θ / 2) * Real.cos (θ / 2) + Real.cos (θ / 2) * Real.sin (θ / 2) := Real.sin_add (θ / 2) (θ / 2)
  have hz : θ / 2 + θ / 2 = θ := by ring
  have hc : Real.sin (θ / 2) * Real.cos (θ / 2) + Real.cos (θ / 2) * Real.sin (θ / 2) = Real.cos (θ / 2) * Real.sin (θ / 2) + Real.sin (θ / 2) * Real.cos (θ / 2) := by ring
  have h_subst : Real.sin (θ / 2 + θ / 2) = Real.sin θ := congr_arg Real.sin hz
  have h_real1 : Real.sin (θ / 2) * Real.cos (θ / 2) + Real.cos (θ / 2) * Real.sin (θ / 2) = Real.sin θ := Eq.trans (Eq.symm h_add) h_subst
  have h_real : Real.cos (θ / 2) * Real.sin (θ / 2) + Real.sin (θ / 2) * Real.cos (θ / 2) = Real.sin θ := Eq.trans (Eq.symm hc) h_real1
  
  have c1 : (↑(Real.cos (θ / 2) * Real.sin (θ / 2) + Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) = 
            (↑(Real.cos (θ / 2) * Real.sin (θ / 2)) : ℂ) + (↑(Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) := Complex.ofReal_add _ _
  have c2 : (↑(Real.cos (θ / 2) * Real.sin (θ / 2)) : ℂ) = (↑(Real.cos (θ / 2)) : ℂ) * (↑(Real.sin (θ / 2)) : ℂ) := Complex.ofReal_mul _ _
  have c3 : (↑(Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) = (↑(Real.sin (θ / 2)) : ℂ) * (↑(Real.cos (θ / 2)) : ℂ) := Complex.ofReal_mul _ _
  
  have c4 : (↑(Real.cos (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) := Complex.ofReal_cos _
  have c5 : (↑(Real.sin (θ / 2)) : ℂ) = Complex.sin ↑(θ / 2) := Complex.ofReal_sin _
  have c2_mul : (↑(Real.cos (θ / 2)) : ℂ) * (↑(Real.sin (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) := congr_arg₂ (· * ·) c4 c5
  have c3_mul : (↑(Real.sin (θ / 2)) : ℂ) * (↑(Real.cos (θ / 2)) : ℂ) = Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) := congr_arg₂ (· * ·) c5 c4
  
  have c6 : (↑(Real.cos (θ / 2) * Real.sin (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) := Eq.trans c2 c2_mul
  have c7 : (↑(Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) = Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) := Eq.trans c3 c3_mul
  
  have c8 : (↑(Real.cos (θ / 2) * Real.sin (θ / 2)) : ℂ) + (↑(Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) := congr_arg₂ (· + ·) c6 c7
  have c9 : (↑(Real.cos (θ / 2) * Real.sin (θ / 2) + Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) = Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) := Eq.trans c1 c8
  
  have c10 : (↑(Real.sin θ) : ℂ) = Complex.sin ↑θ := Complex.ofReal_sin _
  
  have h_complex : (↑(Real.cos (θ / 2) * Real.sin (θ / 2) + Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) = ↑(Real.sin θ) := congr_arg Complex.ofReal h_real
  have h_final1 : Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) = (↑(Real.cos (θ / 2) * Real.sin (θ / 2) + Real.sin (θ / 2) * Real.cos (θ / 2)) : ℂ) := Eq.symm c9
  have h_final2 : Complex.cos ↑(θ / 2) * Complex.sin ↑(θ / 2) + Complex.sin ↑(θ / 2) * Complex.cos ↑(θ / 2) = ↑(Real.sin θ) := Eq.trans h_final1 h_complex
  exact Eq.trans h_final2 c10

lemma hasDerivAt_ofReal (t : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
  have h1 := hasDerivAt_id t
  have h2 := HasDerivAt.smul_const h1 (1 : ℂ)
  have eq1 : (fun (y : ℝ) => id y • (1 : ℂ)) = fun (s : ℝ) => (s : ℂ) := by ext x; simp
  have eq2 : (1 : ℝ) • (1 : ℂ) = 1 := by simp
  rw [eq1, eq2] at h2
  exact h2

lemma scalar_integral_deriv (t0 t : ℝ) :
  HasDerivAt (fun s : ℝ => Complex.I * ((s:ℂ) - (t0:ℂ))) Complex.I t := by
  have hd1 : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 t := hasDerivAt_ofReal t
  have hd2 : HasDerivAt (fun s : ℝ => (s:ℂ) - (t0:ℂ)) 1 t := hd1.sub_const (t0:ℂ)
  have hd3 := HasDerivAt.const_mul Complex.I hd2
  have h_eq : Complex.I * 1 = Complex.I := mul_one _
  rw [h_eq] at hd3
  exact hd3

lemma integral_t_M (M : Matrix (Fin 2) (Fin 2) ℂ) (t0 t : ℝ) :
  HasDerivAt (fun s : ℝ => (Complex.I * ((s:ℂ) - (t0:ℂ))) • M)
             (Complex.I • M) t :=
  HasDerivAt.smul_const (scalar_integral_deriv t0 t) M

end CGD.Quantum

-- FILENAME: CGD/Foundations/GaugeGroup.lean

import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import CGD.Foundations.Math

open Complex Matrix

namespace CGD.Foundations

noncomputable abbrev sl2cAlgebra := LieAlgebra.SpecialLinear.sl (Fin 2) Complex
abbrev SL2C := ↥sl2cAlgebra
abbrev ChiralM := Matrix (Fin 4) (Fin 4) Complex

lemma mem_sl_iff (A : Matrix (Fin 2) (Fin 2) Complex) : A ∈ sl2cAlgebra ↔ Matrix.trace A = 0 := by rfl

noncomputable def toSl2c (M : Matrix (Fin 2) (Fin 2) Complex) : SL2C :=
  let tr := M.trace
  let M' := M - (tr / 2) • (1 : Matrix (Fin 2) (Fin 2) Complex)
  ⟨M', by rw[mem_sl_iff, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]; rw[Fintype.card_fin]; simp only[Nat.cast_ofNat]; rw[smul_eq_mul]; field_simp; ring⟩

def isSu2 (M : Matrix (Fin 2) (Fin 2) Complex) : Prop := 
  Matrix.trace M = 0 ∧ M.conjTranspose = -M

def SU2Group := { M : Matrix (Fin 2) (Fin 2) Complex // M * M.conjTranspose = 1 ∧ M.det = 1 }

instance : One SU2Group where
  one := ⟨1, by simp [Matrix.conjTranspose_one]⟩

noncomputable def mkMat (m00 m01 m10 m11 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![m00, m01], ![m10, m11]]

noncomputable def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := mkMat 0 1 1 0
noncomputable def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := mkMat 0 (-Complex.I) Complex.I 0
noncomputable def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := mkMat 1 0 0 (-1)

lemma trace_sigmaX : Matrix.trace sigmaX = 0 := by
  unfold Matrix.trace Matrix.diag sigmaX mkMat
  simp

lemma trace_sigmaY : Matrix.trace sigmaY = 0 := by
  unfold Matrix.trace Matrix.diag sigmaY mkMat
  simp

lemma trace_sigmaZ : Matrix.trace sigmaZ = 0 := by
  unfold Matrix.trace Matrix.diag sigmaZ mkMat
  simp

lemma toSl2c_val_eq (M : Matrix (Fin 2) (Fin 2) ℂ) (h_tr : Matrix.trace M = 0) : (toSl2c M).val = M := by
  unfold toSl2c; dsimp
  rw [h_tr]
  have hz : (0:ℂ) / 2 = 0 := by ring
  rw [hz, zero_smul, sub_zero]

noncomputable def sigma1 : SL2C := toSl2c sigmaX
noncomputable def sigma2 : SL2C := toSl2c sigmaY
noncomputable def sigma3 : SL2C := toSl2c sigmaZ

lemma val_sigma1 : sigma1.val = sigmaX := toSl2c_val_eq sigmaX trace_sigmaX
lemma val_sigma2 : sigma2.val = sigmaY := toSl2c_val_eq sigmaY trace_sigmaY
lemma val_sigma3 : sigma3.val = sigmaZ := toSl2c_val_eq sigmaZ trace_sigmaZ

def chiralIsoTo (x : Fin 2 ⊕ Fin 2) : Fin 4 :=
  match x with | Sum.inl i => if i.val = 0 then 0 else 1 | Sum.inr i => if i.val = 0 then 2 else 3

def chiralIsoInv (k : Fin 4) : Fin 2 ⊕ Fin 2 :=
  match k.val with | 0 => Sum.inl 0 | 1 => Sum.inl 1 | 2 => Sum.inr 0 | _ => Sum.inr 1

def chiralIso : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := chiralIsoTo
  invFun := chiralIsoInv
  left_inv := by intro x; cases x with | inl i => fin_cases i <;> rfl | inr i => fin_cases i <;> rfl
  right_inv := by intro k; fin_cases k <;> rfl

noncomputable def embedSelfDual (m : SL2C) : ChiralM := Matrix.of (fun i j => match (chiralIso.symm i), (chiralIso.symm j) with | Sum.inl i', Sum.inl j' => m.val i' j' | _, _ => 0)
noncomputable def embedAntiSelfDual (m : SL2C) : ChiralM := Matrix.of (fun i j => match (chiralIso.symm i), (chiralIso.symm j) with | Sum.inr i', Sum.inr j' => m.val i' j' | _, _ => 0)

structure ChiralComponents where
  self_dual : SL2C
  anti_self_dual  : SL2C

noncomputable def chiralProject (M : ChiralM) : ChiralComponents :=
  let b := M.submatrix chiralIso chiralIso
  { self_dual := toSl2c (fun i j => b (Sum.inl i) (Sum.inl j)), anti_self_dual := toSl2c (fun i j => b (Sum.inr i) (Sum.inr j)) }

end CGD.Foundations

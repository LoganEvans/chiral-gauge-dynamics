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

open Complex Matrix

namespace CGD.Foundations

/-- 
CRITICAL ONTOLOGY NOTE: 
Despite the historically inherited name `SL2C`, this type explicitly represents 
the **Lie Algebra** $\mathfrak{sl}(2,\mathbb{C})$ (the vector space of trace-free 
2x2 complex matrices), NOT the curved Lie Group (matrices with det=1).
Because it is a vector space natively built on a Mathlib submodule, it supports 
addition, scalar multiplication, and naturally inherits the `NormedSpace` topology 
required for `ContDiff` (smooth functional variations).
-/
noncomputable abbrev sl2cAlgebra := LieAlgebra.SpecialLinear.sl (Fin 2) Complex
abbrev SL2C := ↥sl2cAlgebra
abbrev ChiralM := Matrix (Fin 4) (Fin 4) Complex

lemma mem_sl_iff (A : Matrix (Fin 2) (Fin 2) Complex) : A ∈ sl2cAlgebra ↔ Matrix.trace A = 0 := by rfl

/-- The compact real form SU(2): Trace-free, anti-Hermitian 2x2 matrices. -/
def isSu2 (M : Matrix (Fin 2) (Fin 2) Complex) : Prop := 
  Matrix.trace M = 0 ∧ M.conjTranspose = -M

/-- We explicitly bind SU(2) as a trace-free physical phase space. -/
abbrev su2 := { M : SL2C // isSu2 M.val }

noncomputable def sigma1 : SL2C := ⟨Matrix.of ![![0, 1], ![1, 0]], by rw[mem_sl_iff, Matrix.trace_fin_two]; dsimp; ring⟩
noncomputable def sigma2 : SL2C := ⟨Matrix.of ![![0, -I], ![I, 0]], by rw[mem_sl_iff, Matrix.trace_fin_two]; dsimp; ring⟩
noncomputable def sigma3 : SL2C := ⟨Matrix.of ![![1, 0], ![0, -1]], by rw[mem_sl_iff, Matrix.trace_fin_two]; dsimp; ring⟩

def chiralIsoTo (x : Fin 2 ⊕ Fin 2) : Fin 4 :=
  match x with | Sum.inl i => if i.val = 0 then 0 else 1 | Sum.inr i => if i.val = 0 then 2 else 3

def chiralIsoInv (k : Fin 4) : Fin 2 ⊕ Fin 2 :=
  match k.val with | 0 => Sum.inl 0 | 1 => Sum.inl 1 | 2 => Sum.inr 0 | _ => Sum.inr 1

def chiralIso : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := chiralIsoTo
  invFun := chiralIsoInv
  left_inv := by intro x; cases x with | inl i => fin_cases i <;> rfl | inr i => fin_cases i <;> rfl
  right_inv := by intro k; fin_cases k <;> rfl

noncomputable def embedLight (m : SL2C) : ChiralM := Matrix.of (fun i j => match (chiralIso.symm i), (chiralIso.symm j) with | Sum.inl i', Sum.inl j' => m.val i' j' | _, _ => 0)
noncomputable def embedDark (m : SL2C) : ChiralM := Matrix.of (fun i j => match (chiralIso.symm i), (chiralIso.symm j) with | Sum.inr i', Sum.inr j' => m.val i' j' | _, _ => 0)

structure ChiralComponents where
  light : SL2C
  dark  : SL2C

noncomputable def toSl2c (M : Matrix (Fin 2) (Fin 2) Complex) : SL2C :=
  let tr := M.trace
  let M' := M - (tr / 2) • (1 : Matrix (Fin 2) (Fin 2) Complex)
  ⟨M', by rw[mem_sl_iff, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]; rw[Fintype.card_fin]; simp only[Nat.cast_ofNat]; rw[smul_eq_mul]; field_simp; ring⟩

noncomputable def chiralProject (M : ChiralM) : ChiralComponents :=
  let b := M.submatrix chiralIso chiralIso
  { light := toSl2c (fun i j => b (Sum.inl i) (Sum.inl j)), dark := toSl2c (fun i j => b (Sum.inr i) (Sum.inr j)) }

end CGD.Foundations

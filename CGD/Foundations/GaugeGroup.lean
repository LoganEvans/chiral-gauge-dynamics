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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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

noncomputable def extractAdjoint (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let c1 := (1 / 2 : ℂ) * Matrix.trace (M * sigma1.val)
  let c2 := (1 / 2 : ℂ) * Matrix.trace (M * sigma2.val)
  let c3 := (1 / 2 : ℂ) * Matrix.trace (M * sigma3.val)
  Matrix.of ![![0, c3, -c2], ![-c3, 0, c1], ![c2, -c1, 0]]

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

@[simp]
lemma chiralProject_embed_sd (L R : SL2C) :
  (chiralProject (embedSelfDual L + embedAntiSelfDual R)).self_dual = L := by
  apply Subtype.ext
  change (toSl2c (fun i j => (embedSelfDual L + embedAntiSelfDual R) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)))).val = L.val
  have h : (fun i j => (embedSelfDual L + embedAntiSelfDual R) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j))) = L.val := by
    ext i j
    change (embedSelfDual L) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) + (embedAntiSelfDual R) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) = L.val i j
    dsimp [embedSelfDual, embedAntiSelfDual]
    simp only [Equiv.symm_apply_apply]
    exact add_zero _
  rw [h]
  exact toSl2c_val_eq L.val L.property

@[simp]
lemma chiralProject_embed_asd (L R : SL2C) :
  (chiralProject (embedSelfDual L + embedAntiSelfDual R)).anti_self_dual = R := by
  apply Subtype.ext
  change (toSl2c (fun i j => (embedSelfDual L + embedAntiSelfDual R) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)))).val = R.val
  have h : (fun i j => (embedSelfDual L + embedAntiSelfDual R) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j))) = R.val := by
    ext i j
    change (embedSelfDual L) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) + (embedAntiSelfDual R) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) = R.val i j
    dsimp [embedSelfDual, embedAntiSelfDual]
    simp only [Equiv.symm_apply_apply]
    exact zero_add _
  rw [h]
  exact toSl2c_val_eq R.val R.property

-- ==============================================================================
-- ALGEBRAIC HELPERS FOR EMBEDDING TRACES AND ORTHOGONALITY
-- ==============================================================================

lemma embed_self_dual_inr_left (A : SL2C) (i : Fin 2) (j : Fin 4) :
  (embedSelfDual A) (chiralIso (Sum.inr i)) j = 0 := by
  unfold embedSelfDual
  simp only[Matrix.of_apply, Equiv.symm_apply_apply]

lemma embed_self_dual_inr_right (A : SL2C) (i : Fin 4) (j : Fin 2) :
  (embedSelfDual A) i (chiralIso (Sum.inr j)) = 0 := by
  unfold embedSelfDual
  simp only [Matrix.of_apply, Equiv.symm_apply_apply]
  cases chiralIso.symm i
  · rfl
  · rfl

lemma embed_anti_self_dual_inl_left (A : SL2C) (i : Fin 2) (j : Fin 4) :
  (embedAntiSelfDual A) (chiralIso (Sum.inl i)) j = 0 := by
  unfold embedAntiSelfDual
  simp only[Matrix.of_apply, Equiv.symm_apply_apply]

lemma embed_anti_self_dual_inl_right (A : SL2C) (i : Fin 4) (j : Fin 2) :
  (embedAntiSelfDual A) i (chiralIso (Sum.inl j)) = 0 := by
  unfold embedAntiSelfDual
  simp only [Matrix.of_apply, Equiv.symm_apply_apply]
  cases chiralIso.symm i
  · rfl
  · rfl

lemma embed_self_dual_inl_inl (A : SL2C) (i j : Fin 2) :
  (embedSelfDual A) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) = A.val i j := by
  unfold embedSelfDual
  simp only[Matrix.of_apply, Equiv.symm_apply_apply]

lemma embed_anti_self_dual_inr_inr (A : SL2C) (i j : Fin 2) :
  (embedAntiSelfDual A) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) = A.val i j := by
  unfold embedAntiSelfDual
  simp only [Matrix.of_apply, Equiv.symm_apply_apply]

lemma embed_self_dual_mul_inl_inl (A B : SL2C) (i j : Fin 2) :
  (embedSelfDual A * embedSelfDual B) (chiralIso (Sum.inl i)) (chiralIso (Sum.inl j)) =
  (A.val * B.val) i j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw[← Equiv.sum_comp chiralIso (fun k => (embedSelfDual A) (chiralIso (Sum.inl i)) k * (embedSelfDual B) k (chiralIso (Sum.inl j)))]
  rw[Fintype.sum_sum_type]
  have h_inr : ∑ x : Fin 2, (embedSelfDual A) (chiralIso (Sum.inl i)) (chiralIso (Sum.inr x)) * (embedSelfDual B) (chiralIso (Sum.inr x)) (chiralIso (Sum.inl j)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [embed_self_dual_inr_right]
    exact zero_mul _
  rw [h_inr, add_zero]
  apply Finset.sum_congr rfl
  intro x _
  rw[embed_self_dual_inl_inl, embed_self_dual_inl_inl]

lemma embed_anti_self_dual_mul_inr_inr (A B : SL2C) (i j : Fin 2) :
  (embedAntiSelfDual A * embedAntiSelfDual B) (chiralIso (Sum.inr i)) (chiralIso (Sum.inr j)) =
  (A.val * B.val) i j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw[← Equiv.sum_comp chiralIso (fun k => (embedAntiSelfDual A) (chiralIso (Sum.inr i)) k * (embedAntiSelfDual B) k (chiralIso (Sum.inr j)))]
  rw [Fintype.sum_sum_type]
  have h_inl : ∑ x : Fin 2, (embedAntiSelfDual A) (chiralIso (Sum.inr i)) (chiralIso (Sum.inl x)) * (embedAntiSelfDual B) (chiralIso (Sum.inl x)) (chiralIso (Sum.inr j)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw[embed_anti_self_dual_inl_right]
    exact zero_mul _
  rw[h_inl, zero_add]
  apply Finset.sum_congr rfl
  intro x _
  rw[embed_anti_self_dual_inr_inr, embed_anti_self_dual_inr_inr]

lemma embed_self_dual_mul_apply (A B : SL2C) (x y : Fin 2 ⊕ Fin 2) :
  (embedSelfDual A * embedSelfDual B) (chiralIso x) (chiralIso y) =
  match x, y with
  | Sum.inl i, Sum.inl j => (A.val * B.val) i j
  | _, _ => 0 := by
  cases x <;> cases y
  · exact embed_self_dual_mul_inl_inl A B _ _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_self_dual_inr_right]; exact mul_zero _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_self_dual_inr_left]; exact zero_mul _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_self_dual_inr_left]; exact zero_mul _

lemma embed_anti_self_dual_mul_apply (A B : SL2C) (x y : Fin 2 ⊕ Fin 2) :
  (embedAntiSelfDual A * embedAntiSelfDual B) (chiralIso x) (chiralIso y) =
  match x, y with
  | Sum.inr i, Sum.inr j => (A.val * B.val) i j
  | _, _ => 0 := by
  cases x <;> cases y
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_anti_self_dual_inl_left]; exact zero_mul _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_anti_self_dual_inl_left]; exact zero_mul _
  · rw[Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; rw[embed_anti_self_dual_inl_right]; exact mul_zero _
  · exact embed_anti_self_dual_mul_inr_inr A B _ _

lemma orthogonality_term (A B : SL2C) (i j k : Fin 4) :
  (embedSelfDual A) i k * (embedAntiSelfDual B) k j = 0 := by
  rw[embedSelfDual, embedAntiSelfDual]
  rw [Matrix.of_apply, Matrix.of_apply]
  cases hk : chiralIso.symm k with
  | inl kl => exact mul_zero _
  | inr kr =>
    cases hi : chiralIso.symm i with
    | inl il => exact zero_mul _
    | inr ir => exact zero_mul _

lemma chiralOrthogonality (A B : SL2C) : (embedSelfDual A) * (embedAntiSelfDual B) = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply orthogonality_term

lemma orthogonality_term_dl (A B : SL2C) (i j k : Fin 4) :
  (embedAntiSelfDual A) i k * (embedSelfDual B) k j = 0 := by
  rw[embedAntiSelfDual, embedSelfDual]
  rw [Matrix.of_apply, Matrix.of_apply]
  cases hk : chiralIso.symm k with
  | inl kl =>
    cases hi : chiralIso.symm i with
    | inl il => exact zero_mul _
    | inr ir => exact zero_mul _
  | inr kr =>
    cases hj : chiralIso.symm j with
    | inl jl => exact mul_zero _
    | inr jr => exact mul_zero _

lemma chiralOrthogonalityDl (A B : SL2C) : (embedAntiSelfDual A) * (embedSelfDual B) = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply orthogonality_term_dl

lemma trace_embed_self_dual_mul (A B : SL2C) :
  Matrix.trace (embedSelfDual A * embedSelfDual B) = Matrix.trace (A.val * B.val) := by
  rw [Matrix.trace, Matrix.trace]
  simp only[Matrix.diag]
  rw[← Equiv.sum_comp chiralIso (fun i => (embedSelfDual A * embedSelfDual B) i i)]
  rw [Fintype.sum_sum_type]
  have h_inr : ∑ x : Fin 2, (embedSelfDual A * embedSelfDual B) (chiralIso (Sum.inr x)) (chiralIso (Sum.inr x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    have hz : (embedSelfDual A) (chiralIso (Sum.inr x)) k = 0 := embed_self_dual_inr_left A x k
    rw[hz, zero_mul]
  rw [h_inr, add_zero]
  apply Finset.sum_congr rfl
  intro x _
  rw [embed_self_dual_mul_inl_inl]

lemma trace_embed_anti_self_dual_mul (A B : SL2C) :
  Matrix.trace (embedAntiSelfDual A * embedAntiSelfDual B) = Matrix.trace (A.val * B.val) := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag]
  rw[← Equiv.sum_comp chiralIso (fun i => (embedAntiSelfDual A * embedAntiSelfDual B) i i)]
  rw [Fintype.sum_sum_type]
  have h_inl : ∑ x : Fin 2, (embedAntiSelfDual A * embedAntiSelfDual B) (chiralIso (Sum.inl x)) (chiralIso (Sum.inl x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    have hz : (embedAntiSelfDual A) (chiralIso (Sum.inl x)) k = 0 := embed_anti_self_dual_inl_left A x k
    rw [hz, zero_mul]
  rw[h_inl, zero_add]
  apply Finset.sum_congr rfl
  intro x _
  rw[embed_anti_self_dual_mul_inr_inr]

lemma trace_embed_mul_embed (L1 R1 L2 R2 : SL2C) :
  Matrix.trace ((embedSelfDual L1 + embedAntiSelfDual R1) * (embedSelfDual L2 + embedAntiSelfDual R2)) =
  Matrix.trace (L1.val * L2.val) + Matrix.trace (R1.val * R2.val) := by
  have h1 : (embedSelfDual L1 + embedAntiSelfDual R1) * (embedSelfDual L2 + embedAntiSelfDual R2) =
    embedSelfDual L1 * embedSelfDual L2 + embedAntiSelfDual R1 * embedAntiSelfDual R2 := by
    rw[Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    rw[chiralOrthogonality, chiralOrthogonalityDl]
    simp
  rw[h1, Matrix.trace_add]
  rw[trace_embed_self_dual_mul, trace_embed_anti_self_dual_mul]

lemma to_sl2c_of_trace_zero (M : Matrix (Fin 2) (Fin 2) Complex) (h : Matrix.trace M = 0) :
  (toSl2c M).val = M := by
  unfold toSl2c
  dsimp
  rw [h]
  have h0 : (0 : Complex) / 2 = 0 := zero_div 2
  rw[h0, zero_smul, sub_zero]

end CGD.Foundations

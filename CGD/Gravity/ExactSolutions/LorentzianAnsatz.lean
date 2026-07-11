-- FILENAME: CGD/Gravity/ExactSolutions/LorentzianAnsatz.lean

import CGD.Gravity.ExactSolutions.Math

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

@[litlib_track "Linear-In-Coordinates Lorentzian Matrix Ansatz"]
noncomputable def exactLorentzianL (mu : Fin 4) (x : SpacetimePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  if mu = 1 then - (x 0 : ℝ) • sigmaX + (x 3 : ℝ) • ((Complex.I / 2) • sigmaY) - (x 2 : ℝ) • ((Complex.I / 2) • sigmaZ)
  else if mu = 2 then - (x 0 : ℝ) • sigmaY + (x 1 : ℝ) • ((Complex.I / 2) • sigmaZ) - (x 3 : ℝ) • ((Complex.I / 2) • sigmaX)
  else if mu = 3 then - (x 0 : ℝ) • sigmaZ + (x 2 : ℝ) • ((Complex.I / 2) • sigmaX) - (x 1 : ℝ) • ((Complex.I / 2) • sigmaY)
  else 0

noncomputable def exactLorentzianField (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  toSl2c (exactLorentzianL mu x)

lemma exactLorentzian_smooth (mu : Fin 4) (i j : Fin 2) : ContDiff ℝ ⊤ (fun x : SpacetimePoint => (exactLorentzianField mu x).val i j) := by
  dsimp [exactLorentzianField, exactLorentzianL]
  split_ifs with h1 h2 h3
  · let L : SpacetimePoint →L[ℝ] ℂ :=
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaX i j)) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 3) (((Complex.I / 2) • sigmaY) i j)) -
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 2) (((Complex.I / 2) • sigmaZ) i j))
    have h_eq : (fun x : SpacetimePoint => (toSl2c (- (x 0 : ℝ) • sigmaX + (x 3 : ℝ) • ((Complex.I / 2) • sigmaY) - (x 2 : ℝ) • ((Complex.I / 2) • sigmaZ))).val i j) = L := by
      ext x
      have h_tr : Matrix.trace (- (x 0 : ℝ) • sigmaX + (x 3 : ℝ) • ((Complex.I / 2) • sigmaY) - (x 2 : ℝ) • ((Complex.I / 2) • sigmaZ)) = 0 := by
        unfold Matrix.trace Matrix.diag sigmaX sigmaY sigmaZ mkMat; simp [Fin.sum_univ_two]
      rw [toSl2c_val_eq _ h_tr]
      change (- (x 0 : ℝ) • sigmaX + (x 3 : ℝ) • ((Complex.I / 2) • sigmaY) - (x 2 : ℝ) • ((Complex.I / 2) • sigmaZ)) i j =
        (x 0 : ℝ) • (-sigmaX i j) + (x 3 : ℝ) • (((Complex.I / 2) • sigmaY) i j) - (x 2 : ℝ) • (((Complex.I / 2) • sigmaZ) i j)
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
    rw [h_eq]
    exact ContinuousLinearMap.contDiff L
  · let L : SpacetimePoint →L[ℝ] ℂ :=
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaY i j)) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 1) (((Complex.I / 2) • sigmaZ) i j)) -
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 3) (((Complex.I / 2) • sigmaX) i j))
    have h_eq : (fun x : SpacetimePoint => (toSl2c (- (x 0 : ℝ) • sigmaY + (x 1 : ℝ) • ((Complex.I / 2) • sigmaZ) - (x 3 : ℝ) • ((Complex.I / 2) • sigmaX))).val i j) = L := by
      ext x
      have h_tr : Matrix.trace (- (x 0 : ℝ) • sigmaY + (x 1 : ℝ) • ((Complex.I / 2) • sigmaZ) - (x 3 : ℝ) • ((Complex.I / 2) • sigmaX)) = 0 := by
        unfold Matrix.trace Matrix.diag sigmaX sigmaY sigmaZ mkMat; simp [Fin.sum_univ_two]
      rw [toSl2c_val_eq _ h_tr]
      change (- (x 0 : ℝ) • sigmaY + (x 1 : ℝ) • ((Complex.I / 2) • sigmaZ) - (x 3 : ℝ) • ((Complex.I / 2) • sigmaX)) i j =
        (x 0 : ℝ) • (-sigmaY i j) + (x 1 : ℝ) • (((Complex.I / 2) • sigmaZ) i j) - (x 3 : ℝ) • (((Complex.I / 2) • sigmaX) i j)
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
    rw [h_eq]
    exact ContinuousLinearMap.contDiff L
  · let L : SpacetimePoint →L[ℝ] ℂ :=
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaZ i j)) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 2) (((Complex.I / 2) • sigmaX) i j)) -
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 1) (((Complex.I / 2) • sigmaY) i j))
    have h_eq : (fun x : SpacetimePoint => (toSl2c (- (x 0 : ℝ) • sigmaZ + (x 2 : ℝ) • ((Complex.I / 2) • sigmaX) - (x 1 : ℝ) • ((Complex.I / 2) • sigmaY))).val i j) = L := by
      ext x
      have h_tr : Matrix.trace (- (x 0 : ℝ) • sigmaZ + (x 2 : ℝ) • ((Complex.I / 2) • sigmaX) - (x 1 : ℝ) • ((Complex.I / 2) • sigmaY)) = 0 := by
        unfold Matrix.trace Matrix.diag sigmaX sigmaY sigmaZ mkMat; simp [Fin.sum_univ_two]
      rw [toSl2c_val_eq _ h_tr]
      change (- (x 0 : ℝ) • sigmaZ + (x 2 : ℝ) • ((Complex.I / 2) • sigmaX) - (x 1 : ℝ) • ((Complex.I / 2) • sigmaY)) i j =
        (x 0 : ℝ) • (-sigmaZ i j) + (x 2 : ℝ) • (((Complex.I / 2) • sigmaX) i j) - (x 1 : ℝ) • (((Complex.I / 2) • sigmaY) i j)
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
    rw [h_eq]
    exact ContinuousLinearMap.contDiff L
  · exact contDiff_const

noncomputable def L_0 : SpacetimePoint →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ := 0
noncomputable def L_1 : SpacetimePoint →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaX)) +
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 3) ((Complex.I / 2) • sigmaY)) -
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 2) ((Complex.I / 2) • sigmaZ))
noncomputable def L_2 : SpacetimePoint →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaY)) +
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 1) ((Complex.I / 2) • sigmaZ)) -
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 3) ((Complex.I / 2) • sigmaX))
noncomputable def L_3 : SpacetimePoint →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaZ)) +
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 2) ((Complex.I / 2) • sigmaX)) -
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 1) ((Complex.I / 2) • sigmaY))

noncomputable def L_map (mu : Fin 4) : SpacetimePoint →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  if mu = 1 then L_1
  else if mu = 2 then L_2
  else if mu = 3 then L_3
  else L_0

lemma exactLorentzianL_eq_L_map (mu : Fin 4) (p : SpacetimePoint) :
  exactLorentzianL mu p = L_map mu p := by
  unfold exactLorentzianL L_map L_1 L_2 L_3 L_0
  split_ifs <;> {
    ext i j
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply]
  }

lemma exactLorentzianL_trace_zero (mu : Fin 4) (p : SpacetimePoint) :
  Matrix.trace (exactLorentzianL mu p) = 0 := by
  unfold exactLorentzianL
  split_ifs with h1 h2 h3
  · unfold Matrix.trace Matrix.diag sigmaX sigmaY sigmaZ mkMat; simp [Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
  · unfold Matrix.trace Matrix.diag sigmaX sigmaY sigmaZ mkMat; simp [Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
  · unfold Matrix.trace Matrix.diag sigmaX sigmaY sigmaZ mkMat; simp [Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
  · unfold Matrix.trace Matrix.diag; simp [Fin.sum_univ_two]

lemma val_exactLorentzianField_eq (mu : Fin 4) (p : SpacetimePoint) :
  (exactLorentzianField mu p).val = L_map mu p := by
  unfold exactLorentzianField
  have h_tr := exactLorentzianL_trace_zero mu p
  rw [toSl2c_val_eq _ h_tr]
  exact exactLorentzianL_eq_L_map mu p

lemma partialDeriv_L_map (mu k : Fin 4) (x : SpacetimePoint) (i j : Fin 2) :
  partialDeriv k (fun p => L_map mu p i j) x = L_map mu (Pi.single k 1) i j := by
  unfold L_map
  split_ifs with h1 h2 h3
  · let L : SpacetimePoint →L[ℝ] ℂ :=
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaX i j)) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 3) (((Complex.I / 2) • sigmaY) i j)) -
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 2) (((Complex.I / 2) • sigmaZ) i j))
    have h_eq : (fun p => L_1 p i j) = L := by
      ext p; unfold L_1
      have h_L_eval : L p = (p 0 : ℝ) • (-sigmaX i j) + (p 3 : ℝ) • (((Complex.I / 2) • sigmaY) i j) - (p 2 : ℝ) • (((Complex.I / 2) • sigmaZ) i j) := rfl
      rw [h_L_eval]
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
    rw [h_eq]
    exact partialDeriv_cL L k x
  · let L : SpacetimePoint →L[ℝ] ℂ :=
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaY i j)) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 1) (((Complex.I / 2) • sigmaZ) i j)) -
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 3) (((Complex.I / 2) • sigmaX) i j))
    have h_eq : (fun p => L_2 p i j) = L := by
      ext p; unfold L_2
      have h_L_eval : L p = (p 0 : ℝ) • (-sigmaY i j) + (p 1 : ℝ) • (((Complex.I / 2) • sigmaZ) i j) - (p 3 : ℝ) • (((Complex.I / 2) • sigmaX) i j) := rfl
      rw [h_L_eval]
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
    rw [h_eq]
    exact partialDeriv_cL L k x
  · let L : SpacetimePoint →L[ℝ] ℂ :=
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 0) (-sigmaZ i j)) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 2) (((Complex.I / 2) • sigmaX) i j)) -
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj 1) (((Complex.I / 2) • sigmaY) i j))
    have h_eq : (fun p => L_3 p i j) = L := by
      ext p; unfold L_3
      have h_L_eval : L p = (p 0 : ℝ) • (-sigmaZ i j) + (p 2 : ℝ) • (((Complex.I / 2) • sigmaX) i j) - (p 1 : ℝ) • (((Complex.I / 2) • sigmaY) i j) := rfl
      rw [h_L_eval]
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply]
    rw [h_eq]
    exact partialDeriv_cL L k x
  · let L : SpacetimePoint →L[ℝ] ℂ := 0
    have h_eq : (fun p => L_0 p i j) = L := by
      ext p; unfold L_0; rfl
    rw [h_eq]
    exact partialDeriv_cL L k x

lemma partialDerivMat_exactLorentzian (k mu : Fin 4) (x : SpacetimePoint) :
  partialDerivMat k (fun p => (exactLorentzianField mu p).val) x = L_map mu (Pi.single k 1) := by
  ext i j
  unfold partialDerivMat
  have h_eq : (fun p => (exactLorentzianField mu p).val i j) = (fun p => L_map mu p i j) := by
    ext p; rw [val_exactLorentzianField_eq]
  rw [h_eq]
  exact partialDeriv_L_map mu k x i j

lemma partialDerivSl2c_exactLorentzian_eval (k mu : Fin 4) (x : SpacetimePoint) :
  partialDerivSl2c k (exactLorentzianField mu) x = toSl2c (L_map mu (Pi.single k 1)) := by
  unfold partialDerivSl2c
  rw [partialDerivMat_exactLorentzian]

noncomputable def origin : SpacetimePoint := fun _ => 0

lemma exactLorentzianField_origin_zero (mu : Fin 4) :
  exactLorentzianField mu origin = 0 := by
  apply Subtype.ext
  rw [val_exactLorentzianField_eq mu origin]
  unfold L_map L_1 L_2 L_3 L_0 origin
  split_ifs <;> {
    ext i j
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply]
  }

lemma exactLorentzian_comm_origin (mu nu : Fin 4) :
  ⁅exactLorentzianField mu origin, exactLorentzianField nu origin⁆ = 0 := by
  have h_mu : exactLorentzianField mu origin = 0 := exactLorentzianField_origin_zero mu
  have h_nu : exactLorentzianField nu origin = 0 := exactLorentzianField_origin_zero nu
  rw [h_mu, h_nu]
  simp

noncomputable def c_F_mat (mu nu : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  L_map nu (Pi.single mu 1) - L_map mu (Pi.single nu 1)

lemma curvature_origin_eq (mu nu : Fin 4) :
  curvatureSl2c exactLorentzianField mu nu origin = toSl2c (c_F_mat mu nu) := by
  rw [curvatureSl2c_def]
  rw [exactLorentzian_comm_origin mu nu, add_zero]
  rw [partialDerivSl2c_exactLorentzian_eval, partialDerivSl2c_exactLorentzian_eval]
  rw [toSl2c_sub]
  rfl

noncomputable def F_origin_val (mu nu : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if mu = 0 ∧ nu = 1 then -sigmaX
  else if mu = 0 ∧ nu = 2 then -sigmaY
  else if mu = 0 ∧ nu = 3 then -sigmaZ
  else if mu = 1 ∧ nu = 0 then sigmaX
  else if mu = 2 ∧ nu = 0 then sigmaY
  else if mu = 3 ∧ nu = 0 then sigmaZ
  else if mu = 1 ∧ nu = 2 then Complex.I • sigmaZ
  else if mu = 2 ∧ nu = 1 then -Complex.I • sigmaZ
  else if mu = 1 ∧ nu = 3 then -Complex.I • sigmaY
  else if mu = 3 ∧ nu = 1 then Complex.I • sigmaY
  else if mu = 2 ∧ nu = 3 then Complex.I • sigmaX
  else if mu = 3 ∧ nu = 2 then -Complex.I • sigmaX
  else 0

lemma c_F_mat_0_1 : c_F_mat 0 1 = -sigmaX := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_0_2 : c_F_mat 0 2 = -sigmaY := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_0_3 : c_F_mat 0 3 = -sigmaZ := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_1_0 : c_F_mat 1 0 = sigmaX := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_2_0 : c_F_mat 2 0 = sigmaY := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_3_0 : c_F_mat 3 0 = sigmaZ := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_1_2 : c_F_mat 1 2 = Complex.I • sigmaZ := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_2_1 : c_F_mat 2 1 = -Complex.I • sigmaZ := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_1_3 : c_F_mat 1 3 = -Complex.I • sigmaY := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_3_1 : c_F_mat 3 1 = Complex.I • sigmaY := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_2_3 : c_F_mat 2 3 = Complex.I • sigmaX := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_3_2 : c_F_mat 3 2 = -Complex.I • sigmaX := by
  ext i j
  unfold c_F_mat L_map L_1 L_2 L_3 L_0
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, Pi.single, Function.update]
  try push_cast
  try ring

lemma c_F_mat_same (mu : Fin 4) : c_F_mat mu mu = 0 := by
  unfold c_F_mat
  exact sub_self (L_map mu (Pi.single mu 1))

lemma c_F_mat_eval (mu nu : Fin 4) : c_F_mat mu nu = F_origin_val mu nu := by
  fin_cases mu <;> fin_cases nu
  · change c_F_mat 0 0 = F_origin_val 0 0; rw [c_F_mat_same 0]; rfl
  · change c_F_mat 0 1 = F_origin_val 0 1; rw [c_F_mat_0_1]; rfl
  · change c_F_mat 0 2 = F_origin_val 0 2; rw [c_F_mat_0_2]; rfl
  · change c_F_mat 0 3 = F_origin_val 0 3; rw [c_F_mat_0_3]; rfl
  · change c_F_mat 1 0 = F_origin_val 1 0; rw [c_F_mat_1_0]; rfl
  · change c_F_mat 1 1 = F_origin_val 1 1; rw [c_F_mat_same 1]; rfl
  · change c_F_mat 1 2 = F_origin_val 1 2; rw [c_F_mat_1_2]; rfl
  · change c_F_mat 1 3 = F_origin_val 1 3; rw [c_F_mat_1_3]; rfl
  · change c_F_mat 2 0 = F_origin_val 2 0; rw [c_F_mat_2_0]; rfl
  · change c_F_mat 2 1 = F_origin_val 2 1; rw [c_F_mat_2_1]; rfl
  · change c_F_mat 2 2 = F_origin_val 2 2; rw [c_F_mat_same 2]; rfl
  · change c_F_mat 2 3 = F_origin_val 2 3; rw [c_F_mat_2_3]; rfl
  · change c_F_mat 3 0 = F_origin_val 3 0; rw [c_F_mat_3_0]; rfl
  · change c_F_mat 3 1 = F_origin_val 3 1; rw [c_F_mat_3_1]; rfl
  · change c_F_mat 3 2 = F_origin_val 3 2; rw [c_F_mat_3_2]; rfl
  · change c_F_mat 3 3 = F_origin_val 3 3; rw [c_F_mat_same 3]; rfl

noncomputable def adj_F (mu nu : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ :=
  extractAdjoint (F_origin_val mu nu)

lemma gauge_field_eq (A : Sl2cGaugeField) (v : Fin 4 → SpacetimePoint → SL2C)
  (smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (v mu x).val i j))
  (h : A.val = v) : A = { val := v, is_smooth := smooth } := by
  cases A with
  | mk A_val A_smooth =>
    dsimp at h
    subst h
    rfl

lemma F_origin_val_trace (mu nu : Fin 4) : Matrix.trace (F_origin_val mu nu) = 0 := by
  fin_cases mu <;> fin_cases nu <;> {
    unfold Matrix.trace Matrix.diag
    rw [Fin.sum_univ_two]
    dsimp [F_origin_val, sigmaX, sigmaY, sigmaZ, mkMat, Matrix.smul_apply, Matrix.neg_apply]
    ring
  }

lemma cgdAdjointCurvature_eval (u : Universe) (mu nu : Fin 4)
  (h_sd : u.sd_sector.val = exactLorentzianField) :
  cgdAdjointCurvature u mu nu origin = adj_F mu nu := by
  have h_def : cgdAdjointCurvature u mu nu origin = extractAdjoint (curvatureSl2c u.sd_sector mu nu origin).val := rfl
  rw [h_def]

  have h_sd_full : u.sd_sector = { val := exactLorentzianField, is_smooth := exactLorentzian_smooth } :=
    gauge_field_eq u.sd_sector exactLorentzianField exactLorentzian_smooth h_sd
  rw [h_sd_full]

  rw [curvature_origin_eq mu nu]
  rw [c_F_mat_eval mu nu]
  rw [toSl2c_val_eq (F_origin_val mu nu) (F_origin_val_trace mu nu)]
  rfl

end CGD.Gravity

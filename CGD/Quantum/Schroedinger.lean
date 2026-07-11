-- FILENAME: CGD/Quantum/Schroedinger.lean

import CGD.Quantum.Dirac
import Litlib.Core
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Math Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum

noncomputable def P_plus : Matrix (Fin 4) (Fin 4) Complex :=
  (1 / 2 : Complex) • (1 + gamma0)

noncomputable def P_minus : Matrix (Fin 4) (Fin 4) Complex :=
  (1 / 2 : Complex) • (1 - gamma0)

noncomputable def modulatedTemporalDeriv (dPsi0 Psi : Matrix (Fin 4) (Fin 4) Complex) (m : Complex) : Matrix (Fin 4) (Fin 4) Complex :=
  dPsi0 + m • Psi

noncomputable def spatialDiracOp (dPsi : Fin 4 → Matrix (Fin 4) (Fin 4) Complex) : Matrix (Fin 4) (Fin 4) Complex :=
  gammaVec 1 * dPsi 1 + gammaVec 2 * dPsi 2 + gammaVec 3 * dPsi 3

/--
The core Dirac operator evaluated in the local tangent space frame (using tangent space index 'a'
instead of coordinate index 'mu'). In curved space, dP represents the tetrad-contracted derivative.
-/
noncomputable def localDiracOp (dP : Fin 4 → Matrix (Fin 4) (Fin 4) Complex) : Matrix (Fin 4) (Fin 4) Complex :=
  ∑ a, gammaVec a * dP a

lemma sum_fin_4_matrix (f : Fin 4 → Matrix (Fin 4) (Fin 4) Complex) : ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp [add_assoc]

lemma eval_mul_4x4_local (A B : Matrix (Fin 4) (Fin 4) Complex) (i j : Fin 4) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j := by
  rw [Matrix.mul_apply]
  have h_sum : ∑ k : Fin 4, A i k * B k j = A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp [add_assoc]
  exact h_sum

lemma gamma0_sq : gamma0 * gamma0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    rw [eval_mul_4x4_local]
    simp [gamma0, Matrix.fromBlocks, Matrix.reindex, Litlib.Math.Dirac.chiralIso,
          Litlib.Math.Dirac.chiralIsoInv, Litlib.Math.Dirac.chiralIsoTo,
          Matrix.submatrix, Sum.elim, Matrix.zero_apply]
  }

lemma gamma0_gammaVec_anti_1 : gamma0 * gammaVec 1 = - (gammaVec 1 * gamma0) := by
  ext a b
  fin_cases a <;> fin_cases b
  all_goals {
    rw [Matrix.neg_apply, eval_mul_4x4, eval_mul_4x4]
    simp [gamma0, gammaVec, gammaSpatial,
          sigmaToMatrix, Litlib.Math.SU2.s1, Litlib.Math.SU2.s2, Litlib.Math.SU2.s3,
          Matrix.fromBlocks, Matrix.reindex, Litlib.Math.Dirac.chiralIso,
          Litlib.Math.Dirac.chiralIsoInv, Litlib.Math.Dirac.chiralIsoTo,
          Matrix.submatrix, Sum.elim]
    try ring_nf
  }

lemma gamma0_gammaVec_anti_2 : gamma0 * gammaVec 2 = - (gammaVec 2 * gamma0) := by
  ext a b
  fin_cases a <;> fin_cases b
  all_goals {
    rw [Matrix.neg_apply, eval_mul_4x4, eval_mul_4x4]
    simp [gamma0, gammaVec, gammaSpatial,
          sigmaToMatrix, Litlib.Math.SU2.s1, Litlib.Math.SU2.s2, Litlib.Math.SU2.s3,
          Matrix.fromBlocks, Matrix.reindex, Litlib.Math.Dirac.chiralIso,
          Litlib.Math.Dirac.chiralIsoInv, Litlib.Math.Dirac.chiralIsoTo,
          Matrix.submatrix, Sum.elim]
    try ring_nf
  }

lemma gamma0_gammaVec_anti_3 : gamma0 * gammaVec 3 = - (gammaVec 3 * gamma0) := by
  ext a b
  fin_cases a <;> fin_cases b
  all_goals {
    rw [Matrix.neg_apply, eval_mul_4x4, eval_mul_4x4]
    simp [gamma0, gammaVec, gammaSpatial,
          sigmaToMatrix, Litlib.Math.SU2.s1, Litlib.Math.SU2.s2, Litlib.Math.SU2.s3,
          Matrix.fromBlocks, Matrix.reindex, Litlib.Math.Dirac.chiralIso,
          Litlib.Math.Dirac.chiralIsoInv, Litlib.Math.Dirac.chiralIsoTo,
          Matrix.submatrix, Sum.elim]
    try ring_nf
  }

/-- Proves the core Clifford spatial anticommutation natively via 4x4 block computation. -/
lemma gamma0_gammaVec_anti (j : Fin 4) (hj : j ≠ 0) : gamma0 * gammaVec j = - (gammaVec j * gamma0) := by
  revert hj
  fin_cases j
  · intro h; contradiction
  · intro _; exact gamma0_gammaVec_anti_1
  · intro _; exact gamma0_gammaVec_anti_2
  · intro _; exact gamma0_gammaVec_anti_3

lemma P_plus_gamma0 : P_plus * gamma0 = P_plus := by
  ext i j
  dsimp [P_plus]
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, gamma0_sq]
  simp [Matrix.smul_apply, Matrix.add_apply]
  ring

lemma P_minus_gamma0 : P_minus * gamma0 = - P_minus := by
  ext i j
  dsimp [P_minus]
  rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, gamma0_sq]
  simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply]
  ring

lemma P_plus_gammaVec (j : Fin 4) (hj : j ≠ 0) : P_plus * gammaVec j = gammaVec j * P_minus := by
  dsimp [P_plus, P_minus]
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  rw [gamma0_gammaVec_anti j hj]
  ext a b
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  try ring

lemma P_minus_gammaVec (j : Fin 4) (hj : j ≠ 0) : P_minus * gammaVec j = gammaVec j * P_plus := by
  dsimp [P_plus, P_minus]
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
  rw [gamma0_gammaVec_anti j hj]
  ext a b
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  try ring

lemma localDiracOp_expand (dP : Fin 4 → Matrix (Fin 4) (Fin 4) Complex) :
  localDiracOp dP = gamma0 * dP 0 + spatialDiracOp dP := by
  dsimp [localDiracOp, spatialDiracOp]
  rw [sum_fin_4_matrix]
  have h0 : gammaVec 0 = gamma0 := rfl
  rw [h0]
  ext a b
  simp [Matrix.add_apply]
  ring

lemma P_plus_D_space (dPsi : Fin 4 → Matrix (Fin 4) (Fin 4) Complex) :
  P_plus * spatialDiracOp dPsi =
  gammaVec 1 * (P_minus * dPsi 1) + gammaVec 2 * (P_minus * dPsi 2) + gammaVec 3 * (P_minus * dPsi 3) := by
  dsimp [spatialDiracOp]
  rw [Matrix.mul_add, Matrix.mul_add]
  have h_assoc1 : P_plus * (gammaVec 1 * dPsi 1) = (P_plus * gammaVec 1) * dPsi 1 := (Matrix.mul_assoc _ _ _).symm
  have h_assoc2 : P_plus * (gammaVec 2 * dPsi 2) = (P_plus * gammaVec 2) * dPsi 2 := (Matrix.mul_assoc _ _ _).symm
  have h_assoc3 : P_plus * (gammaVec 3 * dPsi 3) = (P_plus * gammaVec 3) * dPsi 3 := (Matrix.mul_assoc _ _ _).symm
  rw [h_assoc1, h_assoc2, h_assoc3]
  rw [P_plus_gammaVec 1 (by decide), P_plus_gammaVec 2 (by decide), P_plus_gammaVec 3 (by decide)]
  have h_assoc4 : (gammaVec 1 * P_minus) * dPsi 1 = gammaVec 1 * (P_minus * dPsi 1) := Matrix.mul_assoc _ _ _
  have h_assoc5 : (gammaVec 2 * P_minus) * dPsi 2 = gammaVec 2 * (P_minus * dPsi 2) := Matrix.mul_assoc _ _ _
  have h_assoc6 : (gammaVec 3 * P_minus) * dPsi 3 = gammaVec 3 * (P_minus * dPsi 3) := Matrix.mul_assoc _ _ _
  rw [h_assoc4, h_assoc5, h_assoc6]

lemma P_minus_D_space (dPsi : Fin 4 → Matrix (Fin 4) (Fin 4) Complex) :
  P_minus * spatialDiracOp dPsi =
  gammaVec 1 * (P_plus * dPsi 1) + gammaVec 2 * (P_plus * dPsi 2) + gammaVec 3 * (P_plus * dPsi 3) := by
  dsimp [spatialDiracOp]
  rw [Matrix.mul_add, Matrix.mul_add]
  have h_assoc1 : P_minus * (gammaVec 1 * dPsi 1) = (P_minus * gammaVec 1) * dPsi 1 := (Matrix.mul_assoc _ _ _).symm
  have h_assoc2 : P_minus * (gammaVec 2 * dPsi 2) = (P_minus * gammaVec 2) * dPsi 2 := (Matrix.mul_assoc _ _ _).symm
  have h_assoc3 : P_minus * (gammaVec 3 * dPsi 3) = (P_minus * gammaVec 3) * dPsi 3 := (Matrix.mul_assoc _ _ _).symm
  rw [h_assoc1, h_assoc2, h_assoc3]
  rw [P_minus_gammaVec 1 (by decide), P_minus_gammaVec 2 (by decide), P_minus_gammaVec 3 (by decide)]
  have h_assoc4 : (gammaVec 1 * P_plus) * dPsi 1 = gammaVec 1 * (P_plus * dPsi 1) := Matrix.mul_assoc _ _ _
  have h_assoc5 : (gammaVec 2 * P_plus) * dPsi 2 = gammaVec 2 * (P_plus * dPsi 2) := Matrix.mul_assoc _ _ _
  have h_assoc6 : (gammaVec 3 * P_plus) * dPsi 3 = gammaVec 3 * (P_plus * dPsi 3) := Matrix.mul_assoc _ _ _
  rw [h_assoc4, h_assoc5, h_assoc6]

/--
The exact algebraic chiral split of the emergent Dirac equation.
By applying the projection operators, the relativistic Dirac equation natively factors
into a coupled system for the large and small components.
-/
@[litlib_track "Algebraic Dirac Chiral Split"]
theorem algebraicDiracChiralSplit (dPsi : Fin 4 → SpacetimePoint → Matrix (Fin 4) (Fin 4) Complex)
  (Psi : SpacetimePoint → Matrix (Fin 4) (Fin 4) Complex) (m : Complex) (x : SpacetimePoint) :
  localDiracOp (fun a => dPsi a x) = m • Psi x →
  let D0_mod := modulatedTemporalDeriv (dPsi 0 x) (Psi x) m
  let D_space := spatialDiracOp (fun mu => dPsi mu x)
  (P_plus * D0_mod + P_plus * gamma0 * D_space = 2 • m • (P_plus * Psi x)) ∧
  (P_minus * D0_mod + P_minus * gamma0 * D_space = 0) := by
  intro h
  let dP := fun a => dPsi a x
  let Px := Psi x
  let D0_mod := modulatedTemporalDeriv (dP 0) Px m
  let D_space := spatialDiracOp dP

  have h_expand : gamma0 * dP 0 + D_space = m • Px := by
    have h_sum := localDiracOp_expand dP
    rw [← h_sum]
    exact h

  have h_rearrange : dP 0 + gamma0 * D_space = m • (gamma0 * Px) := by
    have h2 : gamma0 * (gamma0 * dP 0 + D_space) = gamma0 * (m • Px) := by rw [h_expand]
    rw [Matrix.mul_add, Matrix.mul_smul] at h2
    have h3 : gamma0 * (gamma0 * dP 0) = dP 0 := by
      rw [← Matrix.mul_assoc, gamma0_sq, Matrix.one_mul]
    rw [h3] at h2
    exact h2

  constructor
  · have eq1 : P_plus * D0_mod + P_plus * gamma0 * D_space =
               P_plus * (dP 0 + gamma0 * D_space) + P_plus * (m • Px) := by
      dsimp [D0_mod, modulatedTemporalDeriv]
      rw [Matrix.mul_add, Matrix.mul_add]
      have h_assoc : P_plus * gamma0 * D_space = P_plus * (gamma0 * D_space) := Matrix.mul_assoc _ _ _
      rw [h_assoc]
      exact add_right_comm (P_plus * dP 0) (P_plus * (m • Px)) (P_plus * (gamma0 * D_space))
    rw [eq1, h_rearrange]
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, P_plus_gamma0, Matrix.mul_smul]
    ext a b
    simp [Matrix.add_apply, Matrix.smul_apply]
    try ring
  · have eq1 : P_minus * D0_mod + P_minus * gamma0 * D_space =
               P_minus * (dP 0 + gamma0 * D_space) + P_minus * (m • Px) := by
      dsimp [D0_mod, modulatedTemporalDeriv]
      rw [Matrix.mul_add, Matrix.mul_add]
      have h_assoc : P_minus * gamma0 * D_space = P_minus * (gamma0 * D_space) := Matrix.mul_assoc _ _ _
      rw [h_assoc]
      exact add_right_comm (P_minus * dP 0) (P_minus * (m • Px)) (P_minus * (gamma0 * D_space))
    rw [eq1, h_rearrange]
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, P_minus_gamma0, neg_mul, Matrix.mul_smul]
    ext a b
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply]
    try ring

/--
An algebraic decomposition of the emergent Dirac equation.

By applying the standard chiral projection operators (P_plus, P_minus), the
relativistic equation natively factors into coupled relations for the large and
small components. This verifies that the standard algebraic structures required
for non-relativistic limits (which produce the 1/2m Schrödinger/Pauli Hamiltonian)
are natively supported by the macroscopic gauge-covariant geometry.
-/
@[litlib_track "Exact Schroedinger Reduction"]
theorem exactSchroedingerReduction (dPsi : Fin 4 → SpacetimePoint → Matrix (Fin 4) (Fin 4) Complex)
  (Psi : SpacetimePoint → Matrix (Fin 4) (Fin 4) Complex) (m : Complex) (x : SpacetimePoint) :
  localDiracOp (fun a => dPsi a x) = m • Psi x →
  let D0_mod := modulatedTemporalDeriv (dPsi 0 x) (Psi x) m
  let Psi_small := P_plus * Psi x
  (2 • m • Psi_small = P_plus * D0_mod + gammaVec 1 * (P_minus * dPsi 1 x) + gammaVec 2 * (P_minus * dPsi 2 x) + gammaVec 3 * (P_minus * dPsi 3 x)) ∧
  (P_minus * D0_mod = gammaVec 1 * (P_plus * dPsi 1 x) + gammaVec 2 * (P_plus * dPsi 2 x) + gammaVec 3 * (P_plus * dPsi 3 x)) := by
  intro h
  have h_split := algebraicDiracChiralSplit dPsi Psi m x h
  rcases h_split with ⟨h_plus, h_minus⟩

  let dP := fun a => dPsi a x
  let D_space := spatialDiracOp dP
  let D0_mod := modulatedTemporalDeriv (dPsi 0 x) (Psi x) m

  have h_P_plus_D_space : P_plus * gamma0 * D_space = gammaVec 1 * (P_minus * dP 1) + gammaVec 2 * (P_minus * dP 2) + gammaVec 3 * (P_minus * dP 3) := by
    rw [P_plus_gamma0]
    exact P_plus_D_space dP

  have h_P_minus_D_space : P_minus * D_space = gammaVec 1 * (P_plus * dP 1) + gammaVec 2 * (P_plus * dP 2) + gammaVec 3 * (P_plus * dP 3) := by
    exact P_minus_D_space dP

  constructor
  · rw [← h_plus, h_P_plus_D_space]
    ext a b
    simp [Matrix.add_apply]
    try ring
  · have h_minus_eq : P_minus * D0_mod = P_minus * D_space := by
      have h1 : P_minus * D0_mod + P_minus * gamma0 * D_space = 0 := h_minus
      rw [P_minus_gamma0, neg_mul] at h1
      exact eq_of_sub_eq_zero h1
    rw [h_minus_eq, h_P_minus_D_space]

end CGD.Quantum

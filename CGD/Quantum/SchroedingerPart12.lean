-- FILENAME: CGD/Quantum/SchroedingerPart12.lean

import CGD.Quantum.SchroedingerPart11

open CGD.Foundations Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum

/--
The exact algebraic chiral split of the emergent Dirac equation.
By applying the projection operators, the relativistic Dirac equation natively factors 
into a coupled system for the large and small components.
-/
theorem algebraicDiracChiralSplit (dPsi : Fin 4 → SpacetimePoint → Matrix (Fin 4) (Fin 4) Complex) 
  (Psi : SpacetimePoint → Matrix (Fin 4) (Fin 4) Complex) (m : Complex) (x : SpacetimePoint) :
  CGD.Quantum.diracOperatorCore dPsi x = m • Psi x →
  let D0_mod := modulatedTemporalDeriv (dPsi 0 x) (Psi x) m
  let D_space := spatialDiracOp (fun mu => dPsi mu x)
  (P_plus * D0_mod + P_plus * gamma0 * D_space = 2 • m • (P_plus * Psi x)) ∧
  (P_minus * D0_mod + P_minus * gamma0 * D_space = 0) := by
  intro h
  let dP := fun mu => dPsi mu x
  let Px := Psi x
  let D0_mod := modulatedTemporalDeriv (dP 0) Px m
  let D_space := spatialDiracOp dP
  
  have h_expand : gamma0 * dP 0 + D_space = m • Px := by
    have h_sum := diracOperatorCore_expand dP
    change (∑ mu, gammaVec mu * dP mu) = m • Px at h
    rw [h_sum] at h
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

end CGD.Quantum

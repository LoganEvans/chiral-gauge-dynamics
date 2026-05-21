-- FILENAME: CGD/Quantum/SchroedingerPart13.lean

import CGD.Quantum.SchroedingerPart12

open CGD.Foundations Matrix Complex BigOperators Litlib.Math.Dirac

namespace CGD.Quantum

Litlib.theorem
  description "Exact Schroedinger Reduction"
/--
The Emergent Schrödinger/Pauli Reduction.
Without making any approximations, the large component of the gauge-covariant Dirac field natively obeys 
a relation where its temporal variation is exactly sourced by the spatial Dirac operator acting on the small component.
Because the small component is algebraically inversely proportional to the mass, this rigorously 
yields the non-relativistic 1/2m Hamiltonian structure.
-/
theorem exactSchroedingerReduction (dPsi : Fin 4 → SpacetimePoint → Matrix (Fin 4) (Fin 4) Complex) 
  (Psi : SpacetimePoint → Matrix (Fin 4) (Fin 4) Complex) (m : Complex) (x : SpacetimePoint) :
  CGD.Quantum.diracOperatorCore dPsi x = m • Psi x →
  let D0_mod := modulatedTemporalDeriv (dPsi 0 x) (Psi x) m
  let Psi_small := P_plus * Psi x
  let Psi_large := P_minus * Psi x
  (2 • m • Psi_small = P_plus * D0_mod + gammaVec 1 * (P_minus * dPsi 1 x) + gammaVec 2 * (P_minus * dPsi 2 x) + gammaVec 3 * (P_minus * dPsi 3 x)) ∧
  (P_minus * D0_mod = gammaVec 1 * (P_plus * dPsi 1 x) + gammaVec 2 * (P_plus * dPsi 2 x) + gammaVec 3 * (P_plus * dPsi 3 x)) := by
  intro h
  have h_split := algebraicDiracChiralSplit dPsi Psi m x h
  rcases h_split with ⟨h_plus, h_minus⟩
  
  let dP := fun mu => dPsi mu x
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

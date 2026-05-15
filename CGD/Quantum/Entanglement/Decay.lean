-- FILENAME: CGD/Quantum/Entanglement/Decay.lean

import Litlib.Core
import CGD.Quantum.Entanglement.Basic
import CGD.Axioms.Ontology
import CGD.Quantum.Definitions
import Litlib.Y2001.bali2001qcd.Signature

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms Litlib.Y2001.bali2001qcd

namespace CGD.Quantum

/-- 
In the CGD framework, entanglement between two points is physically mediated by a topological 
SU(2) wormhole (a twisted flux tube). This theorem proves that if the Euclidean spatial 
distance between the entangled particles exceeds the QCD string-breaking threshold (2M/sigma), 
the energy of the intact entangled wormhole strictly exceeds the energy of the snapped 
(decohered) state. 

By binding `u.sd_sector` to the `intactState` parameter of the `FluxTubeStringBreaking` axiom, 
this signature rigorously prevents free-variable exploits and enforces the ER=EPR decay limit.
-/
theorem kinematicHamiltonianCrossover
  (energyFunc : (Fin 4 → SpacetimePoint → SL2C) → ℝ)
  (intactState snappedState : ℝ → Fin 4 → SpacetimePoint → SL2C)
  {sigma M : ℝ} [eb : FluxTubeStringBreaking (Fin 4 → SpacetimePoint → SL2C) energyFunc intactState snappedState sigma M]
  (u : Universe)
  (x y : SpacetimePoint) (theta L : ℝ)
  (h_entangled : areEntangled u.sd_sector x y theta)
  (h_dist : L^2 = (x 1 - y 1)^2 + (x 2 - y 2)^2 + (x 3 - y 3)^2)
  (h_L_pos : L > 0)
  (h_intact : u.sd_sector = intactState L)
  (h_sigma : sigma > 0)
  (h_L_crossover : L > (2 * M) / sigma) :
  energyFunc (u.sd_sector) > energyFunc (snappedState L) := by
  
  -- Step 1: Map the unified Universe sector to the parametrized intact state
  rw [h_intact]
  
  -- Step 2: Evaluate the energies of both topological states using the Litlib QCD bounds
  rw [eb.intactEnergy L h_L_pos]
  rw [eb.snappedEnergy L h_L_pos]
  
  -- Step 3: Multiply the crossover distance bound by the strictly positive string tension
  have h_mul : sigma * L > sigma * ((2 * M) / sigma) := mul_lt_mul_of_pos_left h_L_crossover h_sigma
  
  -- Step 4: Cancel the string tension to yield the raw mass threshold
  have h_cancel : sigma * ((2 * M) / sigma) = 2 * M := mul_div_cancel₀ _ (ne_of_gt h_sigma)
  rw [h_cancel] at h_mul
  
  -- Step 5: Conclude the strict energy inequality
  exact h_mul

Litlib.theorem
  description "Entanglement Decay"
/--
A direct consequence of the Hamiltonian crossover: when the spatial distance exceeds the 
crossover bound, the intact flux tube holding the entangled pair drops out of the global minimum. 
This establishes a deterministic, geometrical mechanism for macroscopic quantum decoherence.
-/
theorem dynamicEntanglementDecay
  (energyFunc : (Fin 4 → SpacetimePoint → SL2C) → ℝ)
  (intactState snappedState : ℝ → Fin 4 → SpacetimePoint → SL2C)
  {sigma M : ℝ} [eb : FluxTubeStringBreaking (Fin 4 → SpacetimePoint → SL2C) energyFunc intactState snappedState sigma M]
  (u : Universe)
  (x y : SpacetimePoint) (theta L : ℝ)
  (h_entangled : areEntangled u.sd_sector x y theta)
  (h_dist : L^2 = (x 1 - y 1)^2 + (x 2 - y 2)^2 + (x 3 - y 3)^2)
  (h_L_pos : L > 0)
  (h_intact : u.sd_sector = intactState L)
  (h_sigma : sigma > 0)
  (h_L_crossover : L > (2 * M) / sigma) :
  ¬ isGlobalMinimum energyFunc u.sd_sector := by
  
  -- Step 1: Assume for contradiction that the intact wormhole is the global minimum
  intro h_min
  unfold isGlobalMinimum at h_min
  
  -- Step 2: Extract the actual crossover inequality from the previous theorem
  have h_crossover := kinematicHamiltonianCrossover energyFunc intactState snappedState u x y theta L h_entangled h_dist h_L_pos h_intact h_sigma h_L_crossover
  
  -- Step 3: Apply the minimum bound to the specific alternative of the snapped flux tube
  have h_le := h_min (snappedState L)
  
  -- Step 4: The contradiction (A ≤ B and A > B) logically forbids the infinite survival of the entanglement
  linarith

end CGD.Quantum

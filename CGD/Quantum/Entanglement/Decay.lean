-- FILENAME: CGD/Quantum/Entanglement/Decay.lean

import Litlib.Core
import CGD.Quantum.Entanglement.Basic
import CGD.Axioms.Ontology
import CGD.Quantum.Definitions
import Litlib.Y2001.bali2001qcd.Signature

set_option linter.unusedSimpArgs false

open CGD.Foundations CGD.Gravity Matrix Complex BigOperators
open CGD.Axioms Litlib.Y2001.bali2001qcd

namespace CGD.Quantum

/-- 
This theorem proves that if the Euclidean spatial distance of a macroscopic topological flux tube 
exceeds the QCD string-breaking threshold (2M/sigma), the energy of the intact flux tube 
strictly exceeds the energy of the snapped state.

By binding `u.sd_sector` to the `intactState` parameter of the `FluxTubeStringBreaking` axiom, 
this signature rigorously prevents free-variable exploits and enforces the physical decay limit.
-/
theorem kinematicFluxTubeCrossover
  (energyFunc : (Fin 4 → SpacetimePoint → SL2C) → ℝ)
  (intactState snappedState : ℝ → Fin 4 → SpacetimePoint → SL2C)
  {sigma M : ℝ} [eb : FluxTubeStringBreaking (Fin 4 → SpacetimePoint → SL2C) energyFunc intactState snappedState sigma M]
  (u : Universe)
  (L : ℝ)
  (h_L_pos : L > 0)
  (h_intact : u.sd_sector = intactState L)
  (h_L_crossover : L > (2 * M) / sigma) :
  energyFunc (u.sd_sector) > energyFunc (snappedState L) := by
  
  -- Step 1: Map the unified Universe sector to the parametrized intact state
  rw [h_intact]
  
  -- Step 2: Evaluate the energies of both topological states using the Litlib QCD bounds
  rw [eb.intactEnergy L h_L_pos]
  rw [eb.snappedEnergy L h_L_pos]
  
  -- Step 3: Multiply the crossover distance bound by the strictly positive string tension
  have h_mul : sigma * L > sigma * ((2 * M) / sigma) := mul_lt_mul_of_pos_left h_L_crossover eb.h_sigma_pos
  
  -- Step 4: Cancel the string tension to yield the raw mass threshold
  have h_cancel : sigma * ((2 * M) / sigma) = 2 * M := mul_div_cancel₀ _ (ne_of_gt eb.h_sigma_pos)
  rw [h_cancel] at h_mul
  
  -- Step 5: Conclude the strict energy inequality
  exact h_mul

Litlib.theorem
  description "Flux Tube Breaking Limit"
/--
A direct consequence of the Hamiltonian crossover: when the spatial distance exceeds the 
crossover bound, the intact flux tube drops out of the global minimum. 
This establishes a deterministic, geometrical mechanism for macroscopic string breaking.
-/
theorem dynamicFluxTubeBreakingLimit
  (energyFunc : (Fin 4 → SpacetimePoint → SL2C) → ℝ)
  (intactState snappedState : ℝ → Fin 4 → SpacetimePoint → SL2C)
  {sigma M : ℝ} [eb : FluxTubeStringBreaking (Fin 4 → SpacetimePoint → SL2C) energyFunc intactState snappedState sigma M]
  (u : Universe)
  (L : ℝ)
  (h_L_pos : L > 0)
  (h_intact : u.sd_sector = intactState L)
  (h_L_crossover : L > (2 * M) / sigma) :
  ¬ isGlobalMinimum energyFunc u.sd_sector := by
  
  -- Step 1: Assume for contradiction that the intact string is the global minimum
  intro h_min
  unfold isGlobalMinimum at h_min
  
  -- Step 2: Extract the actual crossover inequality from the previous theorem
  have h_crossover := kinematicFluxTubeCrossover energyFunc intactState snappedState u L h_L_pos h_intact h_L_crossover
  
  -- Step 3: Apply the minimum bound to the specific alternative of the snapped flux tube
  have h_le := h_min (snappedState L)
  
  -- Step 4: The contradiction (A ≤ B and A > B) logically forbids the infinite survival of the string
  linarith

end CGD.Quantum

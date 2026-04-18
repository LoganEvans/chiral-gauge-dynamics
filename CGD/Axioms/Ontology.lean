-- FILENAME: CGD/Axioms/Ontology.lean

import CGD.Axioms.Spacetime
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CGD.Axioms

open CGD.Foundations

/-- 
A structurally sound Gauge Field.
By bundling the mapping, we rigorously guarantee that every physical field is:
1. Smooth (`ContDiff`) across the entire manifold.
2. Strictly physical (evaluating exclusively to SU(2) anti-Hermitian phase space).
This eradicates the need to lazily assume `h_smooth` and `h_su2` across dozens of theorems.
-/
structure GaugeField where
  val : Fin 4 → CGD.Axioms.SpacetimePoint → SL2C
  is_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (val mu x).val i j)
  is_su2 : ∀ mu x, isSu2 (val mu x).val

instance : CoeFun GaugeField (fun _ => Fin 4 → CGD.Axioms.SpacetimePoint → SL2C) where
  coe := GaugeField.val

/-- Rigorous Zero instance for the physical field. -/
instance : Zero GaugeField where
  zero := {
    val := fun _ _ => 0
    is_smooth := fun _ _ _ => contDiff_const
    is_su2 := fun _ _ => by
      constructor
      · change Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0
        simp
      · change Matrix.conjTranspose (0 : Matrix (Fin 2) (Fin 2) ℂ) = -(0 : Matrix (Fin 2) (Fin 2) ℂ)
        ext i j
        simp
  }

/-- 
The Core Ontology: The universe is a macroscopic, classical Spin(4, C) gauge connection.
Because Spin(4, C) is mathematically isomorphic to SL(2,C)_L x SL(2,C)_R, the universe 
natively and rigorously decomposes into two independent, structurally rigid chiral gauge fields.
-/
structure Universe where
  self_dual : GaugeField
  anti_self_dual  : GaugeField

/-- The trivial vacuum (A = 0) everywhere. -/
instance : Zero Universe where
  zero := { self_dual := 0, anti_self_dual := 0 }

/-- 
The unified 4x4 Dirac spin connection (ChiralM). 
Assembled natively from the independent Left and Right topological sectors without 
allowing unphysical off-diagonal mixing.
-/
noncomputable def Universe.embed (u : Universe) (mu : Fin 4) (x : CGD.Axioms.SpacetimePoint) : ChiralM := 
  embedSelfDual (u.self_dual mu x) + embedAntiSelfDual (u.anti_self_dual mu x)

end CGD.Axioms

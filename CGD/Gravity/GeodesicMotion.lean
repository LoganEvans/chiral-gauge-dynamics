-- FILENAME: CGD/Gravity/GeodesicMotion.lean

import Litlib.Core
import CGD.Gravity.StressEnergy
import CGD.Foundations.Calculus
import CGD.Axioms.Phenomenology
import Mathlib.Topology.Basic
import Litlib.Y1975.geroch1975motion.Signature
import Litlib.Y2003.nakahara2003geometry.Signature

set_option linter.unusedVariables false

open Complex Matrix CGD.Foundations BigOperators Classical
open CGD.Axioms

namespace CGD.Gravity

noncomputable def realMetricProxy (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ) : Fin 4 → Fin 4 → SpacetimePoint → ℝ := 
  fun m n p => (g m n p).re

noncomputable def realMetricInvProxy (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ) : Fin 4 → Fin 4 → SpacetimePoint → ℝ := 
  fun m n p => (CGD.Gravity.matrixInv4x4 (fun a b => g a b p) m n).re

noncomputable def realDerivProxy : Fin 4 → (SpacetimePoint → ℝ) → SpacetimePoint → ℝ := 
  fun m f p => (partialDeriv m (fun x => (f x : ℂ)) p).re

noncomputable def realChristoffelProxy (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ) : Fin 4 → Fin 4 → Fin 4 → SpacetimePoint → ℝ := 
  fun lam mu nu x => (1 / 2 : ℝ) * ∑ rho : Fin 4, realMetricInvProxy g lam rho x * (
    realDerivProxy mu (fun p => realMetricProxy g rho nu p) x +
    realDerivProxy nu (fun p => realMetricProxy g rho mu p) x -
    realDerivProxy rho (fun p => realMetricProxy g mu nu p) x
  )

def realTimelikeProxy (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ) (p : SpacetimePoint) (t : Fin 4 → ℝ) : Prop :=
  (∑ m : Fin 4, ∑ n : Fin 4, realMetricProxy g m n p * t m * t n) < 0

def realFutureTimelikeProxy (g : Fin 4 → Fin 4 → SpacetimePoint → ℂ) (p : SpacetimePoint) (t : Fin 4 → ℝ) : Prop :=
  realTimelikeProxy g p t ∧ t 0 > 0

end CGD.Gravity

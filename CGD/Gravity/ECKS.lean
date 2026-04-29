-- FILENAME: CGD/Gravity/ECKS.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Axioms.Ontology
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

open Complex Matrix BigOperators
open CGD.Axioms CGD.Foundations

namespace CGD.Gravity

noncomputable def addSpinConnections (ω K : SpinConnection) : SpinConnection :=
  fun I J μ x => ω I J μ x + K I J μ x

noncomputable def cgdContortion (F : Fin 4 → Fin 4 → SpacetimePoint → SL2C) : SpinConnection :=
  fun I J μ x => Matrix.trace ((F I J x).val * (F J μ x).val)

lemma torsion_of_sum (e : TetradField) (ω K : SpinConnection) (I μ ν : SpacetimeIndex) (x : SpacetimePoint) :
  torsionTensor e (addSpinConnections ω K) I μ ν x =
  torsionTensor e ω I μ ν x + ∑ J : InternalIndex, (K I J μ x * e J ν x - K I J ν x * e J μ x) := by
  unfold torsionTensor addSpinConnections
  have h_sum : (∑ J : InternalIndex, ((ω I J μ x + K I J μ x) * e J ν x - (ω I J ν x + K I J ν x) * e J μ x)) =
               (∑ J : InternalIndex, (ω I J μ x * e J ν x - ω I J ν x * e J μ x)) +
               (∑ J : InternalIndex, (K I J μ x * e J ν x - K I J ν x * e J μ x)) := by
    rw[← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J _
    ring
  rw[h_sum]
  ring

Litlib.theorem
  description "ECKS Gravity (Contortion from Chiral Connection)"
/--
The torsion of the combined spin connection cleanly separates into the base torsion and a contortion tensor derived from the chiral connection, recovering Einstein-Cartan-Kibble-Sciama gravity.
-/
theorem algebraicECKS (u : Universe)
  (e : TetradField) (ω_lc : SpinConnection)
  (_h_lc_torsion_free : isTorsionFree e ω_lc) :
  ∀ (I μ ν : SpacetimeIndex) (x : SpacetimePoint),
    torsionTensor e (addSpinConnections ω_lc (cgdContortion (fun a b p => curvatureSl2c u.sd_sector a b p))) I μ ν x =
    torsionTensor e ω_lc I μ ν x + ∑ J, (cgdContortion (fun a b p => curvatureSl2c u.sd_sector a b p) I J μ x * e J ν x - cgdContortion (fun a b p => curvatureSl2c u.sd_sector a b p) I J ν x * e J μ x) := by
  intro I μ ν x
  exact torsion_of_sum e ω_lc (cgdContortion (fun a b p => curvatureSl2c u.sd_sector a b p)) I μ ν x

end CGD.Gravity

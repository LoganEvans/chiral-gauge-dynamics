-- FILENAME: CGD/Axioms/MacroscopicVolume.lean

import Mathlib.Topology.Basic
import CGD.Axioms.Ontology
import CGD.Foundations.Spacetime
import CGD.Gravity.Geometry

open CGD.Foundations CGD.Math CGD.Gravity Set

namespace CGD.Axioms

/--
Axiom II: Macroscopic Existence (The "Non-Empty" Condition)
We constrain the physics by demanding that the emergent metric is
non-degenerate over an open topological bulk. By defining the bulk as
an `IsOpen` set, we safely allow the volume to mathematically crash to zero
on its boundaries (the Big Bang) or at topological punctures (derived matter defects),
without destroying the extended macroscopic spacetime.
-/
class MacroscopicVolume (u : Universe) (bulk : Set SpacetimePoint) : Prop where
  h_bulk_open : IsOpen bulk
  h_bulk_nonempty : Set.Nonempty bulk
  volume_exists : ∀ x ∈ bulk,
    (urbantkeMetric (fun μ ν => curvatureSl2c u.sd_sector μ ν x)).det ≠ 0

end CGD.Axioms

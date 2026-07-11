-- FILENAME: CGD/Gravity/ExactSolutions/Definitions.lean

import CGD.Axioms.PhysicalUniverse
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Gravity.Geometry

open CGD.Axioms CGD.Foundations CGD.Math CGD.Gravity

namespace CGD.Gravity.ExactSolutions

/--
A Physical Universe natively satisfies the kinematic reality conditions if and only if
the macroscopic Urbantke metric constructed from its self-dual curvature is strictly
real, strictly non-degenerate, and strictly Lorentzian (signature -+++ or +---)
everywhere within the topological bulk.

This mathematically enforces the historical Reality Conditions without requiring
any non-polynomial differential constraints.
-/
def SatisfiesRealityConditions (pu : PhysicalUniverse) : Prop :=
  ∀ x ∈ pu.bulk, isLorentzian (urbantkeMetric (fun μ ν => curvatureSl2c pu.toUniverse.sd_sector.val μ ν x))

end CGD.Gravity.ExactSolutions

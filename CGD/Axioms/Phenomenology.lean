-- FILENAME: CGD/Axioms/Phenomenology.lean

import CGD.Axioms.Ontology
import CGD.Foundations.Spacetime
import CGD.Foundations.Calculus
import CGD.Gravity.Geometry

open CGD.Foundations CGD.Gravity Complex Matrix

namespace CGD.Axioms

/-- 
Phenomenological Axiom: Macroscopic Volume.
Asserts that within a specified macroscopic bulk region, the emergent 
Urbantke metric of the self-dual sector is strictly non-degenerate. 
This mathematically differentiates extended 4D spacetime from lower-dimensional 
topological defects (such as flux tubes or entangled wormholes), where the metric 
natively collapses to zero.
-/
class MacroscopicVolume (u : Universe) (bulk : Set SpacetimePoint) : Prop where
  volume_exists : ∀ x ∈ bulk, (urbantkeMetric (fun μ ν => curvatureSl2c u.sd_sector μ ν x)).det ≠ 0

/-- 
Phenomenological Axiom: Macroscopic Time.
Asserts that within a specified macroscopic bulk region, the emergent 
Urbantke metric exhibits a strict Lorentzian signature. This breaks the 
static 4D Euclidean topological symmetry to establish a physical arrow of causality, 
which natively degenerates at the core of quantum topological defects.
-/
class MacroscopicTime (u : Universe) (bulk : Set SpacetimePoint) : Prop where
  time_exists : ∀ x ∈ bulk, isLorentzian (urbantkeMetric (fun μ ν => curvatureSl2c u.sd_sector μ ν x))

end CGD.Axioms

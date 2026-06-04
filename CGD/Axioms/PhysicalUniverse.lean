-- FILENAME: CGD/Axioms/PhysicalUniverse.lean

import CGD.Axioms.Ontology
import CGD.Axioms.MacroscopicVolume
import CGD.Axioms.UnimodularVacuum
import CGD.Foundations.Spacetime

open CGD.Foundations

namespace CGD.Axioms

/-- 
The Comprehensive Physical Reality.
Bundles the foundational ontology with the topological bulk and its required physical mixins. 
Matter is never inputted as an assumption; it exists entirely as the topological complement 
of the macroscopic bulk.
-/
structure PhysicalUniverse where
  toUniverse : Universe
  bulk : Set SpacetimePoint
  has_volume : MacroscopicVolume toUniverse bulk
  has_vacuum : UnimodularVacuum toUniverse bulk

end CGD.Axioms

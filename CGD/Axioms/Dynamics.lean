-- FILENAME: CGD/Axioms/Dynamics.lean

import CGD.Axioms.Ontology
import CGD.Foundations.Action

namespace CGD.Axioms

open CGD.Foundations

/--
The Principle of Least Action requires the path to be a stationary point (δS = 0).
Now secured against discontinuous trap-door exploits.
-/
def principleOfLeastAction (u : Universe) : Prop :=
  isStationaryPoint universeAction u isValidUniverseVariation

end CGD.Axioms

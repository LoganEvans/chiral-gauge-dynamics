-- FILENAME: CGD/Gravity/MetricSuperposition.lean

import CGD.Gravity.Geometry
import CGD.Axioms.Ontology

set_option linter.unusedVariables false

open Complex Matrix BigOperators
open CGD.Axioms CGD.Foundations

namespace CGD.Gravity

noncomputable def metricChiral (F : Fin 4 → Fin 4 → ChiralM) : Matrix (Fin 4) (Fin 4) Complex :=
  urbantkeMetric (fun mu nu => (chiralProject (F mu nu)).self_dual) +
  urbantkeMetric (fun mu nu => (chiralProject (F mu nu)).anti_self_dual)

/-- 🟡 KINEMATIC: Metric Superposition -/
theorem algebraicMetricSuperposition (u : Universe) (x : SpacetimePoint) :
  metricChiral (fun mu nu => curvature (fun m p => u.spin4c_connection m p) mu nu x) =
  urbantkeMetric (fun mu nu => (chiralProject (curvature (fun m p => u.spin4c_connection m p) mu nu x)).self_dual) +
  urbantkeMetric (fun mu nu => (chiralProject (curvature (fun m p => u.spin4c_connection m p) mu nu x)).anti_self_dual) :=
  rfl

end CGD.Gravity

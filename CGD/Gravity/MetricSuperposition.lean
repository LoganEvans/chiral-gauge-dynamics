-- FILENAME: CGD/Gravity/MetricSuperposition.lean

import CGD.Gravity.Geometry
import CGD.Axioms.Ontology

set_option linter.unusedVariables false

open Complex Matrix BigOperators
open CGD.Axioms CGD.Foundations

namespace CGD.Gravity

noncomputable def metricChiral (F : Fin 4 → Fin 4 → ChiralM) : Matrix (Fin 4) (Fin 4) Complex :=
  urbantkeMetric (fun mu nu => (chiralProject (F mu nu)).light) +
  urbantkeMetric (fun mu nu => (chiralProject (F mu nu)).dark)

/-- 🟡 KINEMATIC: Metric Superposition -/
theorem algebraicMetricSuperposition (u : Universe) (x : SpacetimePoint) :
  metricChiral (fun mu nu => curvature (fun m p => u.embed m p) mu nu x) =
  urbantkeMetric (fun mu nu => (chiralProject (curvature (fun m p => u.embed m p) mu nu x)).light) +
  urbantkeMetric (fun mu nu => (chiralProject (curvature (fun m p => u.embed m p) mu nu x)).dark) :=
  rfl

end CGD.Gravity

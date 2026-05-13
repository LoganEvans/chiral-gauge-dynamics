-- FILENAME: CGD/Foundations/Topology.lean

import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Instances.Matrix
import CGD.Foundations.GaugeGroup

namespace CGD.Foundations

abbrev S3 := { x : Fin 4 → ℝ // (x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 = 1 }

end CGD.Foundations

-- FILENAME: CGD/Foundations/Topology.lean

import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Instances.Matrix
import CGD.Foundations.GaugeGroup

namespace CGD.Foundations

class HasAsymptoticBoundary (Bulk BoundaryMap : Type*) [TopologicalSpace Bulk] [TopologicalSpace BoundaryMap] where
  boundaryMap : Bulk → BoundaryMap
  map_continuous : Continuous boundaryMap

class PreservesVacuum (Bulk BoundaryMap : Type*) [TopologicalSpace Bulk] [TopologicalSpace BoundaryMap] [Zero Bulk] [One BoundaryMap] [HasAsymptoticBoundary Bulk BoundaryMap] : Prop where
  boundary_vacuum : HasAsymptoticBoundary.boundaryMap (0 : Bulk) = (1 : BoundaryMap)

class HasTopologicalMeasure (BoundaryMap : Type*) where
  windingNumber : BoundaryMap → ℤ
  cartanMaurerIntegral : BoundaryMap → ℝ

class VacuumHasZeroMeasure (BoundaryMap : Type*) [One BoundaryMap] [HasTopologicalMeasure BoundaryMap] : Prop where
  integral_zero : HasTopologicalMeasure.cartanMaurerIntegral (1 : BoundaryMap) = (0 : ℝ)

abbrev S3 := { x : Fin 4 → ℝ // (x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 = 1 }

end CGD.Foundations

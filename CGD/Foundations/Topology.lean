-- FILENAME: CGD/Foundations/Topology.lean

import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic

namespace CGD.Foundations

class HasAsymptoticBoundary (Bulk Boundary : Type*) [TopologicalSpace Bulk] [TopologicalSpace Boundary] where
  boundaryMap : Bulk → Boundary
  map_continuous : Continuous boundaryMap

class PreservesVacuum (Bulk Boundary : Type*) [TopologicalSpace Bulk] [TopologicalSpace Boundary] [Zero Bulk] [Zero Boundary] [HasAsymptoticBoundary Bulk Boundary] : Prop where
  boundary_zero : HasAsymptoticBoundary.boundaryMap (0 : Bulk) = (0 : Boundary)

class HasTopologicalMeasure (Boundary : Type*) where
  windingNumber : Boundary → ℤ
  cartanMaurerIntegral : Boundary → ℝ

class VacuumHasZeroMeasure (Boundary : Type*) [Zero Boundary] [HasTopologicalMeasure Boundary] : Prop where
  integral_zero : HasTopologicalMeasure.cartanMaurerIntegral (0 : Boundary) = (0 : ℝ)
  
end CGD.Foundations

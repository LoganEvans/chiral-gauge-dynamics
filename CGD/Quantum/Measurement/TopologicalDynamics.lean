-- FILENAME: CGD/Quantum/Measurement/TopologicalDynamics.lean

import CGD.Foundations.Topology
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.NormNum

open CGD.Foundations

namespace CGD.Quantum.Measurement

/-- 
Using Smale's rigorous topological limit (Condition 3), we define a point x 
as flowing to a critical point c if the 1-parameter group of transformations 
(the flow) converges to c as time approaches infinity.
-/
def FlowsTo {M : Type*} [TopologicalSpace M] (phi : ℝ → M → M) (x : M) (c : M) : Prop :=
  ∃ (seq : ℕ → ℝ), Filter.Tendsto seq Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun n => phi (seq n) x) Filter.atTop (nhds c)

/-- The mathematical definition of a basin of attraction. -/
def BasinOfAttraction {M : Type*} [TopologicalSpace M] (phi : ℝ → M → M) (c : M) : Set M :=
  { x | FlowsTo phi x c }

/-- 
Pure geometry definition of a spherical cap boundary on S2.
A spherical cap bounded by angle theta from the North Pole (0,0,1) is exactly
the set of points whose z-coordinate is greater than or equal to cos(theta).
-/
def IsSphericalCap (basin : Set S2) (boundary_angle : ℝ) : Prop :=
  basin = { p : S2 | p.val 2 ≥ Real.cos boundary_angle }

/-- 
The macroscopic detector's aligned eigenstate, geometrically represented as the 
North Pole of the S2 Hopf base manifold (0, 0, 1).
-/
def detectorEigenstate : S2 := ⟨fun i => if i.val = 2 then 1 else 0, by
  change (if (0:ℕ) = 2 then (1:ℝ) else 0)^2 + (if (1:ℕ) = 2 then (1:ℝ) else 0)^2 + (if (2:ℕ) = 2 then (1:ℝ) else 0)^2 = 1
  norm_num⟩

/-- 
Rotates a point on S2 around the Z-axis (the detector axis) by an azimuthal angle phi. 
This strictly defines the U(1) gauge transformation natively on the base manifold.
-/
noncomputable def azimuthalRotate (p : S2) (phi : ℝ) : S2 :=
  let x := p.val 0
  let y := p.val 1
  let z := p.val 2
  let x' := x * Real.cos phi - y * Real.sin phi
  let y' := x * Real.sin phi + y * Real.cos phi
  let z' := z
  ⟨fun i => if i.val = 0 then x' else if i.val = 1 then y' else z', by
    change x'^2 + y'^2 + z'^2 = 1
    have h_orig : x^2 + y^2 + z^2 = 1 := p.property
    calc
      x'^2 + y'^2 + z'^2 = (x * Real.cos phi - y * Real.sin phi)^2 + (x * Real.sin phi + y * Real.cos phi)^2 + z^2 := by ring
      _ = x^2 * ((Real.cos phi)^2 + (Real.sin phi)^2) + y^2 * ((Real.sin phi)^2 + (Real.cos phi)^2) + z^2 := by ring
      _ = x^2 * 1 + y^2 * 1 + z^2 := by rw [Real.cos_sq_add_sin_sq, Real.sin_sq_add_cos_sq]
      _ = x^2 + y^2 + z^2 := by ring
      _ = 1 := h_orig⟩

end CGD.Quantum.Measurement

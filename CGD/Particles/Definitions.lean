-- FILENAME: CGD/Particles/Definitions.lean

import CGD.Foundations.Spacetime
import CGD.Gravity.Geometry
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import Mathlib.Data.Complex.Basic
import Litlib.Core
import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse
import Litlib.Y1983.witten1983current.Signature
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open CGD.Axioms CGD.Foundations CGD.Math Matrix Complex

namespace CGD.Particles

/--
The 4D Topological Soliton (Skyrmion) in the regular gauge.
Topologically localizes the gauge field.
Multiplied by Complex.I to map into the strictly anti-Hermitian su(2) Lie algebra.
Ontologically, this represents the spatial compactification of a 3D Cauchy slice (R3 U {infty} ~= S3)
rather than a 4D Euclidean tunneling event.
-/
noncomputable def topologicalSoliton (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  let r2 : ℂ := (x 0 : ℂ)^2 + (x 1 : ℂ)^2 + (x 2 : ℂ)^2 + (x 3 : ℂ)^2
  let D : ℂ := r2 + 1
  if mu = 0 then (Complex.I / D) • ((x 1 : ℂ) • sigma1 + (x 2 : ℂ) • sigma2 + (x 3 : ℂ) • sigma3)
  else if mu = 1 then (Complex.I / D) • (-(x 0 : ℂ) • sigma1 - (x 3 : ℂ) • sigma2 + (x 2 : ℂ) • sigma3)
  else if mu = 2 then (Complex.I / D) • ((x 3 : ℂ) • sigma1 - (x 0 : ℂ) • sigma2 - (x 1 : ℂ) • sigma3)
  else if mu = 3 then (Complex.I / D) • (-(x 2 : ℂ) • sigma1 + (x 1 : ℂ) • sigma2 - (x 0 : ℂ) • sigma3)
  else 0

noncomputable def homogeneousChaosAnsatz (mu : Fin 4) (x : SpacetimePoint) : SL2C :=
  if mu = 1 then (Complex.I * (x 1 : ℂ)) • sigma1
  else if mu = 2 then (Complex.I * (x 2 : ℂ)) • sigma2
  else 0

/--
Defines a single-color (Abelian) condensate where all components of the curvature tensor commute, constraining the field to a single U(1) Cartan subalgebra.
-/
def isSingleColor (F : Fin 4 -> Fin 4 -> SL2C) : Prop :=
  ∀ mu nu rho sigma, ⁅F mu nu, F rho sigma⁆ = 0

/--
A valid topological projection from the 4D Spacetime gauge field down to a 3D 
spatial boundary. Because the input `Sl2cGaugeField` is natively guaranteed 
to be smooth by the `PhysicalUniverse` axioms, this projection inherently 
guarantees the differentiability and SU(2) bounds of the output matrix field.
-/
structure FermionBoundaryProjection where
  map : Sl2cGaugeField → ((Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
  h_SU2 : ∀ A x, IsSU2 (map A x)
  h_smooth : ∀ A i j, Differentiable ℝ (fun x => map A x i j)

/--
Encapsulates the strict mathematical prerequisites for a macroscopic gauge field 
to constitute a topological fermion. By taking a `PhysicalUniverse` and a valid 
projection, it derives its smoothness and SU(2) nature natively from the 
universe's Anti-Self-Dual (Matter) sector, requiring only the assertion of 
the topological boundary conditions (Vacuum at infinity, Baryon Number = 1).
-/
structure IsFermionicState
  [MeasureTheory.MeasureSpace (Fin 3 → ℝ)]
  (pu : PhysicalUniverse)
  (proj : FermionBoundaryProjection) : Prop where
  h_vacuum : AsymptoticVacuumSU2 (proj.map pu.toUniverse.asd_sector)
  h_integrable : MeasureTheory.Integrable (BaryonNumberIntegrandSU2 (proj.map pu.toUniverse.asd_sector))
  h_degree_one : baryon_number_SU2 
                   (proj.map pu.toUniverse.asd_sector) 
                   (proj.h_SU2 pu.toUniverse.asd_sector) 
                   (proj.h_smooth pu.toUniverse.asd_sector) 
                   h_vacuum h_integrable = 1

/--
Encapsulates the mathematical operation of a 2π adiabatic spatial rotation 
on a topological state, required to evaluate quantum spin-statistics.
-/
structure IsFermionicRotation
  (path_parity : (ℝ → (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ) → ℕ)
  (U_0 : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
  (U_rot : ℝ → (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ) : Prop where
  h_rot_SU2 : ∀ t x, IsSU2 (U_rot t x)
  h_is_2pi_rot : ∀ t x, U_rot t x = U_0 (rotZ t x)
  h_fr_parity : path_parity U_rot = 1

end CGD.Particles

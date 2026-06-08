-- FILENAME: CGD/Particles/Summary.lean

import CGD.Axioms.PhysicalUniverse
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Spacetime
import CGD.Foundations.Topology
import CGD.Gravity.Geometry
import CGD.Particles.Definitions
import CGD.Particles.Color
import CGD.Particles.Confinement
import CGD.Particles.Mass
import CGD.Particles.TopologicalStability
import Mathlib.Data.Matrix.Basic
import Litlib.Y1975.belavin1975pseudoparticle.Signature
import Litlib.Y2003.nakahara2003geometry.Chapter10.Sec05_GaugeTheories

open Complex Matrix CGD.Foundations CGD.Axioms CGD.Gravity CGD.Particles

namespace CGD.Particles

/--
@Litlib.theorem

This theorem aggregates all particle and topological defect properties of the CGD framework 
into a single rigorous conjunction. It mathematically proves that for any well-defined 
physical universe, the following particle phenomena emerge directly from the topology:
1. Macroscopic spacetime volume geometrically forbids Abelian (single-color) states.
2. Single-color (Abelian) states geometrically degenerate to zero macroscopic volume.
3. Crushed 1D electric strings precisely reduce to the classical 1D confinement Hamiltonian.
4. Non-Abelian SU(2) topological defects strictly generate positive definite inertial mass (Mass Gap).
5. The fundamental BPST instanton is topologically protected and cannot continuously decay to the vacuum.
-/
theorem particlesSummary
  (pu : PhysicalUniverse) :

  -- Conjunct 1: Kinematic Multi-Color Requirement
  -- Proved by `kinematicMultiColorRequirement` in `CGD.Particles.Color`
  -- Demonstrates that a non-zero macroscopic spacetime volume strictly requires non-Abelian fields.
  (∀ (F : Fin 4 → Fin 4 → SL2C),
    (urbantkeMetric F).det ≠ 0 →
    ¬ isSingleColor F)
  ∧

  -- Conjunct 2: Kinematic Single-Color Degeneracy
  -- Proved by `kinematicSingleColorDegeneracy` in `CGD.Particles.Color`
  -- Demonstrates that the Urbantke metric determinant fundamentally requires non-commuting Lie algebra generators.
  (∀ (F : Fin 4 → Fin 4 → SL2C),
    isSingleColor F →
    (urbantkeMetric F).det = 0)
  ∧

  -- Conjunct 3: Kinematic String Confinement
  -- Proved by `kinematicStringConfinement` in `CGD.Particles.Confinement`
  -- Establishes that when the continuous electric field geometrically collapses into a 1D string, 
  -- the 3D densitized Hamiltonian precisely reduces to the exact 1D confinement Hamiltonian.
  (∀ (E B : Matrix (Fin 3) (Fin 3) ℂ) (E_z : ℂ),
    isCrushedString E E_z →
    ∃ (v : Fin 3 → ℂ), (∑ i : Fin 3, v i * v i = 1) ∧
      densitizedHamiltonian E B = (1 / 2 : ℂ) * E_z^2 + (1 / 2 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, B a b * B a b)
  ∧

  -- Conjunct 4: Topological Mass Gap
  -- Proved by `topologicalMassGap` in `CGD.Particles.Mass`
  -- By applying the positive definite trace property to the SU(2) curvature defect, we prove the 
  -- topological origin of strictly positive inertial mass.
  (∀ (x : SpacetimePoint),
    (∀ μ p, isSu2 (pu.toUniverse.asd_sector.val μ p).val) →
    (curvatureSl2c pu.toUniverse.asd_sector.val 1 2 x ≠ 0) →
    inertialMass pu x > 0)
  ∧

  -- Conjunct 5: Kinematic Topological Stability
  -- Proved by `kinematicTopologicalStability` in `CGD.Particles.TopologicalStability`
  -- Establishes the absolute topological stability of the instanton configuration via its Cartan-Maurer degree.
  (∀ (windingNumber : (S3 → SU2Group) → ℤ)
     (cartanMaurerIntegral : (S3 → SU2Group) → ℝ)
     [Litlib.Y2003.nakahara2003geometry.CartanMaurerTopology (S3 → SU2Group) Continuous windingNumber cartanMaurerIntegral]
     [Litlib.Y1975.belavin1975pseudoparticle.Eq8 S3 SU2Group Continuous windingNumber cartanMaurerIntegral],
     cartanMaurerIntegral 1 = 0 → ¬ isHomotopicConnection bpstInstanton 0) := by
  exact ⟨
    kinematicMultiColorRequirement,
    kinematicSingleColorDegeneracy,
    kinematicStringConfinement,
    topologicalMassGap pu,
    kinematicTopologicalStability
  ⟩

end CGD.Particles

-- FILENAME: CGD/Gravity/GeodesicMotion.lean

import Litlib.Core
import CGD.Gravity.Geometry
import CGD.Gravity.StressEnergy.Conservation
import CGD.Math.Calculus
import CGD.Foundations.Calculus
import CGD.Foundations.GaugeGroup
import Mathlib.Topology.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Litlib.Y2003.nakahara2003geometry.Signature
import Litlib.Y1984.urbantke1984integrability.Signature
import Litlib.Y1951.papapetrou1951spinning.Signature
import Litlib.Y1976.hehl1976general.Signature

open Complex Matrix CGD.Foundations CGD.Math BigOperators Classical
open Topology Litlib.Y1951.papapetrou1951spinning
open Litlib.Y1976.hehl1976general

namespace CGD.Gravity

-- TIER 1: PURE MATHEMATICS EXTRACT
-- Isolates the strict algebraic fact that an antisymmetric tensor contracted with a symmetric product natively vanishes.
@[litlib_track "Antisymmetric Contraction Vanishes"]
lemma antisymmetricContractionVanishes 
  (axial_torsion : Fin 4 → Fin 4 → Fin 4 → ℂ)
  (u : Fin 4 → ℂ)
  (h_axial_antisymm : ∀ a m n, axial_torsion a m n = - axial_torsion a n m) :
  ∀ a, ∑ m : Fin 4, ∑ n : Fin 4, axial_torsion a m n * u m * u n = 0 := by
  intro a
  let S := ∑ m : Fin 4, ∑ n : Fin 4, axial_torsion a m n * u m * u n
  have h1 : S = ∑ n : Fin 4, ∑ m : Fin 4, axial_torsion a m n * u m * u n := Finset.sum_comm
  have h2 : S = -S := by
    calc
      S = ∑ n : Fin 4, ∑ m : Fin 4, axial_torsion a m n * u m * u n := h1
      _ = ∑ n : Fin 4, ∑ m : Fin 4, (- axial_torsion a n m) * u m * u n := by
        apply Finset.sum_congr rfl
        intro n _
        apply Finset.sum_congr rfl
        intro m _
        rw [h_axial_antisymm a m n]
      _ = ∑ n : Fin 4, ∑ m : Fin 4, - (axial_torsion a n m * u n * u m) := by
        apply Finset.sum_congr rfl
        intro n _
        apply Finset.sum_congr rfl
        intro m _
        ring
      _ = - ∑ n : Fin 4, ∑ m : Fin 4, axial_torsion a n m * u n * u m := by
        simp_rw [Finset.sum_neg_distrib]
  have h3 : S + S = 0 := by
    calc
      S + S = S + (-S) := by exact congrArg (fun x => S + x) h2
      _ = 0 := by ring
  have h4 : (2 : ℂ) * S = 0 := by
    calc
      (2 : ℂ) * S = S + S := by ring
      _ = 0 := h3
  have h5 : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h4).resolve_left h5

-- TIER 1: PURE MATHEMATICS EXTRACT (Real Domain for strict Litlib compatibility)
@[litlib_track "Antisymmetric Contraction Vanishes (Real)"]
lemma antisymmetricContractionVanishesReal
  (axial_torsion : Fin 4 → Fin 4 → Fin 4 → ℝ)
  (u : Fin 4 → ℝ)
  (h_axial_antisymm : ∀ a m n, axial_torsion a m n = - axial_torsion a n m) :
  ∀ a, ∑ m : Fin 4, ∑ n : Fin 4, axial_torsion a m n * u m * u n = 0 := by
  intro a
  let S := ∑ m : Fin 4, ∑ n : Fin 4, axial_torsion a m n * u m * u n
  have h1 : S = ∑ n : Fin 4, ∑ m : Fin 4, axial_torsion a m n * u m * u n := Finset.sum_comm
  have h2 : S = -S := by
    calc
      S = ∑ n : Fin 4, ∑ m : Fin 4, axial_torsion a m n * u m * u n := h1
      _ = ∑ n : Fin 4, ∑ m : Fin 4, (- axial_torsion a n m) * u m * u n := by
        apply Finset.sum_congr rfl
        intro n _
        apply Finset.sum_congr rfl
        intro m _
        rw [h_axial_antisymm a m n]
      _ = ∑ n : Fin 4, ∑ m : Fin 4, - (axial_torsion a n m * u n * u m) := by
        apply Finset.sum_congr rfl
        intro n _
        apply Finset.sum_congr rfl
        intro m _
        ring
      _ = - ∑ n : Fin 4, ∑ m : Fin 4, axial_torsion a n m * u n * u m := by
        simp_rw [Finset.sum_neg_distrib]
  have h3 : S + S = 0 := by
    calc
      S + S = S + (-S) := by exact congrArg (fun x => S + x) h2
      _ = 0 := by ring
  have h4 : (2 : ℝ) * S = 0 := by
    calc
      (2 : ℝ) * S = S + S := by ring
      _ = 0 := h3
  have h5 : (2 : ℝ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h4).resolve_left h5

-- TIER 2: PHYSICAL EMERGENCE
-- Replaces the tautological Papapetrou dependency. Proves that an unpolarized test body mathematically decouples from
-- totally antisymmetric torsion (Axial Condensate), natively preserving symmetric GR geodesic trajectories in the Solar System.
@[litlib_track "Macroscopic Single-Pole Geodesic Motion"]
theorem macroscopicSinglePoleGeodesicMotion
  (Point : Type) [TopologicalSpace Point] [Nonempty Point]
  (γ : ℝ → Point)
  (u : ℝ → (Fin 4 → ℂ))
  (du : ℝ → (Fin 4 → ℂ))
  (full_connection : Fin 4 → Fin 4 → Fin 4 → Point → ℂ)
  (axial_torsion : Fin 4 → Fin 4 → Fin 4 → Point → ℂ)
  (chris : Fin 4 → Fin 4 → Fin 4 → Point → ℂ)
  -- The geometric split
  (h_connection_split : ∀ x a m n, full_connection a m n x = chris a m n x + axial_torsion a m n x)
  (h_axial_antisymm : ∀ x a m n, axial_torsion a m n x = - axial_torsion a n m x)
  -- The asymmetric equation of motion
  (h_autoparallel : ∀ s a, du s a + ∑ mu : Fin 4, ∑ nu : Fin 4, full_connection a mu nu (γ s) * u s mu * u s nu = 0) :
  -- Conclusion: The trajectory is driven entirely by the symmetric Christoffel symbols
  ∀ s alpha, du s alpha + ∑ mu : Fin 4, ∑ nu : Fin 4, chris alpha mu nu (γ s) * u s mu * u s nu = 0 := by
  intro s alpha
  have h_auto := h_autoparallel s alpha
  have h_expand : ∑ mu : Fin 4, ∑ nu : Fin 4, full_connection alpha mu nu (γ s) * u s mu * u s nu =
                  ∑ mu : Fin 4, ∑ nu : Fin 4, (chris alpha mu nu (γ s) + axial_torsion alpha mu nu (γ s)) * u s mu * u s nu := by
    apply Finset.sum_congr rfl
    intro mu _
    apply Finset.sum_congr rfl
    intro nu _
    rw [h_connection_split (γ s) alpha mu nu]
  
  have h_split : ∑ mu : Fin 4, ∑ nu : Fin 4, (chris alpha mu nu (γ s) + axial_torsion alpha mu nu (γ s)) * u s mu * u s nu =
                 (∑ mu : Fin 4, ∑ nu : Fin 4, chris alpha mu nu (γ s) * u s mu * u s nu) +
                 (∑ mu : Fin 4, ∑ nu : Fin 4, axial_torsion alpha mu nu (γ s) * u s mu * u s nu) := by
    calc
      ∑ mu : Fin 4, ∑ nu : Fin 4, (chris alpha mu nu (γ s) + axial_torsion alpha mu nu (γ s)) * u s mu * u s nu
      _ = ∑ mu : Fin 4, ∑ nu : Fin 4, (chris alpha mu nu (γ s) * u s mu * u s nu + axial_torsion alpha mu nu (γ s) * u s mu * u s nu) := by
        apply Finset.sum_congr rfl
        intro mu _
        apply Finset.sum_congr rfl
        intro nu _
        ring
      _ = ∑ mu : Fin 4, ((∑ nu : Fin 4, chris alpha mu nu (γ s) * u s mu * u s nu) + (∑ nu : Fin 4, axial_torsion alpha mu nu (γ s) * u s mu * u s nu)) := by
        apply Finset.sum_congr rfl
        intro mu _
        exact Finset.sum_add_distrib
      _ = (∑ mu : Fin 4, ∑ nu : Fin 4, chris alpha mu nu (γ s) * u s mu * u s nu) + (∑ mu : Fin 4, ∑ nu : Fin 4, axial_torsion alpha mu nu (γ s) * u s mu * u s nu) := by
        exact Finset.sum_add_distrib
        
  rw [h_expand, h_split] at h_auto
  
  have h_vanish := antisymmetricContractionVanishes (fun a m n => axial_torsion a m n (γ s)) (u s) (fun a m n => h_axial_antisymm (γ s) a m n) alpha
  rw [h_vanish] at h_auto
  
  have h_zero_add : (∑ mu : Fin 4, ∑ nu : Fin 4, chris alpha mu nu (γ s) * u s mu * u s nu) + 0 = 
                    ∑ mu : Fin 4, ∑ nu : Fin 4, chris alpha mu nu (γ s) * u s mu * u s nu := add_zero _
  rw [h_zero_add] at h_auto
  
  exact h_auto

-- TIER 2: LITLIB HORIZON BRIDGE
-- Proves that the exact Hehl (1976) Autoparallel trajectory (Eq 2.15) natively reduces 
-- to the symmetric Extremal trajectory (Eq 2.16) in the presence of totally antisymmetric torsion.
@[litlib_track "Hehl Autoparallel Reduces to Extremal for Macroscopic Bodies"]
theorem hehlMacroscopicDecoupling
  (full_connection : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
  (chris : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
  (axial_torsion : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
  (x : ℝ → Fin 4 → ℝ)
  (hx : ∀ k, Differentiable ℝ (fun s => x s k))
  (hx' : ∀ k, Differentiable ℝ (fun s => deriv (fun s'' => x s'' k) s))
  [hehl_autoparallel : Eq2_15 full_connection x hx hx']
  (h_connection_split : ∀ p a m n, full_connection p a m n = chris p a m n + axial_torsion p a m n)
  (h_axial_antisymm : ∀ p a m n, axial_torsion p a m n = - axial_torsion p a n m) :
  Eq2_16 chris x hx hx' := by
  constructor
  intro s k
  have h_auto := hehl_autoparallel.autoparallel s k
  
  have h_expand : ∑ i : Fin 4, ∑ j : Fin 4, full_connection (x s) k i j * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s =
                  ∑ i : Fin 4, ∑ j : Fin 4, (chris (x s) k i j + axial_torsion (x s) k i j) * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [h_connection_split (x s) k i j]
    
  have h_split : ∑ i : Fin 4, ∑ j : Fin 4, (chris (x s) k i j + axial_torsion (x s) k i j) * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s =
                 (∑ i : Fin 4, ∑ j : Fin 4, chris (x s) k i j * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s) +
                 (∑ i : Fin 4, ∑ j : Fin 4, axial_torsion (x s) k i j * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s) := by
    calc
      ∑ i : Fin 4, ∑ j : Fin 4, (chris (x s) k i j + axial_torsion (x s) k i j) * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s
      _ = ∑ i : Fin 4, ∑ j : Fin 4, (chris (x s) k i j * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s + axial_torsion (x s) k i j * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i : Fin 4, ((∑ j : Fin 4, chris (x s) k i j * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s) + (∑ j : Fin 4, axial_torsion (x s) k i j * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_add_distrib
      _ = (∑ i : Fin 4, ∑ j : Fin 4, chris (x s) k i j * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s) + (∑ i : Fin 4, ∑ j : Fin 4, axial_torsion (x s) k i j * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s) := by
        exact Finset.sum_add_distrib
        
  rw [h_expand, h_split] at h_auto
  
  have h_vanish := antisymmetricContractionVanishesReal (fun a m n => axial_torsion (x s) a m n) (fun m => deriv (fun s' => x s' m) s) (fun a m n => h_axial_antisymm (x s) a m n) k
  rw [h_vanish] at h_auto
  
  have h_zero_add : (∑ i : Fin 4, ∑ j : Fin 4, chris (x s) k i j * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s) + 0 = 
                    ∑ i : Fin 4, ∑ j : Fin 4, chris (x s) k i j * deriv (fun s' => x s' i) s * deriv (fun s' => x s' j) s := add_zero _
  rw [h_zero_add] at h_auto
  
  exact h_auto

end CGD.Gravity

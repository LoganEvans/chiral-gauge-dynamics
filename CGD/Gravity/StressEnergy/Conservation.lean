-- FILENAME: CGD/Gravity/StressEnergy/Conservation.lean

import Litlib.Core
import Litlib.Y2003.nakahara2003geometry.Signature
import Litlib.Y1984.urbantke1984integrability.Signature
import Mathlib.Data.Matrix.Basic

open Complex Matrix BigOperators Classical

namespace CGD.Gravity

-- TIER 1: PURE MATHEMATICS EXTRACT
-- Entirely divorces the mathematical derivation of contracted Bianchi conservation 
-- from the topological complexities of CGD bulk derivatives and specific matrix definitions.
@[litlib_track "Geometric Stress-Energy Conservation"]
theorem geometricStressEnergyConservation
  (Point : Type) [Nonempty Point]
  (isSmooth : (Point → ℂ) → Prop)
  (partialDeriv : Fin 4 → (Point → ℂ) → Point → ℂ)
  [general_bianchi : Litlib.Y2003.nakahara2003geometry.Theorem_ContractedBianchi Point (Fin 4) isSmooth partialDeriv]
  [symm_metric : Litlib.Y1984.urbantke1984integrability.Eq10_Symmetry]
  (g g_inv : Fin 4 → Fin 4 → Point → ℂ)
  (chris : Fin 4 → Fin 4 → Fin 4 → Point → ℂ)
  (ricci : Fin 4 → Fin 4 → Point → ℂ)
  (G : Fin 4 → Fin 4 → Point → ℂ)
  (F F_dual : Point → Fin 3 → Fin 4 → Fin 4 → ℂ)
  (epsilon3 : Fin 3 → Fin 3 → Fin 3 → ℂ)
  (h_metric_eq10 : ∀ x, 
    (∀ a mu nu, F x a mu nu = - F x a nu mu) ∧
    (∀ a mu nu, F_dual x a mu nu = - F_dual x a nu mu) ∧
    (∀ a b c, epsilon3 a b c = - epsilon3 b a c ∧ epsilon3 a b c = - epsilon3 a c b) ∧
    (∀ mu nu, g mu nu x =
      (-1 / 6 : ℂ) * ∑ a, ∑ b, ∑ c, ∑ alpha, ∑ beta, epsilon3 a c b * F x a mu alpha * F_dual x c alpha beta * F x b beta nu))
  (h_inv_symm : ∀ x i j, g_inv i j x = g_inv j i x)
  (h_inv_prop : ∀ x i j, ∑ k, g i k x * g_inv k j x = if i = j then 1 else 0)
  (h_chris_eq : ∀ x rho mu nu, chris rho mu nu x =
    (1/2 : ℂ) * ∑ sigma, g_inv rho sigma x * (
      partialDeriv mu (fun p => g sigma nu p) x +
      partialDeriv nu (fun p => g mu sigma p) x -
      partialDeriv sigma (fun p => g mu nu p) x))
  (h_ricci_eq : ∀ x mu nu, ricci mu nu x =
    ∑ rho, (partialDeriv rho (fun p => chris rho mu nu p) x -
          partialDeriv nu (fun p => chris rho mu rho p) x +
          ∑ lambda, (chris rho lambda rho x * chris lambda mu nu x -
                chris rho lambda nu x * chris lambda mu rho x)))
  (h_G_eq : ∀ x mu nu, G mu nu x = ricci mu nu x - (1/2:ℂ) * g mu nu x * (∑ alpha, ∑ beta, g_inv alpha beta x * ricci alpha beta x))
  (h_smooth_g : ∀ i j, isSmooth (fun p => g i j p))
  (h_smooth_g_inv : ∀ i j, isSmooth (fun p => g_inv i j p))
  (h_smooth_chris : ∀ rho mu nu, isSmooth (fun p => chris rho mu nu p)) :
  ∀ nu (x : Point),
    ∑ mu, ∑ alpha, g_inv mu alpha x * (
      partialDeriv alpha (fun p => G mu nu p) x -
      ∑ lambda, (chris lambda alpha mu x * G lambda nu x +
                 chris lambda alpha nu x * G mu lambda x)
    ) = 0 := by
  intro nu x
  let scalar := fun p => ∑ alpha, ∑ beta, g_inv alpha beta p * ricci alpha beta p
  have h_symm : ∀ p i j, g i j p = g j i p := by
    intro p i j
    rcases h_metric_eq10 p with ⟨hF_anti, hF_dual_anti, heps3_anti, hg_def⟩
    exact symm_metric.symmetricQuasimetric (F p) (F_dual p) epsilon3 (fun a b => g a b p) hF_anti hF_dual_anti heps3_anti hg_def i j
  exact general_bianchi.all_metrics_satisfy_bianchi g g_inv chris ricci scalar G h_symm h_inv_symm h_inv_prop h_chris_eq h_ricci_eq (fun _ => rfl) h_G_eq h_smooth_g h_smooth_g_inv h_smooth_chris nu x

end CGD.Gravity

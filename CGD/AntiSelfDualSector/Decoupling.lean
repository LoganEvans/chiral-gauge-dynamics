-- FILENAME: CGD/AntiSelfDualSector/Decoupling.lean

import CGD.Foundations.Action
import CGD.Foundations.Lagrangian
import CGD.Foundations.ChiralDecomposition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CGD.Axioms.Ontology

set_option linter.unusedVariables false

open CGD.Foundations Matrix BigOperators
open CGD.Axioms

namespace CGD.AntiSelfDualSector

lemma F_L_eq (u : Universe) (mu nu : Fin 4) (x : SpacetimePoint) :
  (chiralProject (curvature (fun m p => u.spin4c_connection m p) mu nu x)).self_dual = curvatureSl2c u.sd_sector mu nu x := by
  rw[curvature_embed_eq u mu nu x]
  exact chiral_project_self_dual_embed _ _

/-- An "Airlock" Lemma: Prevents Lean's unifier from expanding the massive AST of the curvature fields. -/
lemma action_vacuum_congr (F1 F2 : Fin 4 -> Fin 4 -> ChiralM)
  (h : ∀ mu nu, (chiralProject (F1 mu nu)).self_dual = (chiralProject (F2 mu nu)).self_dual) :
  actionVacuum F1 = actionVacuum F2 := by
  have h_trace : ∀ mu nu rho sigma,
    Matrix.trace (((chiralProject (F1 mu nu)).self_dual).val * ((chiralProject (F1 rho sigma)).self_dual).val) =
    Matrix.trace (((chiralProject (F2 mu nu)).self_dual).val * ((chiralProject (F2 rho sigma)).self_dual).val) := by
    intros mu nu rho sigma
    rw [h mu nu, h rho sigma]

  have h_sum : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    eta mu rho * eta nu sigma * Matrix.trace (((chiralProject (F1 mu nu)).self_dual).val * ((chiralProject (F1 rho sigma)).self_dual).val)) =
    (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    eta mu rho * eta nu sigma * Matrix.trace (((chiralProject (F2 mu nu)).self_dual).val * ((chiralProject (F2 rho sigma)).self_dual).val)) := by
    apply Finset.sum_congr rfl; intro mu _
    apply Finset.sum_congr rfl; intro nu _
    apply Finset.sum_congr rfl; intro rho _
    apply Finset.sum_congr rfl; intro sigma _
    rw[h_trace mu nu rho sigma]

  have h_eq1 : actionVacuum F1 = (-0.5 : ℂ) * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, eta mu rho * eta nu sigma * Matrix.trace (((chiralProject (F1 mu nu)).self_dual).val * ((chiralProject (F1 rho sigma)).self_dual).val)) := rfl
  have h_eq2 : actionVacuum F2 = (-0.5 : ℂ) * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, eta mu rho * eta nu sigma * Matrix.trace (((chiralProject (F2 mu nu)).self_dual).val * ((chiralProject (F2 rho sigma)).self_dual).val)) := rfl

  rw[h_eq1, h_eq2, h_sum]

/-- 🟡 KINEMATIC: AntiSelfDual Matter Decoupling -/
theorem algebraicAntiSelfDualSectorDecoupling (u : Universe)
  (A_R_alt : Su2GaugeField) (x : SpacetimePoint) :
  actionVacuum (fun mu nu => curvature (fun m p => u.spin4c_connection m p) mu nu x) =
  actionVacuum (fun mu nu => curvature (fun m p => embedSelfDual (u.sd_sector m p) + embedAntiSelfDual (A_R_alt m p)) mu nu x) := by

  let u_alt : Universe := { sd_sector := u.sd_sector, asd_sector := A_R_alt }
  let F_total := fun mu nu => curvature (fun m p => u.spin4c_connection m p) mu nu x
  let F_alt := fun mu nu => curvature (fun m p => u_alt.spin4c_connection m p) mu nu x

  change actionVacuum F_total = actionVacuum F_alt

  apply action_vacuum_congr F_total F_alt
  intro mu nu

  have h_L_eq_1 := F_L_eq u mu nu x
  have h_L_eq_2 := F_L_eq u_alt mu nu x

  have h3 : u_alt.sd_sector = u.sd_sector := rfl

  dsimp [F_total, F_alt]
  rw[h_L_eq_1, h_L_eq_2, h3]

end CGD.AntiSelfDualSector

-- FILENAME: CGD/DarkSector/Decoupling.lean

import CGD.Foundations.Action
import CGD.Foundations.Lagrangian
import CGD.Foundations.ChiralDecomposition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CGD.Axioms.Ontology

set_option linter.unusedVariables false

open CGD.Foundations Matrix BigOperators
open CGD.Axioms

namespace CGD.DarkSector

lemma F_L_eq (u : Universe) (mu nu : Fin 4) (x : SpacetimePoint) :
  (chiralProject (curvature (fun m p => u.embed m p) mu nu x)).light = curvatureSl2c u.light mu nu x := by
  rw[curvature_embed_eq u mu nu x]
  exact chiral_project_light_embed _ _

/-- An "Airlock" Lemma: Prevents Lean's unifier from expanding the massive AST of the curvature fields. -/
lemma action_vacuum_congr (F1 F2 : Fin 4 -> Fin 4 -> ChiralM)
  (h : ∀ mu nu, (chiralProject (F1 mu nu)).light = (chiralProject (F2 mu nu)).light) :
  actionVacuum F1 = actionVacuum F2 := by
  have h_trace : ∀ mu nu rho sigma,
    Matrix.trace (((chiralProject (F1 mu nu)).light).val * ((chiralProject (F1 rho sigma)).light).val) =
    Matrix.trace (((chiralProject (F2 mu nu)).light).val * ((chiralProject (F2 rho sigma)).light).val) := by
    intros mu nu rho sigma
    rw [h mu nu, h rho sigma]

  have h_sum : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    eta mu rho * eta nu sigma * Matrix.trace (((chiralProject (F1 mu nu)).light).val * ((chiralProject (F1 rho sigma)).light).val)) =
    (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4,
    eta mu rho * eta nu sigma * Matrix.trace (((chiralProject (F2 mu nu)).light).val * ((chiralProject (F2 rho sigma)).light).val)) := by
    apply Finset.sum_congr rfl; intro mu _
    apply Finset.sum_congr rfl; intro nu _
    apply Finset.sum_congr rfl; intro rho _
    apply Finset.sum_congr rfl; intro sigma _
    rw[h_trace mu nu rho sigma]

  have h_eq1 : actionVacuum F1 = (-0.5 : ℂ) * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, eta mu rho * eta nu sigma * Matrix.trace (((chiralProject (F1 mu nu)).light).val * ((chiralProject (F1 rho sigma)).light).val)) := rfl
  have h_eq2 : actionVacuum F2 = (-0.5 : ℂ) * (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ rho : Fin 4, ∑ sigma : Fin 4, eta mu rho * eta nu sigma * Matrix.trace (((chiralProject (F2 mu nu)).light).val * ((chiralProject (F2 rho sigma)).light).val)) := rfl

  rw[h_eq1, h_eq2, h_sum]

/-- 🟡 KINEMATIC: Dark Matter Decoupling -/
theorem algebraicDarkSectorDecoupling (u : Universe)
  (A_R_alt : Fin 4 -> SpacetimePoint -> SL2C) (x : SpacetimePoint)
  (h_su2 : ∀ mu p, isSu2 (A_R_alt mu p).val) :
  actionVacuum (fun mu nu => curvature (fun m p => u.embed m p) mu nu x) =
  actionVacuum (fun mu nu => curvature (fun m p => embedLight (u.light m p) + embedDark (A_R_alt m p)) mu nu x) := by

  let u_alt : Universe := { light := u.light, dark := A_R_alt }
  let F_total := fun mu nu => curvature (fun m p => u.embed m p) mu nu x
  let F_alt := fun mu nu => curvature (fun m p => u_alt.embed m p) mu nu x

  change actionVacuum F_total = actionVacuum F_alt

  apply action_vacuum_congr F_total F_alt
  intro mu nu

  have h_L_eq_1 := F_L_eq u mu nu x
  have h_L_eq_2 := F_L_eq u_alt mu nu x

  have h3 : u_alt.light = u.light := rfl

  dsimp [F_total, F_alt]
  rw[h_L_eq_1, h_L_eq_2, h3]

end CGD.DarkSector

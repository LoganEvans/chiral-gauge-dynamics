-- FILENAME: CGD/Gravity/ExactSolutions/MainTheorem.lean

import CGD.Gravity.ExactSolutions.CDJEvaluation
import CGD.Gravity.ExactSolutions.UrbantkeEvaluation

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

/--
This formally constructs an exact analytical non-Abelian $SU(2)$ gauge configuration 
that simultaneously satisfies the trace-free Capovilla CDJ constraint at the spatial 
origin, and produces a non-degenerate, strictly real, negative-determinant 
Lorentzian metric (det g < 0) at x = 0.

This mathematically proves that the foundational vacuum geometry of Chiral Gauge Dynamics 
is strictly non-vacuous.
-/
@[litlib_track "Exact Non-Abelian Lorentzian Macroscopic Witness"]
theorem dynamicExactLorentzianSolution :
  ∃ (u : Universe) (x : SpacetimePoint), 
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)) = 
    ((∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      epsilon4 μ ν ρ σ • (cgdAdjointCurvature u μ ν x * cgdAdjointCurvature u ρ σ x)).trace / 3) • 1 ∧
    isLorentzian (urbantkeMetric (fun m n => curvatureSl2c u.sd_sector m n x)) := by
  
  let A_L : Sl2cGaugeField := ⟨exactLorentzianField, exactLorentzian_smooth⟩
  let A_R : Sl2cGaugeField := ⟨fun _ _ => 0, fun _ _ _ => contDiff_const⟩
  let u : Universe := universeEquiv.symm (A_L, A_R)

  have h_sd_val : u.sd_sector.val = A_L.val := by
    have h_u_eq : universeEquiv u = (A_L, A_R) := Equiv.right_inv universeEquiv (A_L, A_R)
    exact congrArg Sl2cGaugeField.val (congrArg Prod.fst h_u_eq)

  use u, origin

  have h_cgd_adj : ∀ m n, cgdAdjointCurvature u m n origin = adj_F m n := by
    intro m n
    exact cgdAdjointCurvature_eval u m n h_sd_val

  have h_curv : ∀ m n, curvatureSl2c u.sd_sector m n origin = urb_F_origin m n := by
    intro m n
    have h_sd_full : u.sd_sector = ⟨exactLorentzianField, exactLorentzian_smooth⟩ := by
      apply Sl2cGaugeField.ext
      exact h_sd_val
    rw [h_sd_full, curvature_origin_eq m n]
    unfold urb_F_origin
    rw [c_F_mat_eval m n]

  constructor
  · simp only [h_cgd_adj]; exact CDJ_constraint_holds
  · have h_metric_eq : (fun m n => curvatureSl2c u.sd_sector m n origin) = urb_F_origin := by
      funext m n; exact h_curv m n
    rw [h_metric_eq]; exact metric_is_Lorentzian

end CGD.Gravity

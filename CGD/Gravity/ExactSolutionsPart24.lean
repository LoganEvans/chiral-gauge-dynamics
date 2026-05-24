-- FILENAME: CGD/Gravity/ExactSolutionsPart24.lean

import CGD.Gravity.ExactSolutionsPart23

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CGD.Foundations Matrix Complex BigOperators
open CGD.Axioms

namespace CGD.Gravity

noncomputable def adj_F (mu nu : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ :=
  extractAdjoint (F_origin_val mu nu)

lemma gauge_field_eq (A : Sl2cGaugeField) (v : Fin 4 → SpacetimePoint → SL2C)
  (smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (v mu x).val i j))
  (h : A.val = v) : A = { val := v, is_smooth := smooth } := by
  cases A with
  | mk A_val A_smooth =>
    dsimp at h
    subst h
    rfl

lemma F_origin_val_trace (mu nu : Fin 4) : Matrix.trace (F_origin_val mu nu) = 0 := by
  fin_cases mu <;> fin_cases nu <;> {
    unfold Matrix.trace Matrix.diag
    rw [Fin.sum_univ_two]
    dsimp [F_origin_val, sigmaX, sigmaY, sigmaZ, mkMat, Matrix.smul_apply, Matrix.neg_apply]
    ring
  }

lemma cgdAdjointCurvature_eval (u : Universe) (mu nu : Fin 4)
  (h_sd : u.sd_sector.val = exactLorentzianField) :
  cgdAdjointCurvature u mu nu origin = adj_F mu nu := by
  have h_def : cgdAdjointCurvature u mu nu origin = extractAdjoint (curvatureSl2c u.sd_sector mu nu origin).val := rfl
  rw [h_def]
  
  have h_sd_full : u.sd_sector = { val := exactLorentzianField, is_smooth := exactLorentzian_smooth } := 
    gauge_field_eq u.sd_sector exactLorentzianField exactLorentzian_smooth h_sd
  rw [h_sd_full]
  
  rw [curvature_origin_eq mu nu]
  rw [c_F_mat_eval mu nu]
  rw [toSl2c_val_eq (F_origin_val mu nu) (F_origin_val_trace mu nu)]
  rfl

end CGD.Gravity

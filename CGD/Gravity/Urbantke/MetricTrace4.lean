-- FILENAME: CGD/Gravity/Urbantke/MetricTrace4.lean

import CGD.Gravity.Urbantke.MetricTrace3

set_option linter.unusedSimpArgs false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

lemma sum_trace_expand (a b c : Fin 3) :
  (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2,
    tau a A B * eps2 B C * tau b C D * eps2 D E * tau c E F_idx * eps2 F_idx A) =
  Matrix.trace (TE a * TE b * TE c) := by
  dsimp [Matrix.trace, Matrix.diag, Matrix.mul_apply, TE]
  repeat rw [Fin.sum_univ_two]
  ring

lemma tau_eps_trace (a b c : Fin 3) :
  (∑ A : Fin 2, ∑ B : Fin 2, ∑ C : Fin 2, ∑ D : Fin 2, ∑ E : Fin 2, ∑ F_idx : Fin 2,
    tau a A B * eps2 B C * tau b C D * eps2 D E * tau c E F_idx * eps2 F_idx A) =
  -2 * I * epsilon3 a b c := by
  rw [sum_trace_expand]
  exact trace_TE a b c

end CGD.Gravity

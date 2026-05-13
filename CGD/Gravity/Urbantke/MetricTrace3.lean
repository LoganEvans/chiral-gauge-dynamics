-- FILENAME: CGD/Gravity/Urbantke/MetricTrace3.lean

import CGD.Gravity.Urbantke.MetricTrace2

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace CGD.Gravity

open Complex Matrix BigOperators CGD.Foundations Litlib.Y1991.capovilla1991pure

lemma trace_TE : ∀ (a b c : Fin 3), Matrix.trace (TE a * TE b * TE c) = -2 * I * epsilon3 a b c
| 0, 0, 0 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_000]; ring_nf; try simp only [Complex.I_sq]; try ring
| 0, 0, 1 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_001]; ring_nf; try simp only [Complex.I_sq]; try ring
| 0, 0, 2 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_002]; ring_nf; try simp only [Complex.I_sq]; try ring
| 0, 1, 0 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_010]; ring_nf; try simp only [Complex.I_sq]; try ring
| 0, 1, 1 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_011]; ring_nf; try simp only [Complex.I_sq]; try ring
| 0, 1, 2 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_012]; ring_nf; try simp only [Complex.I_sq]; try ring
| 0, 2, 0 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_020]; ring_nf; try simp only [Complex.I_sq]; try ring
| 0, 2, 1 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_021]; ring_nf; try simp only [Complex.I_sq]; try ring
| 0, 2, 2 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_022]; ring_nf; try simp only [Complex.I_sq]; try ring
| 1, 0, 0 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_100]; ring_nf; try simp only [Complex.I_sq]; try ring
| 1, 0, 1 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_101]; ring_nf; try simp only [Complex.I_sq]; try ring
| 1, 0, 2 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_102]; ring_nf; try simp only [Complex.I_sq]; try ring
| 1, 1, 0 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_110]; ring_nf; try simp only [Complex.I_sq]; try ring
| 1, 1, 1 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_111]; ring_nf; try simp only [Complex.I_sq]; try ring
| 1, 1, 2 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_112]; ring_nf; try simp only [Complex.I_sq]; try ring
| 1, 2, 0 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_120]; ring_nf; try simp only [Complex.I_sq]; try ring
| 1, 2, 1 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_121]; ring_nf; try simp only [Complex.I_sq]; try ring
| 1, 2, 2 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_122]; ring_nf; try simp only [Complex.I_sq]; try ring
| 2, 0, 0 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_200]; ring_nf; try simp only [Complex.I_sq]; try ring
| 2, 0, 1 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_201]; ring_nf; try simp only [Complex.I_sq]; try ring
| 2, 0, 2 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_202]; ring_nf; try simp only [Complex.I_sq]; try ring
| 2, 1, 0 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_210]; ring_nf; try simp only [Complex.I_sq]; try ring
| 2, 1, 1 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_211]; ring_nf; try simp only [Complex.I_sq]; try ring
| 2, 1, 2 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_212]; ring_nf; try simp only [Complex.I_sq]; try ring
| 2, 2, 0 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_220]; ring_nf; try simp only [Complex.I_sq]; try ring
| 2, 2, 1 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_221]; ring_nf; try simp only [Complex.I_sq]; try ring
| 2, 2, 2 => by rw [trace_mul3_fin2]; simp only [TE_0_eq, TE_1_eq, TE_2_eq, mkMat_00, mkMat_01, mkMat_10, mkMat_11, eps3_222]; ring_nf; try simp only [Complex.I_sq]; try ring

end CGD.Gravity

-- FILENAME: CGD/Litlib/Y1956/utiyama1956invariant/Signature.lean

import Litlib.Core
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import CGD.Foundations.GaugeGroup

namespace CGD.Litlib.Y1956.utiyama1956invariant

open CGD.Foundations

Litlib.reference AppendixI_InvariantBilinearForm
  bibtex "utiyama1956invariant"
  title "Invariant theoretical interpretation of interaction"
  authors ["Utiyama, Ryoyu"]
  journal "Physical Review"
  volume "101"
  issue "5"
  pages "1597"
  year "1956"
  publisher "APS"
class AppendixI_InvariantBilinearForm where
  /-- 
  Utiyama 1956, Appendix I. 
  Constructs the uniquely non-degenerate invariant metric (the Killing form) 
  for the group generators. For the Chiral Lie algebra, any complex bilinear form 
  that is invariant under the Adjoint representation (conjugation) is strictly 
  proportional to the matrix trace. 
  -/
  spans : ∀ (B : ChiralM → ChiralM → ℂ),
    (∀ c x y, B (c • x) y = c * B x y) →
    (∀ x1 x2 y, B (x1 + x2) y = B x1 y + B x2 y) →
    (∀ x y1 y2, B x (y1 + y2) = B x y1 + B x y2) →
    (∀ x y (U : ChiralMˣ), B ((U : ChiralM) * x * (↑U⁻¹ : ChiralM)) ((U : ChiralM) * y * (↑U⁻¹ : ChiralM)) = B x y) →
    ∃ (k : ℂ), ∀ x y, B x y = k * Matrix.trace (x * y)

end CGD.Litlib.Y1956.utiyama1956invariant

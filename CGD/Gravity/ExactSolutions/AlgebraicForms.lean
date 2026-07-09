-- FILENAME: CGD/Gravity/ExactSolutions/AlgebraicForms.lean

import CGD.Axioms.PhysicalUniverse
import CGD.Foundations.Calculus

open CGD.Axioms CGD.Foundations Complex Matrix

namespace CGD.Gravity.ExactSolutions

/--
Type O (Isotropic / FLRW Cosmological Vacuum)
Algebraic Form: A_0 = 0, A_j(t) = a(t) σ_j
All principal null directions are degenerate. 
The scale factor `a(t)` must be strictly real and non-static to ensure a non-degenerate Lorentzian metric.
Acts as the volume-generating Axial Condensate for all other Petrov types.
-/
def IsTypeOForm (pu : PhysicalUniverse) : Prop :=
  ∃ a : ℝ → ℂ, ∀ x : SpacetimePoint,
    (a (x 0)).im = 0 ∧ 
    (fderiv ℝ a (x 0) 1).im = 0 ∧
    a (x 0) ≠ 0 ∧ 
    fderiv ℝ a (x 0) 1 ≠ 0 ∧
    pu.toUniverse.sd_sector.val 0 x = 0 ∧
    pu.toUniverse.sd_sector.val 1 x = toSl2c (a (x 0) • sigma1.val) ∧
    pu.toUniverse.sd_sector.val 2 x = toSl2c (a (x 0) • sigma2.val) ∧
    pu.toUniverse.sd_sector.val 3 x = toSl2c (a (x 0) • sigma3.val)

/--
Type N (Nilpotent / Gravitational pp-waves)
Algebraic Form: A_μ = A^(vac)_μ + f(t-z) k_μ (σ_x + iσ_y)
Embedded over the Type O axial condensate to prevent macroscopic volume degeneracy.
The wave strictly propagates along the null vector k = (1, 0, 0, -1).
-/
def IsTypeNForm (pu : PhysicalUniverse) : Prop :=
  ∃ a : ℝ → ℂ, ∃ f : ℝ → ℝ, ∀ x : SpacetimePoint,
    (a (x 0)).im = 0 ∧ (fderiv ℝ a (x 0) 1).im = 0 ∧ a (x 0) ≠ 0 ∧ fderiv ℝ a (x 0) 1 ≠ 0 ∧
    pu.toUniverse.sd_sector.val 0 x = toSl2c ((f (x 0 - x 3) : ℂ) • (sigma1.val + Complex.I • sigma2.val)) ∧
    pu.toUniverse.sd_sector.val 1 x = toSl2c (a (x 0) • sigma1.val) ∧
    pu.toUniverse.sd_sector.val 2 x = toSl2c (a (x 0) • sigma2.val) ∧
    pu.toUniverse.sd_sector.val 3 x = toSl2c (a (x 0) • sigma3.val - (f (x 0 - x 3) : ℂ) • (sigma1.val + Complex.I • sigma2.val))

/--
Type D (Kerr-Schild / Isolated Mass Defect / Black Hole)
Algebraic Form: A_μ = A^(vac)_μ + Phi(x) l_μ (n_j σ_j)
Embedded over the Type O axial condensate to prevent macroscopic volume degeneracy.
-/
def IsTypeDForm (pu : PhysicalUniverse) : Prop :=
  ∃ a : ℝ → ℂ, ∃ Phi : SpacetimePoint → ℂ, ∃ l : Fin 4 → ℂ, ∃ n : Fin 3 → ℂ, ∀ x : SpacetimePoint,
    (a (x 0)).im = 0 ∧ (fderiv ℝ a (x 0) 1).im = 0 ∧ a (x 0) ≠ 0 ∧ fderiv ℝ a (x 0) 1 ≠ 0 ∧
    pu.toUniverse.sd_sector.val 0 x = toSl2c ((Phi x * l 0) • (n 0 • sigma1.val + n 1 • sigma2.val + n 2 • sigma3.val)) ∧
    pu.toUniverse.sd_sector.val 1 x = toSl2c (a (x 0) • sigma1.val + (Phi x * l 1) • (n 0 • sigma1.val + n 1 • sigma2.val + n 2 • sigma3.val)) ∧
    pu.toUniverse.sd_sector.val 2 x = toSl2c (a (x 0) • sigma2.val + (Phi x * l 2) • (n 0 • sigma1.val + n 1 • sigma2.val + n 2 • sigma3.val)) ∧
    pu.toUniverse.sd_sector.val 3 x = toSl2c (a (x 0) • sigma3.val + (Phi x * l 3) • (n 0 • sigma1.val + n 1 • sigma2.val + n 2 • sigma3.val))

/--
Type III (Longitudinal Field)
Algebraic Form: A_μ = A^(vac)_μ + f(t-z) v_μ (σ_x + iσ_y) + g(t-z) w_μ σ_z
Embedded over the Type O axial condensate to prevent macroscopic volume degeneracy.
-/
def IsTypeIIIForm (pu : PhysicalUniverse) : Prop :=
  ∃ a f g : ℝ → ℂ, ∃ v w : Fin 4 → ℂ, ∀ x : SpacetimePoint,
    (a (x 0)).im = 0 ∧ (fderiv ℝ a (x 0) 1).im = 0 ∧ a (x 0) ≠ 0 ∧ fderiv ℝ a (x 0) 1 ≠ 0 ∧
    pu.toUniverse.sd_sector.val 0 x = toSl2c ((f (x 0 - x 3) * v 0) • (sigma1.val + Complex.I • sigma2.val) + (g (x 0 - x 3) * w 0) • sigma3.val) ∧
    pu.toUniverse.sd_sector.val 1 x = toSl2c (a (x 0) • sigma1.val + (f (x 0 - x 3) * v 1) • (sigma1.val + Complex.I • sigma2.val) + (g (x 0 - x 3) * w 1) • sigma3.val) ∧
    pu.toUniverse.sd_sector.val 2 x = toSl2c (a (x 0) • sigma2.val + (f (x 0 - x 3) * v 2) • (sigma1.val + Complex.I • sigma2.val) + (g (x 0 - x 3) * w 2) • sigma3.val) ∧
    pu.toUniverse.sd_sector.val 3 x = toSl2c (a (x 0) • sigma3.val + (f (x 0 - x 3) * v 3) • (sigma1.val + Complex.I • sigma2.val) + (g (x 0 - x 3) * w 3) • sigma3.val)

/--
Type II (Radiating Mass / Liénard-Wiechert)
Algebraic Form: A_μ = A^(vac)_μ + Phi(x) l_μ (n_j σ_j) + f(t-z) v_μ (σ_x + iσ_y)
Embedded over the Type O axial condensate to prevent macroscopic volume degeneracy.
-/
def IsTypeIIForm (pu : PhysicalUniverse) : Prop :=
  ∃ a : ℝ → ℂ, ∃ Phi : SpacetimePoint → ℂ, ∃ f : ℝ → ℂ, ∃ v l : Fin 4 → ℂ, ∃ n : Fin 3 → ℂ, ∀ x : SpacetimePoint,
    (a (x 0)).im = 0 ∧ (fderiv ℝ a (x 0) 1).im = 0 ∧ a (x 0) ≠ 0 ∧ fderiv ℝ a (x 0) 1 ≠ 0 ∧
    pu.toUniverse.sd_sector.val 0 x = toSl2c ((Phi x * l 0) • (n 0 • sigma1.val + n 1 • sigma2.val + n 2 • sigma3.val) + (f (x 0 - x 3) * v 0) • (sigma1.val + Complex.I • sigma2.val)) ∧
    pu.toUniverse.sd_sector.val 1 x = toSl2c (a (x 0) • sigma1.val + (Phi x * l 1) • (n 0 • sigma1.val + n 1 • sigma2.val + n 2 • sigma3.val) + (f (x 0 - x 3) * v 1) • (sigma1.val + Complex.I • sigma2.val)) ∧
    pu.toUniverse.sd_sector.val 2 x = toSl2c (a (x 0) • sigma2.val + (Phi x * l 2) • (n 0 • sigma1.val + n 1 • sigma2.val + n 2 • sigma3.val) + (f (x 0 - x 3) * v 2) • (sigma1.val + Complex.I • sigma2.val)) ∧
    pu.toUniverse.sd_sector.val 3 x = toSl2c (a (x 0) • sigma3.val + (Phi x * l 3) • (n 0 • sigma1.val + n 1 • sigma2.val + n 2 • sigma3.val) + (f (x 0 - x 3) * v 3) • (sigma1.val + Complex.I • sigma2.val))

/--
Type I (Algebraically General / Binary Merger)
No overlapping roots. Contains zero algebraic symmetry. 
Asserts the existence of an unconstrained configuration to be verified dynamically via oracle.
-/
def IsTypeIForm (pu : PhysicalUniverse) : Prop :=
  ∃ A : Fin 4 → SpacetimePoint → SL2C, ∀ x : SpacetimePoint, ∀ μ : Fin 4,
    pu.toUniverse.sd_sector.val μ x = A μ x

end CGD.Gravity.ExactSolutions

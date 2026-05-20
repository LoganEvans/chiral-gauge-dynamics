-- FILENAME: CGD/Gravity/MacroscopicVacuum/Differential.lean

import CGD.Foundations.Bianchi
import CGD.Gravity.MacroscopicVacuum.Spinors

namespace CGD.Gravity

-- ==========================================
-- PART 1: PRIMITIVE DEFINITIONS
-- ==========================================

/-- The self-dual spin connection is natively the background SU(2) gauge field. -/
noncomputable def cgd_omega (u : CGD.Axioms.Universe) (x : CGD.Foundations.SpacetimePoint) (μ : Fin 4) (A B : Fin 2) : ℂ :=
  (u.sd_sector μ x).val A B

/-- The exact partial derivative expansion of the derived soldering 2-form. -/
noncomputable def cgd_dSigma (e : TetradField) (x : CGD.Foundations.SpacetimePoint) (μ ν ρ : Fin 4) (A B : Fin 2) : ℂ :=
  CGD.Foundations.partialDeriv ρ (fun p => cgd_Sigma e p μ ν A B) x

/-- The inverse Levi-Civita spinor metric (indices up). -/
def cgd_eps2_up (A B : Fin 2) : ℂ := cgd_eps2_down A B

-- ==========================================
-- PART 2: COVARIANT EXTERIOR DERIVATIVE (DΣ)
-- ==========================================

/-- Raises the first index of the spin connection using the inverse spinor metric. -/
noncomputable def cgd_omega_up (u : CGD.Axioms.Universe) (x : CGD.Foundations.SpacetimePoint) (μ : Fin 4) (A C : Fin 2) : ℂ :=
  sumFin2 fun E => cgd_eps2_up A E * cgd_omega u x μ E C

/-- 
The components of the covariant exterior derivative of the soldering form.
D_ρ \Sigma_μν = \partial_ρ \Sigma_μν + \omega_ρ \wedge \Sigma_μν
-/
noncomputable def cgd_covariant_deriv_Sigma_term 
  (u : CGD.Axioms.Universe) (e : TetradField) (x : CGD.Foundations.SpacetimePoint) 
  (μ ν ρ : Fin 4) (A B : Fin 2) : ℂ :=
  cgd_dSigma e x μ ν ρ A B + 
  sumFin2 fun C => cgd_omega_up u x μ A C * cgd_Sigma e x ν ρ B C + cgd_omega_up u x μ B C * cgd_Sigma e x ν ρ A C

/-- 
The fully antisymmetrized exterior covariant derivative representing d\Sigma + \omega \wedge \Sigma.
-/
noncomputable def cgd_D_Sigma_wedge 
  (u : CGD.Axioms.Universe) (e : TetradField) (x : CGD.Foundations.SpacetimePoint) 
  (μ ν ρ : Fin 4) (A B : Fin 2) : ℂ :=
  let term := cgd_covariant_deriv_Sigma_term u e x;
  term μ ν ρ A B + term ν ρ μ A B + term ρ μ ν A B - 
  term ν μ ρ A B - term μ ρ ν A B - term ρ ν μ A B

-- ==========================================
-- PART 3: THE SPINOR BIANCHI IDENTITY (DR = 0)
-- ==========================================

/-- 
Projects the matrix-level covariant derivative of the curvature tensor 
down into the symmetric Capovilla spinor representation.
-/
noncomputable def cgd_D_R_wedge 
  (u : CGD.Axioms.Universe) (x : CGD.Foundations.SpacetimePoint) 
  (μ ν ρ : Fin 4) (A B : Fin 2) : ℂ :=
  let D_F := fun m n r => CGD.Foundations.covariantDeriv (fun i p => u.sd_sector i p) m n r x;
  sumFin2 fun C => (D_F ρ μ ν + D_F μ ν ρ + D_F ν ρ μ).val A C * cgd_eps2_down C B

/--
The Spinor Bianchi Identity.
Rigorously evaluates to zero natively from the N-dimensional Clairaut's theorem 
and the Lie bracket Jacobi identity, without invoking unproven geometric assumptions.
-/
theorem cgd_bianchi_identity_R 
  [clairaut : Litlib.Y1976.rudin1976principles.ClairautTheoremNDimensional]
  (u : CGD.Axioms.Universe) (x : CGD.Foundations.SpacetimePoint) (μ ν ρ : Fin 4) (A B : Fin 2)
  (h_diff_dmu_Anu : ∀ i j, DifferentiableAt ℝ (fun p => (CGD.Foundations.partialDerivSl2c μ (u.sd_sector ν) p).val i j) x)
  (h_diff_dnu_Amu : ∀ i j, DifferentiableAt ℝ (fun p => (CGD.Foundations.partialDerivSl2c ν (u.sd_sector μ) p).val i j) x)
  (h_diff_dnu_Arho : ∀ i j, DifferentiableAt ℝ (fun p => (CGD.Foundations.partialDerivSl2c ν (u.sd_sector ρ) p).val i j) x)
  (h_diff_drho_Anu : ∀ i j, DifferentiableAt ℝ (fun p => (CGD.Foundations.partialDerivSl2c ρ (u.sd_sector ν) p).val i j) x)
  (h_diff_drho_Amu : ∀ i j, DifferentiableAt ℝ (fun p => (CGD.Foundations.partialDerivSl2c ρ (u.sd_sector μ) p).val i j) x)
  (h_diff_dmu_Arho : ∀ i j, DifferentiableAt ℝ (fun p => (CGD.Foundations.partialDerivSl2c μ (u.sd_sector ρ) p).val i j) x)
  (h_diff_bracket_munu : ∀ i j, DifferentiableAt ℝ (fun p => ⁅u.sd_sector μ p, u.sd_sector ν p⁆.val i j) x)
  (h_diff_bracket_nurho : ∀ i j, DifferentiableAt ℝ (fun p => ⁅u.sd_sector ν p, u.sd_sector ρ p⁆.val i j) x)
  (h_diff_bracket_rhomu : ∀ i j, DifferentiableAt ℝ (fun p => ⁅u.sd_sector ρ p, u.sd_sector μ p⁆.val i j) x)
  (h_diffA : ∀ σ p i j, DifferentiableAt ℝ (fun p' => (u.sd_sector σ p').val i j) p)
  (h_smooth_re : ∀ σ i j, ContDiffOn ℝ 2 (fun p => ((u.sd_sector σ p).val i j).re) Set.univ)
  (h_smooth_im : ∀ σ i j, ContDiffOn ℝ 2 (fun p => ((u.sd_sector σ p).val i j).im) Set.univ)
  (h_diff_fderiv_re : ∀ σ i j, DifferentiableAt ℝ (fderiv ℝ (fun p => ((u.sd_sector σ p).val i j).re)) x)
  (h_diff_fderiv_im : ∀ σ i j, DifferentiableAt ℝ (fderiv ℝ (fun p => ((u.sd_sector σ p).val i j).im)) x) :
  cgd_D_R_wedge u x μ ν ρ A B = 0 := by
  
  dsimp only [cgd_D_R_wedge]
  
  have h_bianchi := CGD.Foundations.cgd_bianchi_identity (fun i p => u.sd_sector i p) ρ μ ν x
    h_diff_dmu_Anu h_diff_dnu_Amu h_diff_dnu_Arho h_diff_drho_Anu h_diff_drho_Amu h_diff_dmu_Arho
    h_diff_bracket_munu h_diff_bracket_nurho h_diff_bracket_rhomu
    h_diffA h_smooth_re h_smooth_im h_diff_fderiv_re h_diff_fderiv_im
    
  have h_val_zero : (0 : CGD.Foundations.SL2C).val = 0 := rfl
  
  have h_bianchi_val : (CGD.Foundations.covariantDeriv (fun i p => u.sd_sector i p) ρ μ ν x +
      CGD.Foundations.covariantDeriv (fun i p => u.sd_sector i p) μ ν ρ x +
      CGD.Foundations.covariantDeriv (fun i p => u.sd_sector i p) ν ρ μ x).val = 0 := by
    rw [h_bianchi]
    rfl
    
  have h_inner : (fun C => (CGD.Foundations.covariantDeriv (fun i p => u.sd_sector i p) ρ μ ν x +
      CGD.Foundations.covariantDeriv (fun i p => u.sd_sector i p) μ ν ρ x +
      CGD.Foundations.covariantDeriv (fun i p => u.sd_sector i p) ν ρ μ x).val A C * cgd_eps2_down C B) = fun C => 0 := by
    ext C
    rw [h_bianchi_val]
    simp
    
  rw [h_inner]
  unfold sumFin2
  ring

end CGD.Gravity

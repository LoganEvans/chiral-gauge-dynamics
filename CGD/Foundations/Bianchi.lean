-- FILENAME: CGD/Foundations/Bianchi.lean

import Litlib.Core
import CGD.Axioms.Ontology
import CGD.Foundations.Math
import CGD.Foundations.Calculus
import CGD.Foundations.Charge
import CGD.Foundations.TensorCalculus.DifferentialRules
import Mathlib.Analysis.Calculus.FDeriv.Add

namespace CGD.Foundations

set_option linter.unusedSimpArgs false

/--
Rigorous differential expansion of the covariant derivative acting on the gauge curvature tensor.
This applies the previously proven addition, subtraction, and bracket derivative rules from DifferentialRules.
-/
lemma covariantDeriv_curvatureSl2c_expand
  (A : Fin 4 → SpacetimePoint → SL2C) (ρ μ ν : Fin 4) (x : SpacetimePoint)
  (h_diff_dmu_Anu : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c μ (A ν) p).val i j) x)
  (h_diff_dnu_Amu : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c ν (A μ) p).val i j) x)
  (h_diff_bracket : ∀ i j, DifferentiableAt ℝ (fun p => ⁅A μ p, A ν p⁆.val i j) x) :
  covariantDeriv A ρ μ ν x =
  partialDerivSl2c ρ (fun p => partialDerivSl2c μ (A ν) p) x
  - partialDerivSl2c ρ (fun p => partialDerivSl2c ν (A μ) p) x
  + partialDerivSl2c ρ (fun p => ⁅A μ p, A ν p⁆) x
  + ⁅A ρ x, partialDerivSl2c μ (A ν) x⁆
  - ⁅A ρ x, partialDerivSl2c ν (A μ) x⁆
  + ⁅A ρ x, ⁅A μ x, A ν x⁆⁆ := by

  unfold covariantDeriv

  -- Expand curvature inside the derivative
  have h_curv_eq : (fun p => curvatureSl2c A μ ν p) = fun p => partialDerivSl2c μ (A ν) p - partialDerivSl2c ν (A μ) p + ⁅A μ p, A ν p⁆ := by
    funext p
    exact curvatureSl2c_def A μ ν p
  rw [h_curv_eq]

  -- Expand the standalone curvature inside the Lie bracket
  have h_curv_x : curvatureSl2c A μ ν x = partialDerivSl2c μ (A ν) x - partialDerivSl2c ν (A μ) x + ⁅A μ x, A ν x⁆ := curvatureSl2c_def A μ ν x
  rw [h_curv_x]

  have h_sub_diff : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c μ (A ν) p - partialDerivSl2c ν (A μ) p).val i j) x := by
    intro i j
    have h_val_sub : (fun p => (partialDerivSl2c μ (A ν) p - partialDerivSl2c ν (A μ) p).val i j) = fun p => (partialDerivSl2c μ (A ν) p).val i j - (partialDerivSl2c ν (A μ) p).val i j := rfl
    rw [h_val_sub]
    exact DifferentiableAt.sub (h_diff_dmu_Anu i j) (h_diff_dnu_Amu i j)

  rw [partialDerivSl2c_add (fun p => partialDerivSl2c μ (A ν) p - partialDerivSl2c ν (A μ) p) (fun p => ⁅A μ p, A ν p⁆) ρ x h_sub_diff h_diff_bracket]
  rw [partialDerivSl2c_sub (fun p => partialDerivSl2c μ (A ν) p) (fun p => partialDerivSl2c ν (A μ) p) ρ x h_diff_dmu_Anu h_diff_dnu_Amu]

  apply Subtype.ext

  have h_val_add (M N : SL2C) : (M + N).val = M.val + N.val := rfl
  have h_val_sub (M N : SL2C) : (M - N).val = M.val - N.val := rfl
  have h_val_br (M N : SL2C) : ⁅M, N⁆.val = M.val * N.val - N.val * M.val := rfl

  simp only [h_val_add, h_val_sub, h_val_br, mul_add, add_mul, mul_sub, sub_mul]
  abel

/--
The Jacobi identity for the SL(2,C) gauge group.
By projecting the Lie bracket down to its fundamental matrix multiplication definition,
we prove this identity purely via the associativity of matrix multiplication,
leaving no algebraic loopholes.
-/
lemma sl2c_jacobi (x y z : SL2C) :
  ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  apply Subtype.ext
  have h_val_add (M N : SL2C) : (M + N).val = M.val + N.val := rfl
  have h_val_br (M N : SL2C) : ⁅M, N⁆.val = M.val * N.val - N.val * M.val := rfl
  have h_val_zero : (0 : SL2C).val = 0 := rfl

  simp only [h_val_add, h_val_br, h_val_zero, mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_assoc]
  abel

/--
Commutativity of partial derivatives for SL2C fields, derived strictly from the
N-dimensional Clairaut's theorem via the complex components.
-/
lemma partialDerivSl2c_comm
  [clairaut : Litlib.Y1976.rudin1976principles.ClairautTheoremNDimensional]
  (A : SpacetimePoint → SL2C)
  (h_smooth_re : ∀ i j, ContDiffOn ℝ 2 (fun p => ((A p).val i j).re) Set.univ)
  (h_smooth_im : ∀ i j, ContDiffOn ℝ 2 (fun p => ((A p).val i j).im) Set.univ)
  (μ ν : Fin 4) (x : SpacetimePoint)
  (h_diff_fderiv_re : ∀ i j, DifferentiableAt ℝ (fderiv ℝ (fun p => ((A p).val i j).re)) x)
  (h_diff_fderiv_im : ∀ i j, DifferentiableAt ℝ (fderiv ℝ (fun p => ((A p).val i j).im)) x)
  (h_diffA : ∀ p i j, DifferentiableAt ℝ (fun p' => (A p').val i j) p)
  (h_diff_mu : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c μ A p).val i j) x)
  (h_diff_nu : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c ν A p).val i j) x) :
  partialDerivSl2c μ (fun p => partialDerivSl2c ν A p) x =
  partialDerivSl2c ν (fun p => partialDerivSl2c μ A p) x := by
  apply Subtype.ext
  have h1 : (partialDerivSl2c μ (fun p => partialDerivSl2c ν A p) x).val = partialDerivMat μ (fun p => (partialDerivSl2c ν A p).val) x := partialDerivSl2c_eq_mat (fun p => partialDerivSl2c ν A p) μ x h_diff_nu
  have h2 : (partialDerivSl2c ν (fun p => partialDerivSl2c μ A p) x).val = partialDerivMat ν (fun p => (partialDerivSl2c μ A p).val) x := partialDerivSl2c_eq_mat (fun p => partialDerivSl2c μ A p) ν x h_diff_mu
  rw [h1, h2]
  ext i j
  have h3 : (partialDerivMat μ (fun p => (partialDerivSl2c ν A p).val) x) i j = partialDeriv μ (fun p => (partialDerivSl2c ν A p).val i j) x := rfl
  have h4 : (partialDerivMat ν (fun p => (partialDerivSl2c μ A p).val) x) i j = partialDeriv ν (fun p => (partialDerivSl2c μ A p).val i j) x := rfl
  rw [h3, h4]

  have h_inner_nu : (fun p => (partialDerivSl2c ν A p).val i j) = fun p => partialDeriv ν (fun p' => (A p').val i j) p := by
    ext p
    have h_mat := partialDerivSl2c_eq_mat A ν p (h_diffA p)
    have hr : (partialDerivMat ν (fun p' => (A p').val) p) i j = partialDeriv ν (fun p' => (A p').val i j) p := rfl
    rw [h_mat, hr]

  have h_inner_mu : (fun p => (partialDerivSl2c μ A p).val i j) = fun p => partialDeriv μ (fun p' => (A p').val i j) p := by
    ext p
    have h_mat := partialDerivSl2c_eq_mat A μ p (h_diffA p)
    have hr : (partialDerivMat μ (fun p' => (A p').val) p) i j = partialDeriv μ (fun p' => (A p').val i j) p := rfl
    rw [h_mat, hr]

  rw [h_inner_nu, h_inner_mu]

  apply Complex.ext
  · have h_re1 := partialDeriv_re (fun p => partialDeriv ν (fun p' => (A p').val i j) p) μ x (by
      have h_eq : (fun p => partialDeriv ν (fun p' => (A p').val i j) p) = fun p => (partialDerivSl2c ν A p).val i j := h_inner_nu.symm
      rw [h_eq]
      exact h_diff_nu i j)
    have h_re2 := partialDeriv_re (fun p => partialDeriv μ (fun p' => (A p').val i j) p) ν x (by
      have h_eq : (fun p => partialDeriv μ (fun p' => (A p').val i j) p) = fun p => (partialDerivSl2c μ A p).val i j := h_inner_mu.symm
      rw [h_eq]
      exact h_diff_mu i j)

    have h_inner_re_nu : (fun p => (partialDeriv ν (fun p' => (A p').val i j) p).re) = fun p => partialDeriv ν (fun p' => ((A p').val i j).re) p := by
      ext p
      exact partialDeriv_re (fun p' => (A p').val i j) ν p (h_diffA p i j)
    have h_inner_re_mu : (fun p => (partialDeriv μ (fun p' => (A p').val i j) p).re) = fun p => partialDeriv μ (fun p' => ((A p').val i j).re) p := by
      ext p
      exact partialDeriv_re (fun p' => (A p').val i j) μ p (h_diffA p i j)

    rw [h_inner_re_nu] at h_re1
    rw [h_inner_re_mu] at h_re2
    rw [h_re1, h_re2]
    exact partialDeriv_comm_real (fun p => ((A p).val i j).re) (h_smooth_re i j) μ ν x (h_diff_fderiv_re i j)

  · have h_im1 := partialDeriv_im (fun p => partialDeriv ν (fun p' => (A p').val i j) p) μ x (by
      have h_eq : (fun p => partialDeriv ν (fun p' => (A p').val i j) p) = fun p => (partialDerivSl2c ν A p).val i j := h_inner_nu.symm
      rw [h_eq]
      exact h_diff_nu i j)
    have h_im2 := partialDeriv_im (fun p => partialDeriv μ (fun p' => (A p').val i j) p) ν x (by
      have h_eq : (fun p => partialDeriv μ (fun p' => (A p').val i j) p) = fun p => (partialDerivSl2c μ A p).val i j := h_inner_mu.symm
      rw [h_eq]
      exact h_diff_mu i j)

    have h_inner_im_nu : (fun p => (partialDeriv ν (fun p' => (A p').val i j) p).im) = fun p => partialDeriv ν (fun p' => ((A p').val i j).im) p := by
      ext p
      exact partialDeriv_im (fun p' => (A p').val i j) ν p (h_diffA p i j)
    have h_inner_im_mu : (fun p => (partialDeriv μ (fun p' => (A p').val i j) p).im) = fun p => partialDeriv μ (fun p' => ((A p').val i j).im) p := by
      ext p
      exact partialDeriv_im (fun p' => (A p').val i j) μ p (h_diffA p i j)

    rw [h_inner_im_nu] at h_im1
    rw [h_inner_im_mu] at h_im2
    rw [h_im1, h_im2]
    exact partialDeriv_comm_real (fun p => ((A p).val i j).im) (h_smooth_im i j) μ ν x (h_diff_fderiv_im i j)

/--
Mathematical primitive for the Bianchi Identity.
Evaluates the Lie algebra rules directly but exposes the 14 ugly calculus bounds
required to verify differentiability step-by-step.
-/
theorem mathBianchiIdentity
  [clairaut : Litlib.Y1976.rudin1976principles.ClairautTheoremNDimensional]
  (A : Fin 4 → SpacetimePoint → SL2C) (ρ μ ν : Fin 4) (x : SpacetimePoint)
  (h_diff_dmu_Anu : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c μ (A ν) p).val i j) x)
  (h_diff_dnu_Amu : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c ν (A μ) p).val i j) x)
  (h_diff_dnu_Arho : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c ν (A ρ) p).val i j) x)
  (h_diff_drho_Anu : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c ρ (A ν) p).val i j) x)
  (h_diff_drho_Amu : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c ρ (A μ) p).val i j) x)
  (h_diff_dmu_Arho : ∀ i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c μ (A ρ) p).val i j) x)
  (h_diff_bracket_munu : ∀ i j, DifferentiableAt ℝ (fun p => ⁅A μ p, A ν p⁆.val i j) x)
  (h_diff_bracket_nurho : ∀ i j, DifferentiableAt ℝ (fun p => ⁅A ν p, A ρ p⁆.val i j) x)
  (h_diff_bracket_rhomu : ∀ i j, DifferentiableAt ℝ (fun p => ⁅A ρ p, A μ p⁆.val i j) x)
  (h_diffA : ∀ σ p i j, DifferentiableAt ℝ (fun p' => (A σ p').val i j) p)
  (h_smooth_re : ∀ σ i j, ContDiffOn ℝ 2 (fun p => ((A σ p).val i j).re) Set.univ)
  (h_smooth_im : ∀ σ i j, ContDiffOn ℝ 2 (fun p => ((A σ p).val i j).im) Set.univ)
  (h_diff_fderiv_re : ∀ σ i j, DifferentiableAt ℝ (fderiv ℝ (fun p => ((A σ p).val i j).re)) x)
  (h_diff_fderiv_im : ∀ σ i j, DifferentiableAt ℝ (fderiv ℝ (fun p => ((A σ p).val i j).im)) x) :
  covariantDeriv (A) ρ μ ν x +
  covariantDeriv (A) μ ν ρ x +
  covariantDeriv (A) ν ρ μ x = 0 := by

  rw [covariantDeriv_curvatureSl2c_expand A ρ μ ν x h_diff_dmu_Anu h_diff_dnu_Amu h_diff_bracket_munu]
  rw [covariantDeriv_curvatureSl2c_expand A μ ν ρ x h_diff_dnu_Arho h_diff_drho_Anu h_diff_bracket_nurho]
  rw [covariantDeriv_curvatureSl2c_expand A ν ρ μ x h_diff_drho_Amu h_diff_dmu_Arho h_diff_bracket_rhomu]

  rw [partialDerivSl2c_bracket (A μ) (A ν) ρ x (h_diffA μ x) (h_diffA ν x)]
  rw [partialDerivSl2c_bracket (A ν) (A ρ) μ x (h_diffA ν x) (h_diffA ρ x)]
  rw [partialDerivSl2c_bracket (A ρ) (A μ) ν x (h_diffA ρ x) (h_diffA μ x)]

  have hc1 : partialDerivSl2c ρ (fun p => partialDerivSl2c μ (A ν) p) x = partialDerivSl2c μ (fun p => partialDerivSl2c ρ (A ν) p) x :=
    partialDerivSl2c_comm (A ν) (h_smooth_re ν) (h_smooth_im ν) ρ μ x (h_diff_fderiv_re ν) (h_diff_fderiv_im ν) (h_diffA ν) h_diff_drho_Anu h_diff_dmu_Anu
  have hc2 : partialDerivSl2c ρ (fun p => partialDerivSl2c ν (A μ) p) x = partialDerivSl2c ν (fun p => partialDerivSl2c ρ (A μ) p) x :=
    partialDerivSl2c_comm (A μ) (h_smooth_re μ) (h_smooth_im μ) ρ ν x (h_diff_fderiv_re μ) (h_diff_fderiv_im μ) (h_diffA μ) h_diff_drho_Amu h_diff_dnu_Amu
  have hc3 : partialDerivSl2c μ (fun p => partialDerivSl2c ν (A ρ) p) x = partialDerivSl2c ν (fun p => partialDerivSl2c μ (A ρ) p) x :=
    partialDerivSl2c_comm (A ρ) (h_smooth_re ρ) (h_smooth_im ρ) μ ν x (h_diff_fderiv_re ρ) (h_diff_fderiv_im ρ) (h_diffA ρ) h_diff_dmu_Arho h_diff_dnu_Arho

  rw [hc1, hc2, hc3]

  apply Subtype.ext
  have h_val_add (M N : SL2C) : (M + N).val = M.val + N.val := rfl
  have h_val_sub (M N : SL2C) : (M - N).val = M.val - N.val := rfl
  have h_val_br (M N : SL2C) : ⁅M, N⁆.val = M.val * N.val - N.val * M.val := rfl
  have h_val_zero : (0 : SL2C).val = 0 := rfl

  simp only [h_val_add, h_val_sub, h_val_br, h_val_zero, mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_assoc]
  abel

/--
The Differential Bianchi Identity.
Derived strictly from fundamental Lie algebra properties and Clairaut's theorem,
simultaneously performing the $d^2=0$ and Jacobi cancellations algebraically.
-/
@[litlib_track "Kinematic Bianchi Identity"]
theorem kinematicBianchiIdentity
  [clairaut : Litlib.Y1976.rudin1976principles.ClairautTheoremNDimensional]
  (A : CGD.Axioms.Sl2cGaugeField) (ρ μ ν : Fin 4) (x : SpacetimePoint) :
  covariantDeriv A ρ μ ν x +
  covariantDeriv A μ ν ρ x +
  covariantDeriv A ν ρ μ x = 0 := by

  have h_diffA : ∀ σ p i j, DifferentiableAt ℝ (fun p' => (A σ p').val i j) p :=
    fun σ p i j => (A.is_smooth σ i j).differentiable (by decide) p

  have h_val_pd_eq : ∀ α β p i j, (partialDerivSl2c α (A β) p).val i j = partialDeriv α (fun p' => (A β p').val i j) p := by
    intro α β p i j
    have h_mat := partialDerivSl2c_eq_mat (A β) α p (h_diffA β p)
    have h_eval : (partialDerivMat α (fun p' => (A β p').val) p) i j = partialDeriv α (fun p' => (A β p').val i j) p := rfl
    rw [h_mat, h_eval]

  have h_smooth_pd : ∀ α β i j, ContDiff ℝ ⊤ (fun p => (partialDerivSl2c α (A β) p).val i j) := by
    intro α β i j
    have h_eq : (fun p => (partialDerivSl2c α (A β) p).val i j) = fun p => partialDeriv α (fun p' => (A β p').val i j) p := by
      ext p; exact h_val_pd_eq α β p i j
    rw [h_eq]
    exact contDiff_partialDeriv_complex α _ (A.is_smooth β i j)

  have h_diff_pd : ∀ α β i j, DifferentiableAt ℝ (fun p => (partialDerivSl2c α (A β) p).val i j) x :=
    fun α β i j => (h_smooth_pd α β i j).differentiable (by decide) x

  have h_val_br_eq : ∀ α β p i j, ⁅A α p, A β p⁆.val i j = ((A α p).val * (A β p).val - (A β p).val * (A α p).val) i j := fun α β p i j => rfl

  have h_smooth_br : ∀ α β i j, ContDiff ℝ ⊤ (fun p => ⁅A α p, A β p⁆.val i j) := by
    intro α β i j
    have h_eq : (fun p => ⁅A α p, A β p⁆.val i j) = fun p =>
      ((A α p).val i 0 * (A β p).val 0 j + (A α p).val i 1 * (A β p).val 1 j) -
      ((A β p).val i 0 * (A α p).val 0 j + (A β p).val i 1 * (A α p).val 1 j) := by
      ext p
      rw [h_val_br_eq, Matrix.sub_apply, mul_2x2, mul_2x2]
    rw [h_eq]
    exact (((A.is_smooth α i 0).mul (A.is_smooth β 0 j)).add ((A.is_smooth α i 1).mul (A.is_smooth β 1 j))).sub (((A.is_smooth β i 0).mul (A.is_smooth α 0 j)).add ((A.is_smooth β i 1).mul (A.is_smooth α 1 j)))

  have h_diff_br : ∀ α β i j, DifferentiableAt ℝ (fun p => ⁅A α p, A β p⁆.val i j) x :=
    fun α β i j => (h_smooth_br α β i j).differentiable (by decide) x

  have h_smooth_re : ∀ σ i j, ContDiffOn ℝ 2 (fun p => ((A σ p).val i j).re) Set.univ := by
    intro σ i j
    let Lre : ℂ →L[ℝ] ℝ := { toFun := Complex.re, map_add' := Complex.add_re, map_smul' := fun r c => by simp, cont := Complex.continuous_re }
    have h_top := ContDiff.comp (g := Complex.re) (f := fun p => (A σ p).val i j) Lre.contDiff (A.is_smooth σ i j)
    exact ContDiff.contDiffOn (ContDiff.of_le h_top le_top)

  have h_smooth_im : ∀ σ i j, ContDiffOn ℝ 2 (fun p => ((A σ p).val i j).im) Set.univ := by
    intro σ i j
    let Lim : ℂ →L[ℝ] ℝ := { toFun := Complex.im, map_add' := Complex.add_im, map_smul' := fun r c => by simp, cont := Complex.continuous_im }
    have h_top := ContDiff.comp (g := Complex.im) (f := fun p => (A σ p).val i j) Lim.contDiff (A.is_smooth σ i j)
    exact ContDiff.contDiffOn (ContDiff.of_le h_top le_top)

  have h_diff_fderiv_re : ∀ σ i j, DifferentiableAt ℝ (fderiv ℝ (fun p => ((A σ p).val i j).re)) x := by
    intro σ i j
    let Lre : ℂ →L[ℝ] ℝ := { toFun := Complex.re, map_add' := Complex.add_re, map_smul' := fun r c => by simp, cont := Complex.continuous_re }
    have h_top := ContDiff.comp (g := Complex.re) (f := fun p => (A σ p).val i j) Lre.contDiff (A.is_smooth σ i j)
    have h_fd := contDiff_fderiv_of_contDiff_real h_top
    exact (h_fd.differentiable (by decide) x)

  have h_diff_fderiv_im : ∀ σ i j, DifferentiableAt ℝ (fderiv ℝ (fun p => ((A σ p).val i j).im)) x := by
    intro σ i j
    let Lim : ℂ →L[ℝ] ℝ := { toFun := Complex.im, map_add' := Complex.add_im, map_smul' := fun r c => by simp, cont := Complex.continuous_im }
    have h_top := ContDiff.comp (g := Complex.im) (f := fun p => (A σ p).val i j) Lim.contDiff (A.is_smooth σ i j)
    have h_fd := contDiff_fderiv_of_contDiff_real h_top
    exact (h_fd.differentiable (by decide) x)

  exact mathBianchiIdentity A ρ μ ν x
    (h_diff_pd μ ν) (h_diff_pd ν μ) (h_diff_pd ν ρ) (h_diff_pd ρ ν) (h_diff_pd ρ μ) (h_diff_pd μ ρ)
    (h_diff_br μ ν) (h_diff_br ν ρ) (h_diff_br ρ μ)
    h_diffA h_smooth_re h_smooth_im h_diff_fderiv_re h_diff_fderiv_im

end CGD.Foundations

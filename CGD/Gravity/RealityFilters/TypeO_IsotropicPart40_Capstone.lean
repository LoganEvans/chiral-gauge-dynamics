-- FILENAME: CGD/Gravity/RealityFilters/TypeO_IsotropicPart40_Capstone.lean

import CGD.Gravity.RealityFilters.Definitions
import CGD.Gravity.RealityFilters.AlgebraicForms
import CGD.Gravity.RealityFilters.TypeO_IsotropicPart39_MetricOffDiag

open CGD.Axioms CGD.Foundations Complex Matrix CGD.Gravity

namespace CGD.Gravity.RealityFilters

-- ==============================================================================
-- 1. COMPLEX REALITY HELPERS
-- ==============================================================================

lemma complex_re_im_eq (z : ℂ) (h : z.im = 0) : z = (z.re : ℂ) := by
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im]
    exact h

lemma complex_ne_zero_re (z : ℂ) (h_im : z.im = 0) (h_nz : z ≠ 0) : z.re ≠ 0 := by
  intro h_re
  have h_zero : z = 0 := by
    apply Complex.ext
    · exact h_re
    · exact h_im
  contradiction

lemma im_zero_00 (adot : ℂ) (h_adot_im : adot.im = 0) : (12 * adot ^ 3).im = 0 := by
  rw [complex_re_im_eq adot h_adot_im]
  have : 12 * (adot.re : ℂ) ^ 3 = (((12 : ℝ) * adot.re ^ 3 : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  exact Complex.ofReal_im _

lemma im_zero_ii (adot a_val : ℂ) (h_adot_im : adot.im = 0) (h_a_im : a_val.im = 0) : 
  (-48 * adot * (a_val * a_val) ^ 2).im = 0 := by
  rw [complex_re_im_eq adot h_adot_im, complex_re_im_eq a_val h_a_im]
  have : -48 * (adot.re : ℂ) * ((a_val.re : ℂ) * (a_val.re : ℂ)) ^ 2 = (((-48 : ℝ) * adot.re * (a_val.re * a_val.re) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  exact Complex.ofReal_im _

-- ==============================================================================
-- 2. METRIC DETERMINANT KINEMATICS
-- ==============================================================================

lemma pow_six_pos (r : ℝ) (hr : r ≠ 0) : 0 < r ^ 6 := by
  have h2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have h6 : r ^ 6 = (r ^ 2) ^ 3 := by ring
  rw [h6]
  exact pow_pos h2 3

lemma pow_twelve_pos (r : ℝ) (hr : r ≠ 0) : 0 < r ^ 12 := by
  have h2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have h12 : r ^ 12 = (r ^ 2) ^ 6 := by ring
  rw [h12]
  exact pow_pos h2 6

lemma fin_prod_four (f : Fin 4 → ℂ) : (∏ i : Fin 4, f i) = f 0 * f 1 * f 2 * f 3 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp
  ring

lemma det_diag_4x4 (M : Matrix (Fin 4) (Fin 4) ℂ) (h_off : ∀ i j, i ≠ j → M i j = 0) :
  M.det = M 0 0 * M 1 1 * M 2 2 * M 3 3 := by
  have h_diag : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq]
    · rw [h_off i j h]
      exact (Matrix.diagonal_apply_ne _ h).symm
  rw [h_diag]
  rw [Matrix.det_diagonal]
  exact fin_prod_four (fun i => M i i)

lemma typeO_det_eval (a : ℝ → ℂ) (x : SpacetimePoint) (ha : DifferentiableAt ℝ a (x 0)) :
  (urbantkeMetric (fun m n => curvatureSl2c (typeO_A a) m n x)).det =
  -1327104 * (fderiv ℝ a (x 0) 1) ^ 6 * (a (x 0)) ^ 12 := by
  have h00 := typeO_metric_00 a x ha
  have h11 := typeO_metric_11 a x ha
  have h22 := typeO_metric_22 a x ha
  have h33 := typeO_metric_33 a x ha
  have h_off : ∀ μ ν, μ ≠ ν → urbantkeMetric (fun m n => curvatureSl2c (typeO_A a) m n x) μ ν = 0 := 
    fun μ ν h_diff => typeO_metric_off_diagonal a x ha μ ν h_diff
  have h_det := det_diag_4x4 (urbantkeMetric (fun m n => curvatureSl2c (typeO_A a) m n x)) h_off
  rw [h_det, h00, h11, h22, h33]
  ring

lemma typeO_det_signs (adot a_val : ℂ)
  (h_adot_im : adot.im = 0) (h_a_im : a_val.im = 0)
  (h_adot_nz : adot ≠ 0) (h_a_nz : a_val ≠ 0) :
  (-1327104 * adot ^ 6 * a_val ^ 12).im = 0 ∧
  (-1327104 * adot ^ 6 * a_val ^ 12).re < 0 := by
  have h_adot_re := complex_re_im_eq adot h_adot_im
  have h_a_re := complex_re_im_eq a_val h_a_im
  have h_sub : -1327104 * adot ^ 6 * a_val ^ 12 = (-1327104 * (adot.re : ℂ) ^ 6 * (a_val.re : ℂ) ^ 12) := by
    rw [← h_adot_re, ← h_a_re]
  rw [h_sub]
  have h_real_cast : (-1327104 * (adot.re : ℂ) ^ 6 * (a_val.re : ℂ) ^ 12) = (((-1327104 : ℝ) * adot.re ^ 6 * a_val.re ^ 12 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [h_real_cast]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  have h_adot_nz_re : adot.re ≠ 0 := complex_ne_zero_re adot h_adot_im h_adot_nz
  have h_a_nz_re : a_val.re ≠ 0 := complex_ne_zero_re a_val h_a_im h_a_nz
  have h_adot_pos := pow_six_pos adot.re h_adot_nz_re
  have h_a_pos := pow_twelve_pos a_val.re h_a_nz_re
  have h_mul_pos : 0 < adot.re ^ 6 * a_val.re ^ 12 := mul_pos h_adot_pos h_a_pos
  linarith

-- ==============================================================================
-- 3. THE CAPSTONE: GLOBAL VERIFICATION OF COSMOLOGICAL REALITY
-- ==============================================================================

lemma diff_of_fderiv_apply_ne_zero (f : ℝ → ℂ) (t : ℝ) (h : fderiv ℝ f t 1 ≠ 0) : DifferentiableAt ℝ f t := by
  by_contra hc
  have h0 : fderiv ℝ f t = 0 := fderiv_zero_of_not_differentiableAt hc
  have h1 : fderiv ℝ f t 1 = 0 := by rw [h0]; rfl
  exact h h1

lemma typeO_A_eval_0 (a : ℝ → ℂ) (p : SpacetimePoint) : typeO_A a 0 p = 0 := by
  apply Subtype.ext
  change (typeO_A a 0 p).val = 0
  rw [typeO_A_val_eq, typeO_L_0_eq]

lemma typeO_A_eval_1 (a : ℝ → ℂ) (p : SpacetimePoint) : typeO_A a 1 p = toSl2c (a (p 0) • sigma1.val) := by
  unfold typeO_A typeO_L
  simp

lemma typeO_A_eval_2 (a : ℝ → ℂ) (p : SpacetimePoint) : typeO_A a 2 p = toSl2c (a (p 0) • sigma2.val) := by
  unfold typeO_A typeO_L
  simp

lemma typeO_A_eval_3 (a : ℝ → ℂ) (p : SpacetimePoint) : typeO_A a 3 p = toSl2c (a (p 0) • sigma3.val) := by
  unfold typeO_A typeO_L
  simp

lemma typeO_A_eq (pu : PhysicalUniverse) (a : ℝ → ℂ)
  (h0 : ∀ p : SpacetimePoint, pu.toUniverse.sd_sector.val 0 p = 0)
  (h1 : ∀ p : SpacetimePoint, pu.toUniverse.sd_sector.val 1 p = toSl2c (a (p 0) • sigma1.val))
  (h2 : ∀ p : SpacetimePoint, pu.toUniverse.sd_sector.val 2 p = toSl2c (a (p 0) • sigma2.val))
  (h3 : ∀ p : SpacetimePoint, pu.toUniverse.sd_sector.val 3 p = toSl2c (a (p 0) • sigma3.val)) :
  pu.toUniverse.sd_sector.val = typeO_A a := by
  apply funext
  intro μ
  apply funext
  intro p
  fin_cases μ
  · change pu.toUniverse.sd_sector.val 0 p = typeO_A a 0 p
    rw [h0 p, typeO_A_eval_0]
  · change pu.toUniverse.sd_sector.val 1 p = typeO_A a 1 p
    rw [h1 p, typeO_A_eval_1]
  · change pu.toUniverse.sd_sector.val 2 p = typeO_A a 2 p
    rw [h2 p, typeO_A_eval_2]
  · change pu.toUniverse.sd_sector.val 3 p = typeO_A a 3 p
    rw [h3 p, typeO_A_eval_3]

/--
CAPSTONE THEOREM: Type O (Isotropic/FLRW) spacetimes intrinsically satisfy the non-degenerate 
Lorentzian Reality Conditions natively from the SU(2) topology, requiring no exact scalar field assumptions.
-/
theorem typeO_satisfies_reality (pu : PhysicalUniverse) (h_typeO : IsTypeOForm pu) :
  SatisfiesRealityConditions pu := by
  
  unfold SatisfiesRealityConditions
  intro x _ -- Bulk constraint satisfied strictly globally
  
  rcases h_typeO with ⟨a, h_a_global⟩
  
  -- Extract scalar properties at evaluation point x
  have hx := h_a_global x
  have h_a_im : (a (x 0)).im = 0 := hx.1
  have h_adot_im : (fderiv ℝ a (x 0) 1).im = 0 := hx.2.1
  have h_a_nz : a (x 0) ≠ 0 := hx.2.2.1
  have h_adot_nz : fderiv ℝ a (x 0) 1 ≠ 0 := hx.2.2.2.1
  
  -- Extract and elevate field equalities globally
  have h0 : ∀ p, pu.toUniverse.sd_sector.val 0 p = 0 := fun p => (h_a_global p).2.2.2.2.1
  have h1 : ∀ p, pu.toUniverse.sd_sector.val 1 p = toSl2c (a (p 0) • sigma1.val) := fun p => (h_a_global p).2.2.2.2.2.1
  have h2 : ∀ p, pu.toUniverse.sd_sector.val 2 p = toSl2c (a (p 0) • sigma2.val) := fun p => (h_a_global p).2.2.2.2.2.2.1
  have h3 : ∀ p, pu.toUniverse.sd_sector.val 3 p = toSl2c (a (p 0) • sigma3.val) := fun p => (h_a_global p).2.2.2.2.2.2.2
  
  have ha_diff : DifferentiableAt ℝ a (x 0) := diff_of_fderiv_apply_ne_zero a (x 0) h_adot_nz
  
  have h_A_eq : pu.toUniverse.sd_sector.val = typeO_A a := typeO_A_eq pu a h0 h1 h2 h3
  
  have h_metric_eq : (urbantkeMetric (fun μ ν => curvatureSl2c pu.toUniverse.sd_sector.val μ ν x)) =
                     (urbantkeMetric (fun μ ν => curvatureSl2c (typeO_A a) μ ν x)) := by rw [h_A_eq]
                     
  unfold isLorentzian
  rw [h_metric_eq]
  
  -- 1. Verify imaginary metric components dynamically collapse to zero
  have h_im_zero : ∀ i j, (urbantkeMetric (fun μ ν => curvatureSl2c (typeO_A a) μ ν x) i j).im = 0 := by
    intro i j
    by_cases h_diff : i = j
    · subst h_diff
      fin_cases i
      · change (urbantkeMetric (fun μ ν => curvatureSl2c (typeO_A a) μ ν x) 0 0).im = 0
        rw [typeO_metric_00 a x ha_diff]
        exact im_zero_00 _ h_adot_im
      · change (urbantkeMetric (fun μ ν => curvatureSl2c (typeO_A a) μ ν x) 1 1).im = 0
        rw [typeO_metric_11 a x ha_diff]
        exact im_zero_ii _ _ h_adot_im h_a_im
      · change (urbantkeMetric (fun μ ν => curvatureSl2c (typeO_A a) μ ν x) 2 2).im = 0
        rw [typeO_metric_22 a x ha_diff]
        exact im_zero_ii _ _ h_adot_im h_a_im
      · change (urbantkeMetric (fun μ ν => curvatureSl2c (typeO_A a) μ ν x) 3 3).im = 0
        rw [typeO_metric_33 a x ha_diff]
        exact im_zero_ii _ _ h_adot_im h_a_im
    · have h_off := typeO_metric_off_diagonal a x ha_diff i j h_diff
      change (urbantkeMetric (fun μ ν => curvatureSl2c (typeO_A a) μ ν x) i j).im = 0
      rw [h_off]
      rfl
      
  -- 2. Verify determinant reality conditions (strict Non-Degenerate Lorentzian Signature)
  have h_det_eval_eq := typeO_det_eval a x ha_diff
  have h_signs := typeO_det_signs (fderiv ℝ a (x 0) 1) (a (x 0)) h_adot_im h_a_im h_adot_nz h_a_nz
  
  rw [h_det_eval_eq]
  
  exact ⟨h_im_zero, h_signs.2, h_signs.1⟩

end CGD.Gravity.RealityFilters

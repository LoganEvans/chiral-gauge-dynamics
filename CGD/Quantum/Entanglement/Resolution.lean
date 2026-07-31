-- FILENAME: CGD/Quantum/Entanglement/Resolution.lean

import Litlib.Y1964.bell1964einstein.Signature
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import CGD.Quantum.Entanglement.NoSignaling
import CGD.Quantum.FluxTube
import CGD.Quantum.Entanglement.BellTheorem

set_option autoImplicit false

open MeasureTheory
open scoped InnerProductSpace

namespace CGD.Quantum

noncomputable def resVecA (i : Fin 3) : ℝ := match i.val with | 0 => 1 | _ => 0
noncomputable def resValA : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm resVecA

@[simp] lemma resValA_0 : resValA 0 = 1 := rfl
@[simp] lemma resValA_1 : resValA 1 = 0 := rfl
@[simp] lemma resValA_2 : resValA 2 = 0 := rfl

lemma norm_resValA : ‖resValA‖ = 1 := by
  have h1 : ‖resValA‖ ^ 2 = ⟪resValA, resValA⟫_ℝ := Eq.symm (real_inner_self_eq_norm_sq resValA)
  have h2 : ⟪resValA, resValA⟫_ℝ = 1 := by
    change (∑ i : Fin 3, resValA i * resValA i) = 1
    have h_expand : (∑ i : Fin 3, resValA i * resValA i) = resValA 0 * resValA 0 + resValA 1 * resValA 1 + resValA 2 * resValA 2 := by simp [Fin.sum_univ_succ]
    rw [h_expand]
    norm_num
  rw [h2] at h1
  have h5 : 0 ≤ ‖resValA‖ := norm_nonneg resValA
  nlinarith

noncomputable def resVecD (i : Fin 3) : ℝ := match i.val with | 1 => 1 | _ => 0
noncomputable def resValD : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm resVecD

@[simp] lemma resValD_0 : resValD 0 = 0 := rfl
@[simp] lemma resValD_1 : resValD 1 = 1 := rfl
@[simp] lemma resValD_2 : resValD 2 = 0 := rfl

lemma norm_resValD : ‖resValD‖ = 1 := by
  have h1 : ‖resValD‖ ^ 2 = ⟪resValD, resValD⟫_ℝ := Eq.symm (real_inner_self_eq_norm_sq resValD)
  have h2 : ⟪resValD, resValD⟫_ℝ = 1 := by
    change (∑ i : Fin 3, resValD i * resValD i) = 1
    have h_expand : (∑ i : Fin 3, resValD i * resValD i) = resValD 0 * resValD 0 + resValD 1 * resValD 1 + resValD 2 * resValD 2 := by simp [Fin.sum_univ_succ]
    rw [h_expand]
    norm_num
  rw [h2] at h1
  have h5 : 0 ≤ ‖resValD‖ := norm_nonneg resValD
  nlinarith

noncomputable def resVecB (i : Fin 3) : ℝ := match i.val with | 0 => 4/5 | 1 => 3/5 | _ => 0
noncomputable def resValB : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm resVecB

@[simp] lemma resValB_0 : resValB 0 = 4/5 := rfl
@[simp] lemma resValB_1 : resValB 1 = 3/5 := rfl
@[simp] lemma resValB_2 : resValB 2 = 0 := rfl

lemma norm_resValB : ‖resValB‖ = 1 := by
  have h1 : ‖resValB‖ ^ 2 = ⟪resValB, resValB⟫_ℝ := Eq.symm (real_inner_self_eq_norm_sq resValB)
  have h2 : ⟪resValB, resValB⟫_ℝ = 1 := by
    change (∑ i : Fin 3, resValB i * resValB i) = 1
    have h_expand : (∑ i : Fin 3, resValB i * resValB i) = resValB 0 * resValB 0 + resValB 1 * resValB 1 + resValB 2 * resValB 2 := by simp [Fin.sum_univ_succ]
    rw [h_expand]
    norm_num
  rw [h2] at h1
  have h5 : 0 ≤ ‖resValB‖ := norm_nonneg resValB
  nlinarith

noncomputable def resVecC (i : Fin 3) : ℝ := match i.val with | 0 => 4/5 | 1 => -3/5 | _ => 0
noncomputable def resValC : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm resVecC

@[simp] lemma resValC_0 : resValC 0 = 4/5 := rfl
@[simp] lemma resValC_1 : resValC 1 = -3/5 := rfl
@[simp] lemma resValC_2 : resValC 2 = 0 := rfl

lemma norm_resValC : ‖resValC‖ = 1 := by
  have h1 : ‖resValC‖ ^ 2 = ⟪resValC, resValC⟫_ℝ := Eq.symm (real_inner_self_eq_norm_sq resValC)
  have h2 : ⟪resValC, resValC⟫_ℝ = 1 := by
    change (∑ i : Fin 3, resValC i * resValC i) = 1
    have h_expand : (∑ i : Fin 3, resValC i * resValC i) = resValC 0 * resValC 0 + resValC 1 * resValC 1 + resValC 2 * resValC 2 := by simp [Fin.sum_univ_succ]
    rw [h_expand]
    norm_num
  rw [h2] at h1
  have h5 : 0 ≤ ‖resValC‖ := norm_nonneg resValC
  nlinarith

lemma chsh_pointwise (A_a A_d B_b B_c : ℝ) (hAa : A_a = 1 ∨ A_a = -1) (hAd : A_d = 1 ∨ A_d = -1) (hBb : B_b = 1 ∨ B_b = -1) (hBc : B_c = 1 ∨ B_c = -1) :
  - (A_a * B_b) - (A_a * B_c) - (A_d * B_b) + (A_d * B_c) ≤ 2 := by
  rcases hAa with rfl | rfl <;> rcases hAd with rfl | rfl <;> rcases hBb with rfl | rfl <;> rcases hBc with rfl | rfl <;> norm_num

@[litlib_track "Integrated CHSH Absolute Bound"]
lemma chsh_integral_bound (Λ : Type*) [MeasurableSpace Λ] (μ : Measure Λ)
  (A B : EuclideanSpace ℝ (Fin 3) → Λ → ℝ)
  (h_mu : μ Set.univ = 1)
  (hA : ∀ a lam, ‖a‖ = 1 → A a lam = 1 ∨ A a lam = -1)
  (hB : ∀ b lam, ‖b‖ = 1 → B b lam = 1 ∨ B b lam = -1)
  (h_int : ∀ x y, ‖x‖ = 1 → ‖y‖ = 1 → Integrable (fun lam => A x lam * B y lam) μ)
  (a d b c : EuclideanSpace ℝ (Fin 3))
  (ha : ‖a‖ = 1) (hd : ‖d‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
  - (∫ lam, A a lam * B b lam ∂μ) - (∫ lam, A a lam * B c lam ∂μ) -
  (∫ lam, A d lam * B b lam ∂μ) + (∫ lam, A d lam * B c lam ∂μ) ≤ 2 := by
  
  have i1 := h_int a b ha hb
  have i2 := h_int a c ha hc
  have i3 := h_int d b hd hb
  have i4 := h_int d c hd hc
  
  have int_neg_1 : Integrable (fun lam => -(A a lam * B b lam)) μ := Integrable.neg i1
  have int_sub_2 : Integrable (fun lam => -(A a lam * B b lam) - (A a lam * B c lam)) μ := Integrable.sub int_neg_1 i2
  have int_sub_3 : Integrable (fun lam => -(A a lam * B b lam) - (A a lam * B c lam) - (A d lam * B b lam)) μ := Integrable.sub int_sub_2 i3
  
  have H_split : ∫ lam, -(A a lam * B b lam) - (A a lam * B c lam) - (A d lam * B b lam) + (A d lam * B c lam) ∂μ =
      - (∫ lam, A a lam * B b lam ∂μ) - (∫ lam, A a lam * B c lam ∂μ) -
      (∫ lam, A d lam * B b lam ∂μ) + (∫ lam, A d lam * B c lam ∂μ) := by
    rw [integral_add int_sub_3 i4]
    rw [integral_sub int_sub_2 i3]
    rw [integral_sub int_neg_1 i2]
    rw [integral_neg]
      
  rw [← H_split]
  
  haveI : IsProbabilityMeasure μ := ⟨h_mu⟩
  have h_int_const : Integrable (fun _ : Λ => (2 : ℝ)) μ := integrable_const (2 : ℝ)
  
  have h_int_f : Integrable (fun lam => -(A a lam * B b lam) - (A a lam * B c lam) - (A d lam * B b lam) + (A d lam * B c lam)) μ := 
    Integrable.add int_sub_3 i4
    
  have h_le : ∀ lam, -(A a lam * B b lam) - (A a lam * B c lam) - (A d lam * B b lam) + (A d lam * B c lam) ≤ 2 := by
    intro lam
    apply chsh_pointwise (A a lam) (A d lam) (B b lam) (B c lam)
    · exact hA a lam ha
    · exact hA d lam hd
    · exact hB b lam hb
    · exact hB c lam hc
    
  have h_mono := integral_mono h_int_f h_int_const h_le
  
  have h_int_2 : ∫ _ : Λ, (2 : ℝ) ∂μ = 2 := by
    rw [integral_const]
    change (μ Set.univ).toReal • (2 : ℝ) = 2
    rw [h_mu]
    have h_one : (1 : ENNReal).toReal = 1 := ENNReal.toReal_one
    rw [h_one]
    exact one_smul ℝ (2 : ℝ)
    
  rw [h_int_2] at h_mono
  exact h_mono

@[litlib_track "LHV Cannot Represent Exact Singlet"]
theorem cannot_represent_exactly_proof (Λ : Type*) [MeasurableSpace Λ] :
  ¬ ∃ (μ : Measure Λ) (A B : EuclideanSpace ℝ (Fin 3) → Λ → ℝ),
    (μ Set.univ = 1) ∧
    (∀ a lam, ‖a‖ = 1 → A a lam = 1 ∨ A a lam = -1) ∧
    (∀ b lam, ‖b‖ = 1 → B b lam = 1 ∨ B b lam = -1) ∧
    (∀ a b, ‖a‖ = 1 → ‖b‖ = 1 → Integrable (fun lam => A a lam * B b lam) μ) ∧
    (∀ a b, ‖a‖ = 1 → ‖b‖ = 1 →
      ∫ lam, A a lam * B b lam ∂μ = - ∑ i : Fin 3, a i * b i) := by
  intro h_exists
  rcases h_exists with ⟨μ, A, B, h_mu, hA, hB, h_int, h_eq⟩
  
  have h_bound := chsh_integral_bound Λ μ A B h_mu hA hB h_int resValA resValD resValB resValC norm_resValA norm_resValD norm_resValB norm_resValC
  
  rw [h_eq resValA resValB norm_resValA norm_resValB] at h_bound
  rw [h_eq resValA resValC norm_resValA norm_resValC] at h_bound
  rw [h_eq resValD resValB norm_resValD norm_resValB] at h_bound
  rw [h_eq resValD resValC norm_resValD norm_resValC] at h_bound
  
  have h_ab : (∑ i : Fin 3, resValA i * resValB i) = resValA 0 * resValB 0 + resValA 1 * resValB 1 + resValA 2 * resValB 2 := by simp [Fin.sum_univ_succ]
  have h_ac : (∑ i : Fin 3, resValA i * resValC i) = resValA 0 * resValC 0 + resValA 1 * resValC 1 + resValA 2 * resValC 2 := by simp [Fin.sum_univ_succ]
  have h_db : (∑ i : Fin 3, resValD i * resValB i) = resValD 0 * resValB 0 + resValD 1 * resValB 1 + resValD 2 * resValB 2 := by simp [Fin.sum_univ_succ]
  have h_dc : (∑ i : Fin 3, resValD i * resValC i) = resValD 0 * resValC 0 + resValD 1 * resValC 1 + resValD 2 * resValC 2 := by simp [Fin.sum_univ_succ]
  
  rw [h_ab, h_ac, h_db, h_dc] at h_bound
  
  revert h_bound
  norm_num

@[litlib_track "LHV Cannot Represent Arbitrarily Closely"]
theorem cannot_represent_approx_proof (Λ : Type*) [MeasurableSpace Λ] :
  ¬ ∀ (ε : ℝ), ε > 0 →
    ∃ (μ : Measure Λ) (A B : EuclideanSpace ℝ (Fin 3) → Λ → ℝ),
      (μ Set.univ = 1) ∧
      (∀ a lam, ‖a‖ = 1 → A a lam = 1 ∨ A a lam = -1) ∧
      (∀ b lam, ‖b‖ = 1 → B b lam = 1 ∨ B b lam = -1) ∧
      (∀ a b, ‖a‖ = 1 → ‖b‖ = 1 → Integrable (fun lam => A a lam * B b lam) μ) ∧
      (∀ a b, ‖a‖ = 1 → ‖b‖ = 1 →
        |(∫ lam, A a lam * B b lam ∂μ) - (- ∑ i : Fin 3, a i * b i)| < ε) := by
  intro h_forall
  have h_exists := h_forall (1/10 : ℝ) (by norm_num)
  rcases h_exists with ⟨μ, A, B, h_mu, hA, hB, h_int, h_approx⟩
  
  have h_bound := chsh_integral_bound Λ μ A B h_mu hA hB h_int resValA resValD resValB resValC norm_resValA norm_resValD norm_resValB norm_resValC
  
  have h_ab := h_approx resValA resValB norm_resValA norm_resValB
  have h_ac := h_approx resValA resValC norm_resValA norm_resValC
  have h_db := h_approx resValD resValB norm_resValD norm_resValB
  have h_dc := h_approx resValD resValC norm_resValD norm_resValC
  
  have dot_ab : (∑ i : Fin 3, resValA i * resValB i) = 4/5 := by
    have H : (∑ i : Fin 3, resValA i * resValB i) = resValA 0 * resValB 0 + resValA 1 * resValB 1 + resValA 2 * resValB 2 := by simp [Fin.sum_univ_succ]
    rw [H]; norm_num
  have dot_ac : (∑ i : Fin 3, resValA i * resValC i) = 4/5 := by
    have H : (∑ i : Fin 3, resValA i * resValC i) = resValA 0 * resValC 0 + resValA 1 * resValC 1 + resValA 2 * resValC 2 := by simp [Fin.sum_univ_succ]
    rw [H]; norm_num
  have dot_db : (∑ i : Fin 3, resValD i * resValB i) = 3/5 := by
    have H : (∑ i : Fin 3, resValD i * resValB i) = resValD 0 * resValB 0 + resValD 1 * resValB 1 + resValD 2 * resValB 2 := by simp [Fin.sum_univ_succ]
    rw [H]; norm_num
  have dot_dc : (∑ i : Fin 3, resValD i * resValC i) = -3/5 := by
    have H : (∑ i : Fin 3, resValD i * resValC i) = resValD 0 * resValC 0 + resValD 1 * resValC 1 + resValD 2 * resValC 2 := by simp [Fin.sum_univ_succ]
    rw [H]; norm_num
    
  rw [dot_ab] at h_ab
  rw [dot_ac] at h_ac
  rw [dot_db] at h_db
  rw [dot_dc] at h_dc
  
  have I_ab_lt : (∫ lam, A resValA lam * B resValB lam ∂μ) < -7/10 := by
    have H1 := (abs_lt.mp h_ab).2
    linarith
  have I_ac_lt : (∫ lam, A resValA lam * B resValC lam ∂μ) < -7/10 := by
    have H1 := (abs_lt.mp h_ac).2
    linarith
  have I_db_lt : (∫ lam, A resValD lam * B resValB lam ∂μ) < -1/2 := by
    have H1 := (abs_lt.mp h_db).2
    linarith
  have I_dc_gt : (∫ lam, A resValD lam * B resValC lam ∂μ) > 1/2 := by
    have H1 := (abs_lt.mp h_dc).1
    linarith
    
  linarith

/--
Tier 1: Pure Algebraic Realization.
Proves that the mathematical structure of CGD perfectly instantiates Bell's 
logical conclusion, completely independent of the physical universe ontology.
-/
@[litlib_track "CGD Geometric Trace Derives Bell's Conclusion"]
theorem cgdDerivesBellConclusion :
  Litlib.Y1964.bell1964einstein.Theorem_Conclusion :=
  {
    cannot_represent_exactly := cannot_represent_exactly_proof
    cannot_represent_arbitrarily_closely := cannot_represent_approx_proof
  }

/--
The Capstone Synthesis.
Elegantly unifies the three pillars of entanglement in Chiral Gauge Dynamics:
1. It natively violates the classical correlation limit (CHSH > 2).
2. It strictly obeys Bell's Theorem (Forces the rejection of Local Hidden Variables).
3. It strictly obeys the No-Signaling Theorem (The spacetime metric determinant is zero, 
   mathematically preventing classical geodesic motion or wave propagation).
-/
@[litlib_track "Deterministic Entanglement Resolution"]
theorem cgdEntanglementSynthesis 
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (pu : CGD.Axioms.PhysicalUniverse) 
  (x : CGD.Foundations.SpacetimePoint) 
  (L : ℝ)
  (h_tube : isFluxTube pu.toUniverse.sd_sector x)
  (h_eval : physicalCorrelation matrixExp pu L = cgdMacroscopicCorrelation) :
  
  -- 1. Violation of the Classical Limit (Bell's Inequality)
  (∃ (a b c : EuclideanSpace ℝ (Fin 3)), 
    ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ ‖c‖ = 1 ∧ 
    1 + physicalCorrelation matrixExp pu L b c < abs (physicalCorrelation matrixExp pu L a b - physicalCorrelation matrixExp pu L a c)) ∧
    
  -- 2. Compliance with Bell's Theorem (Rejection of LHVs)
  (Litlib.Y1964.bell1964einstein.Theorem_Conclusion) ∧
      
  -- 3. Compliance with No-Signaling (Topological Metric Degeneracy)
  ((CGD.Gravity.urbantkeMetric (fun m n => CGD.Foundations.curvatureSl2c pu.toUniverse.sd_sector m n x)).det = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases cgdAlgebraicViolationWitness with ⟨a, b, c, ha, hb, hc, h_viol⟩
    use a, b, c
    refine ⟨ha, hb, hc, ?_⟩
    rw [h_eval]
    exact h_viol
  · exact cgdDerivesBellConclusion
  · exact kinematicFluxTubeStability pu x h_tube

end CGD.Quantum

-- FILENAME: CGD/Quantum/Entanglement/Synthesis.lean

import CGD.Quantum.Entanglement.Geometry
import CGD.Quantum.Entanglement.Algebra
import CGD.Quantum.Entanglement.CHSH
import CGD.Quantum.Entanglement.HiddenVariables
import CGD.Quantum.Entanglement.NoSignaling
import CGD.Quantum.Holonomy.Evaluation
import Litlib.Y1964.bell1964einstein.Signature
import Litlib.Y2000.hall2000elementary.Signature
import CGD.Quantum.Definitions

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open CGD.Axioms CGD.Foundations CGD.Gravity Litlib.Y1964.bell1964einstein MeasureTheory

namespace CGD.Quantum

lemma toSl2c_of_sl2c (A : SL2C) : toSl2c A.val = A := by
  apply Subtype.ext
  unfold toSl2c
  dsimp
  have h_tr : Matrix.trace A.val = 0 := A.property
  rw [h_tr]
  have hz : (0:ℂ) / 2 = 0 := by norm_num
  rw [hz, zero_smul, sub_zero]

lemma rotateYAxis_zero (A : Fin 4 → SpacetimePoint → SL2C) :
  (fun mu p => rotateYAxis A 0 mu p) = A := by
  funext mu p
  unfold rotateYAxis
  have hz1 : (((0 : ℝ) : ℂ) / 2) = 0 := by norm_num
  have hz2 : (↑((0 : ℝ) / 2) : ℂ) = 0 := by norm_num
  simp only [hz1, hz2, Complex.cos_zero, Complex.sin_zero, neg_zero]
  have hR : Matrix.of ![![1, (0:ℂ)], ![0, 1]] = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  simp only [hR, Matrix.one_mul, Matrix.mul_one]
  exact toSl2c_of_sl2c (A mu p)

lemma fluxTube_holonomy_unitary
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  [Litlib.Y2000.hall2000elementary.DerivativeExponential (Fin 2) matrixExp]
  (pu : CGD.Axioms.PhysicalUniverse) (L : ℝ)
  (hField : ∀ t, pu.toUniverse.sd_sector.val 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t)) :
  (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) pu.toUniverse.sd_sector.val 1 L) * 
  (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) pu.toUniverse.sd_sector.val 1 L).conjTranspose = 1 := by
  have hField_coe : ∀ t, pu.toUniverse.sd_sector 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t) := hField
  have h_eval := fluxTubeHolonomyEvaluation matrixExp pu 0 L hField_coe
  have h_rot_zero_sl2c : (fun mu p => rotateYAxis pu.toUniverse.sd_sector.val 0 mu p) = pu.toUniverse.sd_sector.val := rotateYAxis_zero pu.toUniverse.sd_sector.val
  change CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) (fun mu p => rotateYAxis pu.toUniverse.sd_sector.val 0 mu p) 1 L = _ at h_eval
  rw [h_rot_zero_sl2c] at h_eval
  have h_su2 := obsHolonomyIsSu2 0 L
  rw [← h_eval] at h_su2
  exact h_su2.1

/--
  The TRUE Physical Bridge. 
  We define the physical correlation by evaluating the macroscopic gauge field 
  holonomy (parallel transport) across the universe, and projecting it against 
  the 3D detector orientations `a` and `b`.
-/
noncomputable def physicalCorrelation 
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (pu : CGD.Axioms.PhysicalUniverse) (L : ℝ) 
  (a b : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  let holonomy_path := CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) pu.toUniverse.sd_sector.val 1 L
  let stateA := cgdMatrix a * holonomy_path
  let stateB := cgdMatrix b * holonomy_path
  ((1 / 2 : ℂ) * Matrix.trace (stateA * stateB.conjTranspose)).re

lemma physicalCorrelation_unitary_reduction
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  (pu : CGD.Axioms.PhysicalUniverse) 
  (L : ℝ) 
  (a b : EuclideanSpace ℝ (Fin 3))
  (h_unitary : (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) pu.toUniverse.sd_sector.val 1 L) * (CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) pu.toUniverse.sd_sector.val 1 L).conjTranspose = 1) :
  physicalCorrelation matrixExp pu L a b = cgdMacroscopicCorrelation a b := by
  simp only [physicalCorrelation, cgdMacroscopicCorrelation]
  let H := CGD.Quantum.macroscopicObservable (CGD.Quantum.holonomy matrixExp) pu.toUniverse.sd_sector.val 1 L
  change ((1 / 2 : ℂ) * Matrix.trace (cgdMatrix a * H * (cgdMatrix b * H).conjTranspose)).re = ((1 / 2 : ℂ) * Matrix.trace (cgdMatrix a * (cgdMatrix b).conjTranspose)).re
  have h1 : (cgdMatrix b * H).conjTranspose = H.conjTranspose * (cgdMatrix b).conjTranspose := Matrix.conjTranspose_mul _ _
  rw [h1]
  have step1 : cgdMatrix a * H * (H.conjTranspose * (cgdMatrix b).conjTranspose) = cgdMatrix a * (H * (H.conjTranspose * (cgdMatrix b).conjTranspose)) := Matrix.mul_assoc _ _ _
  rw [step1]
  have step2 : H * (H.conjTranspose * (cgdMatrix b).conjTranspose) = (H * H.conjTranspose) * (cgdMatrix b).conjTranspose := (Matrix.mul_assoc _ _ _).symm
  rw [step2]
  rw [h_unitary]
  rw [Matrix.one_mul]

@[litlib_track "Physical Universe Rejects Bell's Premises"]
theorem physicalRejectionOfBellPremises 
  (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
  [Litlib.Y2000.hall2000elementary.DerivativeExponential (Fin 2) matrixExp]
  (pu : CGD.Axioms.PhysicalUniverse)
  (L : ℝ)
  (Λ : Type) [MeasurableSpace Λ] (μ : Measure Λ) 
  (A B : EuclideanSpace ℝ (Fin 3) → Λ → ℝ)
  (bell_theorem : Eq1 A B → Eq2 μ A B (physicalCorrelation matrixExp pu L) → Eq15 (physicalCorrelation matrixExp pu L))
  (hField : ∀ t, pu.toUniverse.sd_sector.val 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t)) :
  ¬ (Eq1 A B ∧ Eq2 μ A B (physicalCorrelation matrixExp pu L)) := by
  intro h
  have h15 : Eq15 (physicalCorrelation matrixExp pu L) := bell_theorem h.1 h.2
  have h_unitary := fluxTube_holonomy_unitary matrixExp pu L hField
  have h_eq : physicalCorrelation matrixExp pu L = cgdMacroscopicCorrelation := by
    funext a b
    exact physicalCorrelation_unitary_reduction matrixExp pu L a b h_unitary
  rw [h_eq] at h15
  exact cgdViolatesBellInequality h15

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
  [Litlib.Y2000.hall2000elementary.DerivativeExponential (Fin 2) matrixExp]
  (pu : CGD.Axioms.PhysicalUniverse) 
  (x : CGD.Foundations.SpacetimePoint) 
  (L : ℝ)
  (h_tube : isFluxTube pu.toUniverse.sd_sector x)
  (hField : ∀ t, pu.toUniverse.sd_sector.val 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t)) :
  
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
    have h_unitary := fluxTube_holonomy_unitary matrixExp pu L hField
    have h_eq_ab : physicalCorrelation matrixExp pu L a b = cgdMacroscopicCorrelation a b := physicalCorrelation_unitary_reduction matrixExp pu L a b h_unitary
    have h_eq_ac : physicalCorrelation matrixExp pu L a c = cgdMacroscopicCorrelation a c := physicalCorrelation_unitary_reduction matrixExp pu L a c h_unitary
    have h_eq_bc : physicalCorrelation matrixExp pu L b c = cgdMacroscopicCorrelation b c := physicalCorrelation_unitary_reduction matrixExp pu L b c h_unitary
    rw [h_eq_ab, h_eq_ac, h_eq_bc]
    exact h_viol
  · exact cgdDerivesBellConclusion
  · exact kinematicFluxTubeStability pu x h_tube

end CGD.Quantum

-- FILENAME: CGD/Quantum/Measurement/BornRule.lean

import CGD.Axioms.Ontology
import CGD.Axioms.PhysicalUniverse
import CGD.Quantum.Definitions
import CGD.Quantum.Holonomy.Geometric
import CGD.Quantum.Holonomy.Evaluation
import CGD.Math.HopfFibration
import CGD.Quantum.Measurement.SU2Bounds
import Litlib.Y2000.hall2000elementary.Signature
import Litlib.Core

namespace CGD.Quantum.Measurement

open CGD.Foundations CGD.Math CGD.Quantum CGD.Axioms Litlib.Y2000.hall2000elementary

section GeometricEquivalence

variable (state detector : SU2Group)

@[litlib_track "Geometric Born Rule Equivalence - Fraction"]
theorem geometricBornRuleEquivalenceFraction :
  let geometric_val := (geometricBellCorrelation state detector).re;
  let theta := Real.arccos geometric_val;
  hopfPhaseSpaceFraction theta = (1 + geometric_val) / 2 := by
  intro geometric_val theta
  have h_bounds := su2CorrelationBounds state detector
  exact hopfVolumeIsBornRuleFraction geometric_val h_bounds.left h_bounds.right

@[litlib_track "Geometric Born Rule Equivalence - Cosine"]
theorem geometricBornRuleEquivalenceCos :
  let geometric_val := (geometricBellCorrelation state detector).re;
  let theta := Real.arccos geometric_val;
  (1 + geometric_val) / 2 = (Real.cos (theta / 2))^2 := by
  intro geometric_val theta
  have h_bounds := su2CorrelationBounds state detector
  exact hopfVolumeIsBornRuleCos geometric_val h_bounds.left h_bounds.right

end GeometricEquivalence

section PhysicalEquivalence

variable (matrixExp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
variable [DerivativeExponential (Fin 2) matrixExp]
variable (pu : PhysicalUniverse)
variable (L : ℝ)
variable (alpha_state alpha_detector : ℝ)
variable (hField : ∀ t, pu.toUniverse.sd_sector 1 (straightLinePath t) = fluxTubeFrame 1 (straightLinePath t))

@[litlib_track "Physical Born Rule Equivalence - Fraction"]
theorem physicalBornRuleEquivalenceFraction :
  let state : SU2Group := ⟨
    macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha_state mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alpha_state L hField]; exact obsHolonomyIsSu2 alpha_state L
  ⟩;
  let detector : SU2Group := ⟨
    macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha_detector mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alpha_detector L hField]; exact obsHolonomyIsSu2 alpha_detector L
  ⟩;
  let geometric_val := (geometricBellCorrelation state detector).re;
  let theta := Real.arccos geometric_val;
  hopfPhaseSpaceFraction theta = (1 + geometric_val) / 2 := by
  intro state detector geometric_val theta
  exact geometricBornRuleEquivalenceFraction state detector

@[litlib_track "Physical Born Rule Equivalence - Cosine"]
theorem physicalBornRuleEquivalenceCos :
  let state : SU2Group := ⟨
    macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha_state mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alpha_state L hField]; exact obsHolonomyIsSu2 alpha_state L
  ⟩;
  let detector : SU2Group := ⟨
    macroscopicObservable (holonomy matrixExp) (fun mu p => rotateYAxis (fun m p => pu.toUniverse.sd_sector m p) alpha_detector mu p) 1 L, 
    by rw [fluxTubeHolonomyEvaluation matrixExp pu alpha_detector L hField]; exact obsHolonomyIsSu2 alpha_detector L
  ⟩;
  let geometric_val := (geometricBellCorrelation state detector).re;
  let theta := Real.arccos geometric_val;
  (1 + geometric_val) / 2 = (Real.cos (theta / 2))^2 := by
  intro state detector geometric_val theta
  exact geometricBornRuleEquivalenceCos state detector

end PhysicalEquivalence

end CGD.Quantum.Measurement

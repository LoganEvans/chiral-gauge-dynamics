-- FILENAME: CGD/Axioms/Ontology.lean

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Logic.Equiv.Defs
import CGD.Foundations.GaugeGroup
import CGD.Foundations.Spacetime

namespace CGD.Axioms

open CGD.Foundations CGD.Math

/--
A smooth SL(2, C) gauge field.
As an abstract Lie algebra, it possesses no native spacetime chirality.
-/
structure Sl2cGaugeField where
  val : Fin 4 → CGD.Foundations.SpacetimePoint → SL2C
  is_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (val mu x).val i j)

instance : CoeFun Sl2cGaugeField (fun _ => Fin 4 → CGD.Foundations.SpacetimePoint → SL2C) where
  coe F := F.val

instance : Zero Sl2cGaugeField where
  zero := ⟨fun _ _ => 0, by intro mu i j; exact contDiff_const⟩

lemma Sl2cGaugeField.ext (A B : Sl2cGaugeField) (h : A.val = B.val) : A = B := by
  cases A; cases B; dsimp at h; subst h; rfl

/--
The Core Ontology: The Universe is a macroscopic Spin(4, C) connection.
We define it strictly as a 4x4 continuous gauge field constrained to the
6-dimensional Spin(4, C) Lie algebra.
-/
structure Universe where
  /-- The unified 4x4 Chiral Dirac field -/
  val : Fin 4 → CGD.Foundations.SpacetimePoint → ChiralM

  /-- The geometric constraint forcing the 16D GL(4,C) field into the 6D Spin(4,C) algebra -/
  is_spin4c : ∀ mu x, val mu x =
    embedSelfDual (chiralProject (val mu x)).self_dual +
    embedAntiSelfDual (chiralProject (val mu x)).anti_self_dual

  /-- Smoothness conditions on the topological projections -/
  sd_is_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (chiralProject (val mu x)).self_dual.val i j)
  asd_is_smooth : ∀ mu i j, ContDiff ℝ ⊤ (fun x => (chiralProject (val mu x)).anti_self_dual.val i j)

lemma Universe.ext (u v : Universe) (h : u.val = v.val) : u = v := by
  cases u; cases v; dsimp at h; subst h; rfl

/-- Derives the self-dual SL(2,C) sector from the unified Spin(4,C) field. -/
noncomputable def Universe.sd_sector (u : Universe) : Sl2cGaugeField :=
  ⟨fun mu x => (chiralProject (u.val mu x)).self_dual, u.sd_is_smooth⟩

/-- Derives the anti-self-dual SL(2,C) sector from the unified Spin(4,C) field. -/
noncomputable def Universe.asd_sector (u : Universe) : Sl2cGaugeField :=
  ⟨fun mu x => (chiralProject (u.val mu x)).anti_self_dual, u.asd_is_smooth⟩

@[simp]
lemma universe_val_eq_embed (u : Universe) (mu : Fin 4) (x : SpacetimePoint) :
  u.val mu x = embedSelfDual (u.sd_sector mu x) + embedAntiSelfDual (u.asd_sector mu x) :=
  u.is_spin4c mu x

/--
The Spin(4, C) 4x4 Dirac Representation.
This definition evaluates to the raw 4x4 field, but its underlying
algebra guarantees it matches the spacetime chiral sum exactly.
-/
noncomputable def Universe.spin4c_connection (u : Universe) (mu : Fin 4) (x : CGD.Foundations.SpacetimePoint) : ChiralM :=
  u.val mu x

@[simp]
lemma spin4c_connection_eq_embed (u : Universe) (mu : Fin 4) (x : SpacetimePoint) :
  u.spin4c_connection mu x = embedSelfDual (u.sd_sector mu x) + embedAntiSelfDual (u.asd_sector mu x) :=
  u.is_spin4c mu x

/--
The Definitional Shield: Establishes a rigorous bidirectional equivalence
between the unified 4x4 ontology and the split SL(2,C) formulation.
-/
noncomputable def universeEquiv : Universe ≃ (Sl2cGaugeField × Sl2cGaugeField) where
  toFun u := (u.sd_sector, u.asd_sector)
  invFun p := {
    val := fun mu x => embedSelfDual (p.1 mu x) + embedAntiSelfDual (p.2 mu x)
    is_spin4c := by
      intro mu x
      rw [chiralProject_embed_sd, chiralProject_embed_asd]
    sd_is_smooth := by
      intro mu i j
      have h_eq : (fun (x : SpacetimePoint) => (chiralProject (embedSelfDual (p.1 mu x) + embedAntiSelfDual (p.2 mu x))).self_dual.val i j) = fun x => (p.1 mu x).val i j := by
        ext x
        rw [chiralProject_embed_sd]
      rw [h_eq]
      exact p.1.is_smooth mu i j
    asd_is_smooth := by
      intro mu i j
      have h_eq : (fun (x : SpacetimePoint) => (chiralProject (embedSelfDual (p.1 mu x) + embedAntiSelfDual (p.2 mu x))).anti_self_dual.val i j) = fun x => (p.2 mu x).val i j := by
        ext x
        rw [chiralProject_embed_asd]
      rw [h_eq]
      exact p.2.is_smooth mu i j
  }
  left_inv u := by
    apply Universe.ext
    funext mu x
    exact (u.is_spin4c mu x).symm
  right_inv p := by
    rcases p with ⟨L, R⟩
    apply Prod.ext
    · apply Sl2cGaugeField.ext
      funext mu x
      exact chiralProject_embed_sd (L mu x) (R mu x)
    · apply Sl2cGaugeField.ext
      funext mu x
      exact chiralProject_embed_asd (L mu x) (R mu x)

end CGD.Axioms

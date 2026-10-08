import Mettapedia.TypeTheory.ContextualCorrectedBaseLift

/-!
# Dependent controls for cartesian display factorization

The positive factor retains a supplied bounded witness while its base moves
from n to n+1. The negative control has a valid display substitution but the
wrong base movement, so no factor can recover it along that requested lift.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualDisplayCartesianControls

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualDisplayCartesianFactor

abbrev source : TypeOver familiesCwf Nat := ⟨fun n => Fin ((n + 1) + 1)⟩
abbrev target : TypeOver familiesCwf Nat := ⟨fun n => Fin (n + 1)⟩
def successor : Nat → Nat := fun n => n + 1

def supplied : (Σ n : Nat, Fin ((n + 1) + 1)) → Σ n : Nat, Fin (n + 1) :=
  fun pair => ⟨pair.1 + 1, pair.2⟩

theorem supplied_over :
    familiesCwf.compS (familiesCwf.wk target.val) supplied =
      familiesCwf.compS successor (familiesCwf.wk source.val) := rfl

abbrev actualFactor : source ⟶ TypeOver.reindexObject successor target :=
  factor (C := familiesCwf) (A := source) (B := target) successor supplied supplied_over

/-- Complete generic-variable recovery fixes the factor; the witness is
not replaced with an existential choice. -/
theorem actualFactor_is_identity : actualFactor = 𝟙 source :=
  (factor_unique (C := familiesCwf) (A := source) (B := target) successor supplied supplied_over (𝟙 source) rfl).symm

theorem supplied_recovers_every_pair :
    familiesCwf.compS (TypeOver.extensionSubstitution successor target.val)
      actualFactor.substitution = supplied := factor_composes (C := familiesCwf) (A := source) (B := target) successor supplied supplied_over

theorem actualFactor_readout (n : Nat) (witness : Fin ((n + 1) + 1)) :
    actualFactor.substitution ⟨n, witness⟩ = ⟨n, witness⟩ := by
  rw [actualFactor_is_identity]
  rfl

theorem actualFactor_retains_one :
    (actualFactor.substitution ⟨0, ⟨1, by decide⟩⟩).2.val = 1 := by
  rw [actualFactor_readout]

theorem supplied_base_is_nonidentity : successor ≠ id := by
  intro equal
  have atZero := congrFun equal 0
  exact Nat.zero_ne_one atZero.symm

abbrev unchanged : (Σ n : Nat, Fin (n + 1)) → Σ n : Nat, Fin (n + 1) := id

/-- A valid complete display map cannot be factored along an unrelated
base map. Its first projection gives the obstruction. -/
theorem wrong_base_has_no_factor
    (candidate : target ⟶ TypeOver.reindexObject successor target) :
    familiesCwf.compS (TypeOver.extensionSubstitution successor target.val)
      candidate.substitution ≠ unchanged := by
  intro computed
  have over := factorization_implies_over (C := familiesCwf) (A := target) (B := target) successor unchanged candidate computed
  have atZero := congrFun over (⟨0, ⟨0, by decide⟩⟩ : Σ n : Nat, Fin (n + 1))
  exact Nat.zero_ne_one atZero

/-- The corrected cartesian lift agrees with the chosen identity cell,
including its independently proved comprehension square. -/
theorem corrected_identity_agrees :
    ContextualCorrectedBaseLift.lift (𝟙 (PseudoCwfMorphism.identity
      familiesCwfWithTerminal).base) =
        CorrectedTransformationData.identity (PseudoCwfMorphism.identity familiesCwfWithTerminal) :=
  ContextualCorrectedBaseLift.lift_identity _

end Mettapedia.TypeTheory.ContextualDisplayCartesianControls

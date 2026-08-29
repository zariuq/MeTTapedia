import Mettapedia.GSLT.Core.ObservationControlContract
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ReductionChoiceNormalFormBoundary

/-!
# Prime choice dispatch is derived from observation demand

The validated Prime choice canary produces two distinct normal occurrences.
This module feeds that exact family into the generic observation-control
contract.  A complete bag admits permutation-invariant bulk activation; a
first-witness observer remains controlled; and an ordered stream rejects the
swapped activation.  The evaluator therefore derives control from the
consumer's observation and certificates rather than assigning one global
search order to choice.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace ChoiceDemandControlBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Cybernetics
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationControlContract.Contract
open Mettapedia.GSLT.Core.ObservationIndexedPruning
open ReductionChoiceNormalFormBoundary

def appendOccurrence (state : List Pattern) (occurrence : Pattern) :
    List Pattern :=
  state ++ [occurrence]

def bagObserver : Observer (List Pattern) (Multiset Pattern) where
  observe := fun occurrences => (occurrences : Multiset Pattern)

def firstObserver : Observer (List Pattern) (Option Pattern) where
  observe := List.head?

def orderedObserver : Observer (List Pattern) (List Pattern) :=
  Observer.identity (List Pattern)

def completeChoice : Contract Pattern Unit (Multiset Pattern) where
  observer := bagObserver
  demand := { completion := .completeBag }

def firstChoice : Contract Pattern Unit (Option Pattern) where
  observer := firstObserver
  demand := { completion := .first }

def orderedChoice : Contract Pattern Unit (List Pattern) where
  observer := orderedObserver
  demand := { completion := .orderedStream }

private theorem activateAll_appendOccurrence (initial batch : List Pattern) :
    activateAll appendOccurrence initial batch = initial ++ batch := by
  induction batch generalizing initial with
  | nil => simp [activateAll]
  | cons occurrence tail inductionHypothesis =>
      change activateAll appendOccurrence
        (initial ++ [occurrence]) tail = initial ++ occurrence :: tail
      rw [inductionHypothesis]
      simp [List.append_assoc]

/-- The exact choice occurrence family is serializable at complete-bag
observation. -/
theorem choice_serializable_at_bag :
    SerializableAt bagObserver.observe appendOccurrence []
      [leftDemo, rightDemo] := by
  intro ordering permutation
  rw [activateAll_appendOccurrence, activateAll_appendOccurrence]
  simp only [List.nil_append, bagObserver]
  exact Quot.sound permutation

/-- The same two occurrences are not serializable at exact stream
observation: authored order remains visible. -/
theorem choice_not_serializable_at_ordered_stream :
    ¬ SerializableAt orderedObserver.observe appendOccurrence []
      [leftDemo, rightDemo] := by
  intro serializable
  have swapped := serializable [rightDemo, leftDemo]
    (List.Perm.swap leftDemo rightDemo [])
  rw [activateAll_appendOccurrence, activateAll_appendOccurrence] at swapped
  simp [orderedObserver] at swapped
  exact left_ne_right (List.cons.inj swapped.symm).1

def completeEvidence :
    BatchEvidence completeChoice appendOccurrence []
      [leftDemo, rightDemo] :=
  .serializable choice_serializable_at_bag

def firstEvidence :
    BatchEvidence firstChoice appendOccurrence []
      [leftDemo, rightDemo] :=
  .singletonOnly

def orderedEvidence :
    BatchEvidence orderedChoice appendOccurrence []
      [leftDemo, rightDemo] :=
  .singletonOnly

/-- Complete occurrence-bag demand plus exact serializability earns bulk. -/
theorem complete_choice_dispatches_bulk :
    (dispatchCertified completeChoice .general completeEvidence).activation =
      .bulk := by
  exact completeBag_serializable_dispatches_bulk completeChoice rfl
    choice_serializable_at_bag

/-- First-witness demand does not preselect a branch; the two-path scope stays
under controlled activation. -/
theorem first_choice_remains_controlled :
    (dispatchCertified firstChoice .general firstEvidence).activation =
      .controlled :=
  rfl

/-- Exact stream observation also stays controlled without a valid batch
certificate. -/
theorem ordered_choice_remains_controlled :
    (dispatchCertified orderedChoice .general orderedEvidence).activation =
      .controlled :=
  rfl

/-- The same discovered family therefore receives different lawful plans
solely from its consuming observation. -/
theorem choice_dispatch_is_observation_indexed :
    (dispatchCertified completeChoice .general completeEvidence).activation =
        .bulk ∧
      (dispatchCertified firstChoice .general firstEvidence).activation =
        .controlled ∧
      (dispatchCertified orderedChoice .general orderedEvidence).activation =
        .controlled :=
  ⟨complete_choice_dispatches_bulk, first_choice_remains_controlled,
    ordered_choice_remains_controlled⟩

#print axioms choice_serializable_at_bag
#print axioms choice_not_serializable_at_ordered_stream
#print axioms complete_choice_dispatches_bulk
#print axioms first_choice_remains_controlled
#print axioms ordered_choice_remains_controlled
#print axioms choice_dispatch_is_observation_indexed

end ChoiceDemandControlBoundary
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower

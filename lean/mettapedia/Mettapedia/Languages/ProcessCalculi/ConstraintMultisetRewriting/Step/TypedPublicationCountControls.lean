import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationOfferedCounts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationCoherenceModal
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationRunTransportControls

/-!
# Origin counts and raw-code boundaries on the vector publication

Two indexed offers of the same actual application reach the same successor
but remain two events. Helper transport preserves those events. Collapsing
their origins to a singleton loses the counting observation, and a raw
variable-position observation distinguishes the exchanged source frames.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CountControls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.VectorAppend
open LogicOverTheStep.CountingModalities
open OfferedCounts RunTransportControls

def twoOffers : Fin 2 → Application vlevels Nat callState := fun _ => Vector.application
def oneOffer : Fin 1 → Application vlevels Nat callState := fun _ => Vector.application

def firstEdge : (span twoOffers).Edge := ⟨0, Vector.native_admitted⟩
def secondEdge : (span twoOffers).Edge := ⟨1, Vector.native_admitted⟩

theorem distinct_events_same_successor :
    firstEdge ≠ secondEdge ∧ (span twoOffers).target firstEdge = (span twoOffers).target secondEdge := by
  refine ⟨?_, rfl⟩
  intro same
  have indices := congrArg Subtype.val same
  change (0 : Fin 2) = 1 at indices
  exact (by decide : (0 : Fin 2) ≠ 1) indices

theorem two_events_publish_zero :
    countingDiamond (span twoOffers) 2 (fun state => 0 ∈ state.present) callState := by
  classical
  refine ⟨{firstEdge, secondEdge}, ?_, ?_⟩
  · simp [distinct_events_same_successor.1]
  · intro edge member
    have published : (span twoOffers).target edge = Vector.published := rfl
    refine ⟨rfl, ?_⟩
    rw [published]
    change 0 ∈ Vector.published.present
    rw [Vector.published_occurrences]
    exact Finset.mem_singleton_self _

theorem exchanged_two_events_publish_zero :
    countingDiamond (span (OfferedCounts.move stateIso twoOffers)) 2
      (fun state => 0 ∈ state.present) reversedState :=
  (counts stateIso twoOffers _ (CoherenceModal.occurrence_invariant 0) 2).mp two_events_publish_zero

theorem collapsing_origins_loses_count :
    ¬ countingDiamond (span oneOffer) 2 (fun state => 0 ∈ state.present) callState := by
  rintro ⟨chosen, cardinality, _⟩
  obtain ⟨first, _, second, _, different⟩ := Finset.one_lt_card.mp
    (show 1 < chosen.card by omega)
  apply different
  apply Subtype.ext
  exact Subsingleton.elim _ _

theorem raw_code_not_invariant :
    (callState.label 0).2.code ≠ (reversedState.label 0).2.code := by
  change (.var ⟨0, by decide⟩ : Tower.Tm 3) ≠ exchange.hom.substitution 0
  rw [exchange_changes_parameter_position]
  intro same
  have indices := congrArg Fin.val (Tm.var.inj same)
  cases indices

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CountControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CountControls.exchanged_two_events_publish_zero
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CountControls.collapsing_origins_loses_count

import Mettapedia.GSLT.LanguageDef.GSLTILEvidenceWorlds
import Mettapedia.GSLT.Dynamics.ObservationPolicyFactorization

/-!
# Capability-indexed observation of ambiguous GSLT-IL worlds

An evidence-valued GSLT-IL elaboration profile already retains two independent
kinds of multiplicity: distinct internal outcomes and distinct derivation
histories for one outcome.  This module makes the observer boundary explicit.

The full world observation retains both coordinates.  The visible-outcome
observation forgets derivation history but retains every enumerated semantic
alternative.  The cardinality observation forgets even which alternatives
were present.  Selection is a downstream policy, supported by a readout only
when it is constant on that readout's fibres.

Thus ambiguity is not an error and is not resolved by the interlingua itself.
Different consumers may deliberately observe different quotients of the same
retained world history.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.MultiworldObservation

open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
open Mettapedia.GSLT.LanguageDef.GSLTIL.OccurrenceCells
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uDecision

variable {program : Program} (profile : EvidenceWorlds.Profile program)
  (command : profile.Command)

/-! ## Three observation capabilities over one retained world history -/

/-- Retain the exact ordered enumeration of outcome/history worlds. -/
def worlds : ObservationDiscipline (profile.World command) where
  collection :=
    { Container := List (profile.World command)
      collect := fun events => some events }
  Value := List (profile.World command)
  readout := id

/-- Retain every visible internal outcome and its multiplicity, while
forgetting which derivation history justified each occurrence. -/
def outcomes : ObservationDiscipline (profile.World command) :=
  (worlds profile command).mapValue (List.map Sigma.fst)

/-- Retain only the number of enumerated worlds.  This can observe the degree
of branching but cannot identify the alternatives or their histories. -/
def cardinality : ObservationDiscipline (profile.World command) :=
  (worlds profile command).mapValue List.length

@[simp] theorem worlds_observe (events : List (profile.World command)) :
    (worlds profile command).observe events = some events :=
  rfl

@[simp] theorem outcomes_observe (events : List (profile.World command)) :
    (outcomes profile command).observe events =
      some (events.map Sigma.fst) :=
  rfl

@[simp] theorem cardinality_observe (events : List (profile.World command)) :
    (cardinality profile command).observe events = some events.length :=
  rfl

/-- The full world readout retains every distinction in its witness
container. -/
theorem worlds_faithful : (worlds profile command).Faithful := by
  intro first second equal
  exact equal

/-! ## Exact boundaries between semantic and derivational ambiguity -/

/-- History thinness is exactly what makes the projection from a complete
world to its visible internal outcome injective. -/
theorem worldOutcome_injective_of_historyThin
    (thin : profile.HistoryThin) :
    Function.Injective (Sigma.fst : profile.World command → Pattern) := by
  rintro ⟨firstInternal, firstHistory⟩ ⟨secondInternal, secondHistory⟩ same
  cases same
  have historyEqual : firstHistory = secondHistory :=
    (thin command firstInternal).allEq _ _
  cases historyEqual
  rfl

/-- The outcome observer is faithful precisely on profiles where fixed-outcome
history fibres are thin.  Semantic outcome ambiguity may remain: distinct
internal outcomes are still retained and distinguished. -/
theorem outcomes_faithful_of_historyThin
    (thin : profile.HistoryThin) :
    (outcomes profile command).Faithful := by
  exact List.map_injective_iff.mpr
    (worldOutcome_injective_of_historyThin profile command thin)

/-- Two distinct histories of one visible outcome collide under the outcome
readout.  This is the formal multiworld reason not to replace retained worlds
by their visible terms. -/
theorem outcomes_lossy_of_history_collision
    (first second : profile.World command)
    (distinct : first ≠ second)
    (sameOutcome : first.1 = second.1) :
    (outcomes profile command).Lossy := by
  apply ObservationDiscipline.lossy_of_collision
    (discipline := outcomes profile command)
    (first := [first]) (second := [second])
  · intro singletonEqual
    apply distinct
    injection singletonEqual
  · change [first.1] = [second.1]
    rw [sameOutcome]

/-- Cardinality cannot distinguish any two singleton alternatives, even when
their visible meanings differ. -/
theorem cardinality_lossy_of_distinct_worlds
    (first second : profile.World command)
    (distinct : first ≠ second) :
    (cardinality profile command).Lossy := by
  apply ObservationDiscipline.lossy_of_collision
    (discipline := cardinality profile command)
    (first := [first]) (second := [second])
  · intro singletonEqual
    apply distinct
    injection singletonEqual
  · rfl

/-- A decision that distinguishes two histories with the same visible outcome
cannot be implemented from the outcome readout.  Selection is therefore an
additional policy capability, not a hidden part of elaboration semantics. -/
theorem history_sensitive_policy_not_supported
    (first second : profile.World command)
    (sameOutcome : first.1 = second.1)
    (policy : List (profile.World command) → Decision)
    (differentDecision : policy [first] ≠ policy [second]) :
    ¬ (outcomes profile command).SupportsPolicy policy := by
  apply ObservationDiscipline.not_supportsPolicy_of_collision
    (discipline := outcomes profile command)
    (first := [first]) (second := [second]) policy
  · change [first.1] = [second.1]
    rw [sameOutcome]
  · exact differentDecision

/-- Once a profile earns exact representation, its history fibres are thin,
so visible outcomes are sufficient to retain the complete enumerated world
history.  The representation is the license; this theorem does not make the
ambient raw elaboration functional. -/
theorem outcomes_faithful_of_representation
    (representation :
      Mettapedia.GSLT.LooseRelationEquipment.Representation profile.related) :
    (outcomes profile command).Faithful := by
  have criterion :=
    (profile.representable_iff_covered_outcomeDeterminate_historyThin).mp
      ⟨representation⟩
  exact outcomes_faithful_of_historyThin profile command criterion.2.2

/-! ## Authored positive and negative controls -/

/-- Recover the authored occurrence cell retained by an occurrence-profile
world. -/
def occurrenceCellOfWorld
    {program : Program} {_source _target : Boundary}
    (world : (occurrenceProfile program _source _target).World ()) :
    OccurrenceWireCell program _source _target := by
  rcases world with ⟨internal, history⟩
  cases history with
  | ofCell cell => exact cell

/-- There is an authored GSLT-IL profile whose full world observer is faithful
while its visible-outcome observer is lossy because two distinct occurrence
histories justify the same internal command. -/
theorem exists_authored_multiworld_observation_boundary :
    ∃ (program : Program) (profile : EvidenceWorlds.Profile program)
      (command : profile.Command),
      (worlds profile command).Faithful ∧
        (outcomes profile command).Lossy := by
  obtain ⟨program, source, target, first, second, distinct, _sameWire,
      _covered, _outcomeDeterminate, _notRepresentable⟩ :=
    exists_authored_occurrence_history_nonrepresentable
  let profile := occurrenceProfile program source target
  let firstWorld : profile.World () :=
    ⟨source.2, OccurrenceHistory.ofCell first⟩
  let secondWorld : profile.World () :=
    ⟨source.2, OccurrenceHistory.ofCell second⟩
  have distinctWorld : firstWorld ≠ secondWorld := by
    intro same
    apply distinct
    exact congrArg occurrenceCellOfWorld same
  refine ⟨program, profile, (), worlds_faithful profile (), ?_⟩
  exact outcomes_lossy_of_history_collision profile () firstWorld secondWorld
    distinctWorld rfl

#print axioms worlds_faithful
#print axioms worldOutcome_injective_of_historyThin
#print axioms outcomes_faithful_of_historyThin
#print axioms outcomes_lossy_of_history_collision
#print axioms cardinality_lossy_of_distinct_worlds
#print axioms history_sensitive_policy_not_supported
#print axioms outcomes_faithful_of_representation
#print axioms exists_authored_multiworld_observation_boundary

end Mettapedia.GSLT.LanguageDef.GSLTIL.MultiworldObservation

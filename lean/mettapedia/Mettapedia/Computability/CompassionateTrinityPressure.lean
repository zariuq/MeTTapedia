import Mettapedia.Computability.ObservationCarrierTrinity
import Mettapedia.Cybernetics.ReflexiveValence
import Mettapedia.Cybernetics.StructurePreservingRepair
import Mettapedia.GSLT.Core.OpenTotalityObservation

/-!
# Compassionate observation pressures on the computational trinity

This module asks which observation carriers can retain finite signals needed
by a relational account of valence.  It deliberately proves weaker facts than
a complete ethics: adjacent pain observations are not identified with
suffering, and repeated pain is not identified with its intensity.  They are
small necessary signals which already discriminate the carriers.

Two impossibility results follow.

* Forgetting an ordered history to a bag erases adjacency, so a bag predicate
  cannot in general recover even a finite propagation-shaped signal.
* Forgetting an occurrence bag to a set erases repetition, so a set predicate
  cannot in general recover even a two-occurrence harm signal.

The same witnesses show that the corresponding goals do not descend through
the coarse observers.  Open-totality contributes an independent boundary:
budget exhaustion with no observed pain does not establish closed absence.
Finally, a repair can eliminate represented pain while preserving subject
continuity and a recipient value, whereas deleting the subject or overwriting
that value fails the preservation obligation even though it also removes the
misfit.

Together these results constrain a cognitive language without selecting one
surface syntax: order, multiplicity, completion evidence, and preserved
identity must remain available in some typed or proof-relevant layer.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.CompassionateTrinityPressure

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.MultiscaleGoal
open Mettapedia.Cybernetics.StructurePreservingRepair
open Mettapedia.GSLT.Core.OpenTotalityObservation

/-- A deliberately small observation alphabet.  It is a readout, not an
ontology of the underlying process. -/
inductive ValenceObservation where
  | pain
  | joy
  | neutral
  deriving DecidableEq

/-- A minimal ordered signal: two observed pain events are adjacent. -/
def HasAdjacentPain : List ValenceObservation -> Prop
  | .pain :: .pain :: _ => True
  | _ :: tail => HasAdjacentPain tail
  | [] => False

/-- A minimal occurrence signal: at least two pain observations survive in
the bag. -/
def HasRepeatedPain (observations : Multiset ValenceObservation) : Prop :=
  2 <= observations.count .pain

def clusteredHistory : List ValenceObservation :=
  [.pain, .pain, .joy]

def separatedHistory : List ValenceObservation :=
  [.pain, .joy, .pain]

theorem clustered_hasAdjacentPain : HasAdjacentPain clusteredHistory := by
  simp [clusteredHistory, HasAdjacentPain]

theorem separated_not_hasAdjacentPain :
    ¬ HasAdjacentPain separatedHistory := by
  simp [separatedHistory, HasAdjacentPain]

/-- The two histories have exactly the same occurrence bag. -/
theorem histories_have_same_bag :
    (clusteredHistory : Multiset ValenceObservation) =
      (separatedHistory : Multiset ValenceObservation) := by
  decide

/-- No predicate of the bag alone recovers ordered adjacency for all
histories. -/
theorem no_bag_predicate_recovers_adjacentPain :
    ¬ exists predicate : Multiset ValenceObservation -> Prop,
      forall history,
        HasAdjacentPain history <-> predicate (history : Multiset ValenceObservation) := by
  rintro ⟨predicate, recovers⟩
  have clusteredBag :
      predicate (clusteredHistory : Multiset ValenceObservation) :=
    (recovers clusteredHistory).mp clustered_hasAdjacentPain
  have separatedBag :
      predicate (separatedHistory : Multiset ValenceObservation) := by
    rw [← histories_have_same_bag]
    exact clusteredBag
  exact separated_not_hasAdjacentPain
    ((recovers separatedHistory).mpr separatedBag)

def repeatedPainBag : Multiset ValenceObservation :=
  {.pain, .pain}

def singlePainBag : Multiset ValenceObservation :=
  {.pain}

theorem repeatedPainBag_hasRepeatedPain :
    HasRepeatedPain repeatedPainBag := by
  simp [HasRepeatedPain, repeatedPainBag]

theorem singlePainBag_not_hasRepeatedPain :
    ¬ HasRepeatedPain singlePainBag := by
  simp [HasRepeatedPain, singlePainBag]

/-- The repeated and single bags have the same extensional set. -/
theorem pain_bags_have_same_set :
    repeatedPainBag.toFinset = singlePainBag.toFinset := by
  decide

/-- No predicate of the extensional set alone recovers occurrence
multiplicity for all bags. -/
theorem no_set_predicate_recovers_repeatedPain :
    ¬ exists predicate : Finset ValenceObservation -> Prop,
      forall observations,
        HasRepeatedPain observations <-> predicate observations.toFinset := by
  rintro ⟨predicate, recovers⟩
  have repeatedSet : predicate repeatedPainBag.toFinset :=
    (recovers repeatedPainBag).mp repeatedPainBag_hasRepeatedPain
  have singleSet : predicate singlePainBag.toFinset := by
    rw [← pain_bags_have_same_set]
    exact repeatedSet
  exact singlePainBag_not_hasRepeatedPain
    ((recovers singlePainBag).mpr singleSet)

/-! ## Observer-relative visibility -/

/-- The bag observer forgets history order. -/
def bagObserver : Observer (List ValenceObservation)
    (Multiset ValenceObservation) where
  observe := fun history => (history : Multiset ValenceObservation)

/-- Histories bearing the finite propagation-shaped signal. -/
def adjacencyProblem : ProblemSpace (List ValenceObservation) where
  preferredRegion := {history | HasAdjacentPain history}

/-- Full ordered observation can represent the adjacency goal. -/
theorem adjacency_visible_to_stream :
    adjacencyProblem.GoalVisibleAt
      (Observer.identity (List ValenceObservation)) := by
  exact ⟨{history | HasAdjacentPain history}, fun _ => Iff.rfl⟩

/-- The same goal cannot descend to the bag face. -/
theorem adjacency_not_visible_to_bag :
    ¬ adjacencyProblem.GoalVisibleAt bagObserver := by
  intro visible
  have invariant :=
    (adjacencyProblem.goalVisibleAt_iff_invariantOnFibres bagObserver).mp visible
  have contradiction := invariant clusteredHistory separatedHistory
    histories_have_same_bag
  exact separated_not_hasAdjacentPain
    (contradiction.mp clustered_hasAdjacentPain)

/-- The set observer forgets occurrence multiplicity. -/
def setObserver : Observer (Multiset ValenceObservation)
    (Finset ValenceObservation) where
  observe := Multiset.toFinset

/-- Bags carrying a repeated-pain occurrence signal. -/
def repetitionProblem : ProblemSpace (Multiset ValenceObservation) where
  preferredRegion := {observations | HasRepeatedPain observations}

/-- Full bag observation can represent the repetition goal. -/
theorem repetition_visible_to_bag :
    repetitionProblem.GoalVisibleAt
      (Observer.identity (Multiset ValenceObservation)) := by
  exact ⟨{observations | HasRepeatedPain observations}, fun _ => Iff.rfl⟩

/-- The same goal cannot descend to the set face. -/
theorem repetition_not_visible_to_set :
    ¬ repetitionProblem.GoalVisibleAt setObserver := by
  intro visible
  have invariant :=
    (repetitionProblem.goalVisibleAt_iff_invariantOnFibres setObserver).mp visible
  have contradiction := invariant repeatedPainBag singlePainBag
    pain_bags_have_same_set
  exact singlePainBag_not_hasRepeatedPain
    (contradiction.mp repeatedPainBag_hasRepeatedPain)

/-! ## Open-world absence -/

abbrev EthicalObservation :=
  Observation ValenceObservation Unit Nat Unit Nat Unit Unit
    (fun _ _ => False)

/-- A bounded run can observe no pain and still be merely exhausted. -/
def exhaustedSilence : EthicalObservation :=
  Observation.withoutCapture [] (.exhausted 100 ())

/-- Empty output plus resource exhaustion is not a closed absence proof. -/
theorem exhausted_silence_does_not_establish_closed_absence :
    ¬ Observation.EstablishesClosedAbsence exhaustedSilence := by
  exact Observation.exhausted_not_establishesClosedAbsence
    (CaptureAdmitted := fun _ _ => False)
    (Coverage := Unit) (Fault := Unit)
    ([] : List ValenceObservation) 100 ()

/-! ## Compassionate repair retains the subject -/

structure CareState where
  subjectPresent : Bool
  recipientValue : Bool
  activePain : Bool
  deriving DecidableEq

inductive CareChange : CareState -> CareState -> Type where
  | soothe : CareChange ⟨true, true, true⟩ ⟨true, true, false⟩
  | eraseSubject : CareChange ⟨true, true, true⟩ ⟨false, true, false⟩
  | overwriteValue : CareChange ⟨true, true, true⟩ ⟨true, false, false⟩

/-- Subject continuity and the recipient's selected value form the valued
observation; active pain is the named misfit. -/
def careProblem : Problem CareState (Bool × Bool) Unit where
  valuedObservation := {
    observe := fun state => (state.subjectPresent, state.recipientValue) }
  HasMisfit := fun state _ => state.activePain = true
  Change := CareChange

/-- Pain can be removed while preserving the represented subject and value. -/
def soothingRepair :
    Repair careProblem ⟨true, true, true⟩ ⟨true, true, false⟩ where
  evidence := .soothe
  preservesValue := rfl
  strictlyReducesMisfit := by
    rw [Set.ssubset_iff_subset_ne]
    constructor
    · intro misfit targetMisfit
      simp [Problem.misfits, careProblem] at targetMisfit
    · intro equal
      have sourceMisfit : () ∈ careProblem.misfits ⟨true, true, true⟩ := by
        simp [Problem.misfits, careProblem]
      have targetMisfit : () ∈ careProblem.misfits ⟨true, true, false⟩ := by
        rw [equal]
        exact sourceMisfit
      simp [Problem.misfits, careProblem] at targetMisfit

/-- Erasing the subject removes the represented pain but is not a
structure-preserving repair. -/
theorem erasing_subject_is_not_repair :
    careProblem.misfits ⟨false, true, false⟩ ⊂
        careProblem.misfits ⟨true, true, true⟩ /\
      ¬ Nonempty
        (Repair careProblem ⟨true, true, true⟩ ⟨false, true, false⟩) := by
  constructor
  · rw [Set.ssubset_iff_subset_ne]
    constructor
    · intro misfit targetMisfit
      simp [Problem.misfits, careProblem] at targetMisfit
    · intro equal
      have sourceMisfit : () ∈ careProblem.misfits ⟨true, true, true⟩ := by
        simp [Problem.misfits, careProblem]
      have targetMisfit : () ∈ careProblem.misfits ⟨false, true, false⟩ := by
        rw [equal]
        exact sourceMisfit
      simp [Problem.misfits, careProblem] at targetMisfit
  · rintro ⟨repair⟩
    have preserved := repair.preservesValue
    simp [careProblem] at preserved

/-- Changing what the recipient values is not a repair merely because the
new state no longer registers the old pain. -/
theorem overwriting_recipient_value_is_not_repair :
    careProblem.misfits ⟨true, false, false⟩ ⊂
        careProblem.misfits ⟨true, true, true⟩ /\
      ¬ Nonempty
        (Repair careProblem ⟨true, true, true⟩ ⟨true, false, false⟩) := by
  constructor
  · rw [Set.ssubset_iff_subset_ne]
    constructor
    · intro misfit targetMisfit
      simp [Problem.misfits, careProblem] at targetMisfit
    · intro equal
      have sourceMisfit : () ∈ careProblem.misfits ⟨true, true, true⟩ := by
        simp [Problem.misfits, careProblem]
      have targetMisfit : () ∈ careProblem.misfits ⟨true, false, false⟩ := by
        rw [equal]
        exact sourceMisfit
      simp [Problem.misfits, careProblem] at targetMisfit
  · rintro ⟨repair⟩
    have preserved := repair.preservesValue
    simp [careProblem] at preserved

end Mettapedia.Computability.CompassionateTrinityPressure

#print axioms Mettapedia.Computability.CompassionateTrinityPressure.no_bag_predicate_recovers_adjacentPain
#print axioms Mettapedia.Computability.CompassionateTrinityPressure.no_set_predicate_recovers_repeatedPain
#print axioms Mettapedia.Computability.CompassionateTrinityPressure.adjacency_not_visible_to_bag
#print axioms Mettapedia.Computability.CompassionateTrinityPressure.exhausted_silence_does_not_establish_closed_absence
#print axioms Mettapedia.Computability.CompassionateTrinityPressure.erasing_subject_is_not_repair
#print axioms Mettapedia.Computability.CompassionateTrinityPressure.overwriting_recipient_value_is_not_repair

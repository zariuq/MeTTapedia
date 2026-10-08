import Mettapedia.Algorithms.WellFoundedServices.DependencyAnalysis
import Mettapedia.Machines.RunObservation
import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation

/-!
# Trace observation boundaries

A replay checker can validate only information that an execution trace
actually exports.  This module isolates three erasures that occur at common
native trace boundaries:

* flattening a causal receipt retains event occurrences but forgets edges;
* exporting an observation without its demand annotation forgets both the
  demand role and expected type;
* reporting an external interruption without its frontier forgets the live
  states that remained when execution stopped.

The counterexamples below are constructive non-injectivity results.  They
prevent a checker from reconstructing any of these witnesses solely from the
corresponding erased observation.
-/

namespace Mettapedia.Machines

/-! ## Causal edges -/

universe uCausal

/-- One event occurrence together with its immediate causal predecessors. -/
structure CausalEvent (Event : Type uCausal) where
  event : Event
  directCauses : List Event
deriving DecidableEq, Repr

/-- A finite causal receipt.  Roots identify the events directly supporting
the published observation; `events` retains the immediate-edge relation. -/
structure CausalReceipt (Event : Type uCausal) where
  roots : List Event
  events : List (CausalEvent Event)
deriving DecidableEq, Repr

namespace CausalReceipt

/-- The occurrence-preserving support currently visible to a flattened trace.
The order and multiplicity of event occurrences survive; causal edges do not. -/
def flattenedSupport (receipt : CausalReceipt Event) : List Event :=
  receipt.events.map CausalEvent.event

/-- Boundary identities describe dependencies captured before recording
began. They are visible references, not a reconstructed earlier history. -/
def known (boundary : List Event) (receipt : CausalReceipt Event) : List Event :=
  boundary ++ receipt.flattenedSupport

/-- An event is fresh and refers only to earlier available occurrences.
Repeated predecessor slots remain repeated slots. -/
def Ordered (available : List Event) : List (CausalEvent Event) → Prop
  | [] => True
  | event :: rest => event.event ∉ available ∧
      (∀ cause ∈ event.directCauses, cause ∈ available) ∧
      Ordered (available ++ [event.event]) rest

def WellFormed (boundary : List Event) (receipt : CausalReceipt Event) : Prop :=
  boundary.Nodup ∧ Ordered boundary receipt.events ∧
    ∀ root ∈ receipt.roots, root ∈ receipt.known boundary

def checkEvents [DecidableEq Event] (available : List Event) : List (CausalEvent Event) → Bool
  | [] => true
  | event :: rest => decide (event.event ∉ available) &&
      event.directCauses.all (fun cause => decide (cause ∈ available)) &&
      checkEvents (available ++ [event.event]) rest

def check [DecidableEq Event] (boundary : List Event) (receipt : CausalReceipt Event) : Bool :=
  decide boundary.Nodup && checkEvents boundary receipt.events &&
    receipt.roots.all (fun root => decide (root ∈ receipt.known boundary))

theorem checkEvents_iff [DecidableEq Event] (available : List Event)
    (events : List (CausalEvent Event)) :
    checkEvents available events = true ↔ Ordered available events := by
  induction events generalizing available with
  | nil => simp [checkEvents, Ordered]
  | cons event rest ih => simp [checkEvents, Ordered, ih, and_assoc]

theorem check_iff [DecidableEq Event] (boundary : List Event) (receipt : CausalReceipt Event) :
    check boundary receipt = true ↔ WellFormed boundary receipt := by
  simp [check, WellFormed, checkEvents_iff, and_assoc]

theorem ordered_append (available : List Event) (first second : List (CausalEvent Event)) :
    Ordered available (first ++ second) ↔
      Ordered available first ∧ Ordered (available ++ first.map CausalEvent.event) second := by
  induction first generalizing available with
  | nil => simp [Ordered]
  | cons event rest ih => simp [Ordered, ih, List.append_assoc, and_assoc]

theorem ordered_distinct (available : List Event) (events : List (CausalEvent Event))
    (distinct : available.Nodup) (ordered : Ordered available events) :
    (available ++ events.map CausalEvent.event).Nodup := by
  induction events generalizing available with
  | nil => simpa using distinct
  | cons event rest ih =>
    rcases ordered with ⟨fresh, _, tail⟩
    have extended : (available ++ [event.event]).Nodup := by
      simp only [List.nodup_append, distinct, List.nodup_cons, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_self, true_and, List.mem_singleton]
      rintro member present other rfl rfl
      exact fresh present
    simpa only [List.map_cons, List.append_assoc, List.singleton_append] using
      ih (available ++ [event.event]) extended tail

/-- Every retained cause has a strictly smaller chronological rank. -/
theorem ordered_rank [DecidableEq Event] (available : List Event)
    (events : List (CausalEvent Event)) (ordered : Ordered available events)
    (event : CausalEvent Event) (present : event ∈ events)
    (cause : Event) (depends : cause ∈ event.directCauses) :
    (available ++ events.map CausalEvent.event).idxOf cause <
      (available ++ events.map CausalEvent.event).idxOf event.event := by
  induction events generalizing available with
  | nil => cases present
  | cons head rest ih =>
    rcases ordered with ⟨fresh, causes, tail⟩
    rcases List.mem_cons.mp present with equal | member
    · subst event
      rw [List.map_cons, List.idxOf_append_of_mem (causes cause depends),
        List.idxOf_append_of_notMem fresh]
      simpa using List.idxOf_lt_length_of_mem (causes cause depends)
    · simpa only [List.map_cons, List.append_assoc, List.singleton_append] using
        ih (available ++ [head.event]) tail member

def Direct (receipt : CausalReceipt Event) (cause effect : Event) : Prop :=
  ∃ event ∈ receipt.events, event.event = effect ∧ cause ∈ event.directCauses

theorem direct_rank [DecidableEq Event] (boundary : List Event) (receipt : CausalReceipt Event)
    (valid : WellFormed boundary receipt) {cause effect : Event}
    (edge : receipt.Direct cause effect) :
    (receipt.known boundary).idxOf cause < (receipt.known boundary).idxOf effect := by
  obtain ⟨event, present, rfl, depends⟩ := edge
  exact ordered_rank boundary receipt.events valid.2.1 event present cause depends

theorem ancestry_rank [DecidableEq Event] (boundary : List Event) (receipt : CausalReceipt Event)
    (valid : WellFormed boundary receipt) {cause effect : Event}
    (path : Relation.TransGen receipt.Direct cause effect) :
    (receipt.known boundary).idxOf cause < (receipt.known boundary).idxOf effect := by
  induction path with
  | single edge => exact direct_rank boundary receipt valid edge
  | tail path edge ih => exact ih.trans (direct_rank boundary receipt valid edge)

theorem no_causal_cycle [DecidableEq Event] (boundary : List Event) (receipt : CausalReceipt Event)
    (valid : WellFormed boundary receipt) (event : Event) :
    ¬ Relation.TransGen receipt.Direct event event := by
  intro cycle
  exact Nat.lt_irrefl _ (ancestry_rank boundary receipt valid cycle)

/-- Append one already-identified event. Rejected input leaves the original
immutable receipt available to its caller. This checks structure, not whether
the evaluator actually produced all of the stated dependency edges. -/
def appendEvent? [DecidableEq Event] (boundary : List Event) (receipt : CausalReceipt Event)
    (event : CausalEvent Event) : Option (CausalReceipt Event) :=
  if event.event ∉ receipt.known boundary ∧
      ∀ cause ∈ event.directCauses, cause ∈ receipt.known boundary then
    some { receipt with events := receipt.events ++ [event] }
  else none

theorem appendEvent?_valid [DecidableEq Event] (boundary : List Event)
    (receipt result : CausalReceipt Event) (event : CausalEvent Event)
    (valid : WellFormed boundary receipt) (accepted : appendEvent? boundary receipt event = some result) :
    WellFormed boundary result := by
  unfold appendEvent? at accepted
  split at accepted
  · rename_i allowed
    cases Option.some.inj accepted
    refine ⟨valid.1, ?_, ?_⟩
    · apply (ordered_append boundary receipt.events [event]).mpr
      exact ⟨valid.2.1, allowed.1, allowed.2, trivial⟩
    · intro root present
      have old := valid.2.2 root present
      simpa only [known, flattenedSupport, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc] using
        (List.mem_append_left [event.event] old)
  · cases accepted

/-- Query the retained immediate predecessors of one occurrence. A missing
node returns `none`; an observed root with no predecessors returns `some []`. -/
def causes? [DecidableEq Event] (receipt : CausalReceipt Event) (identity : Event) :
    Option (List Event) :=
  (receipt.events.find? (fun event => decide (event.event = identity))).map CausalEvent.directCauses

theorem causes?_sound [DecidableEq Event] (receipt : CausalReceipt Event)
    (identity : Event) (causes : List Event) (found : receipt.causes? identity = some causes) :
    ∃ event ∈ receipt.events, event.event = identity ∧ event.directCauses = causes := by
  obtain ⟨event, selected, same⟩ := Option.map_eq_some_iff.mp found
  exact ⟨event, List.mem_of_find?_eq_some selected,
    of_decide_eq_true (List.find?_some
      (p := fun candidate : CausalEvent Event => decide (candidate.event = identity)) selected), same⟩

namespace Controls

def shared : CausalReceipt Nat :=
  ⟨[2, 3], [⟨1, []⟩, ⟨2, [1]⟩, ⟨3, [1]⟩]⟩

def erasedSharing : CausalReceipt Nat :=
  ⟨[2, 3], [⟨1, []⟩, ⟨2, [1]⟩, ⟨3, []⟩]⟩

theorem shared_production_distinct_uses :
    check [] shared = true ∧ shared.flattenedSupport = [1, 2, 3] ∧
      shared.causes? 2 = some [1] ∧ shared.causes? 3 = some [1] := by
  decide

theorem missing_occurrence_differs_from_empty_causes :
    shared.causes? 0 = none ∧ shared.causes? 1 = some [] := by decide

theorem missing_dependency_refused : check [] (⟨[1], [⟨1, [9]⟩]⟩ : CausalReceipt Nat) = false := by
  decide

theorem captured_boundary_is_explicit :
    check [9] (⟨[1], [⟨1, [9]⟩]⟩ : CausalReceipt Nat) = true := by decide

theorem duplicated_identity_refused :
    check [] (⟨[1], [⟨1, []⟩, ⟨1, []⟩]⟩ : CausalReceipt Nat) = false := by decide

theorem cycle_refused :
    check [] (⟨[2], [⟨1, [2]⟩, ⟨2, [1]⟩]⟩ : CausalReceipt Nat) = false := by decide

/-- A structurally valid graph can omit a real semantic dependency. Native
event correspondence is required in addition to this structural checker. -/
theorem valid_structure_does_not_authenticate_edges :
    check [] shared = true ∧ check [] erasedSharing = true ∧
      shared.flattenedSupport = erasedSharing.flattenedSupport ∧
      shared.causes? 3 ≠ erasedSharing.causes? 3 := by
  decide

end Controls

/-! ## Retained transitive ancestry

The query reuses the finite catalogue sweep. Its answer describes only the
represented graph, with captured boundary identities included explicitly.
A structurally checked receipt does not authenticate native dependency edges.
-/

/-- Immediate dependants of an occurrence, in retained recording order. -/
def dependants [DecidableEq Event] (receipt : CausalReceipt Event)
    (identity : Event) : List Event :=
  (receipt.events.filter (fun event => decide (identity ∈ event.directCauses))).map CausalEvent.event

theorem mem_dependants [DecidableEq Event] (receipt : CausalReceipt Event)
    (cause effect : Event) : effect ∈ receipt.dependants cause ↔ receipt.Direct cause effect := by
  simp only [dependants, List.mem_map, List.mem_filter, decide_eq_true_eq, Direct]
  constructor
  · rintro ⟨event, ⟨present, depends⟩, same⟩
    exact ⟨event, present, same, depends⟩
  · rintro ⟨event, present, same, depends⟩
    exact ⟨event, ⟨present, depends⟩, same⟩

/-- Both endpoints of a retained edge are available in its declared boundary. -/
theorem direct_known [DecidableEq Event] (boundary : List Event)
    (receipt : CausalReceipt Event) (valid : WellFormed boundary receipt)
    {cause effect : Event} (edge : receipt.Direct cause effect) :
    cause ∈ receipt.known boundary ∧ effect ∈ receipt.known boundary := by
  have effectKnown : effect ∈ receipt.known boundary := by
    obtain ⟨event, present, rfl, _⟩ := edge
    exact List.mem_append_right _ (List.mem_map.mpr ⟨event, present, rfl⟩)
  exact ⟨List.idxOf_lt_length_iff.mp
    ((direct_rank boundary receipt valid edge).trans (List.idxOf_lt_length_iff.mpr effectKnown)),
    effectKnown⟩

/-- Reverse dependencies let the existing affected-item sweep answer which
recorded occurrences support a selected occurrence. -/
def dependencyCatalogue [DecidableEq Event] (boundary : List Event)
    (receipt : CausalReceipt Event) :
    Mettapedia.Algorithms.WellFoundedServices.Catalogue Event where
  items := receipt.known boundary
  deps := receipt.dependants

theorem catalogue_uses_iff [DecidableEq Event] (boundary : List Event)
    (receipt : CausalReceipt Event) (valid : WellFormed boundary receipt)
    (cause effect : Event) :
    (receipt.dependencyCatalogue boundary).Uses cause effect ↔ receipt.Direct cause effect := by
  change cause ∈ receipt.known boundary ∧ effect ∈ receipt.dependants cause ↔ _
  rw [mem_dependants]
  exact ⟨And.right, fun edge => ⟨(direct_known boundary receipt valid edge).1, edge⟩⟩

/-- Missing queried occurrences and invalid receipt structure refuse the
readout. Equal payloads are irrelevant: the query uses occurrence identities.
The result includes the selected occurrence and captured boundary references;
it makes no claim about unavailable history preceding those references. -/
def ancestors? [DecidableEq Event] (boundary : List Event)
    (receipt : CausalReceipt Event) (identity : Event) : Option (List Event) :=
  if receipt.check boundary = true ∧ identity ∈ receipt.known boundary then
    some ((receipt.dependencyCatalogue boundary).affected [identity])
  else none

theorem ancestors?_refused [DecidableEq Event] (boundary : List Event)
    (receipt : CausalReceipt Event) (identity : Event)
    (missing : identity ∉ receipt.known boundary) :
    receipt.ancestors? boundary identity = none := by
  simp [ancestors?, missing]

theorem ancestors?_exact [DecidableEq Event] (boundary : List Event)
    (receipt : CausalReceipt Event) (identity : Event) (result : List Event)
    (reported : receipt.ancestors? boundary identity = some result) :
    WellFormed boundary receipt ∧ identity ∈ receipt.known boundary ∧
      ∀ cause, cause ∈ result ↔ cause = identity ∨ Relation.TransGen receipt.Direct cause identity := by
  unfold ancestors? at reported
  split at reported
  · rename_i admitted
    have valid := (check_iff boundary receipt).mp admitted.1
    cases Option.some.inj reported
    refine ⟨valid, admitted.2, ?_⟩
    intro cause
    rw [(receipt.dependencyCatalogue boundary).mem_affected [identity] cause]
    simp only [List.mem_singleton, exists_eq_left]
    have same : Relation.ReflTransGen (receipt.dependencyCatalogue boundary).Uses cause identity ↔
        Relation.ReflTransGen receipt.Direct cause identity := by
      constructor
      · intro path
        exact Relation.ReflTransGen.mono (fun left right edge =>
          (catalogue_uses_iff boundary receipt valid left right).mp edge) cause identity path
      · intro path
        exact Relation.ReflTransGen.mono (fun left right edge =>
          (catalogue_uses_iff boundary receipt valid left right).mpr edge) cause identity path
    rw [same, Relation.reflTransGen_iff_eq_or_transGen]
    simp only [eq_comm]
  · contradiction

namespace AncestryControls

def diamond : CausalReceipt Nat :=
  ⟨[4], [⟨1, []⟩, ⟨2, [1]⟩, ⟨3, [1]⟩, ⟨4, [2, 3]⟩]⟩

theorem shared_producer_is_retained_once :
    diamond.ancestors? [] 4 = some [4, 2, 3, 1] := by decide

theorem distinct_equal_uses_keep_distinct_queries :
    Controls.shared.ancestors? [] 2 = some [2, 1] ∧
      Controls.shared.ancestors? [] 3 = some [3, 1] := by decide

theorem missing_is_not_recorded_parentless :
    Controls.shared.ancestors? [] 0 = none ∧
      Controls.shared.ancestors? [] 1 = some [1] := by decide

theorem removed_sharing_changes_ancestry :
    Controls.shared.ancestors? [] 3 ≠ Controls.erasedSharing.ancestors? [] 3 := by decide

theorem captured_boundary_stays_visible :
    (⟨[1], [⟨1, [9]⟩]⟩ : CausalReceipt Nat).ancestors? [9] 1 = some [1, 9] := by decide

theorem missing_edge_target_refuses :
    (⟨[1], [⟨1, [9]⟩]⟩ : CausalReceipt Nat).ancestors? [] 1 = none := by decide

theorem duplicate_identity_refuses :
    (⟨[1], [⟨1, []⟩, ⟨1, []⟩]⟩ : CausalReceipt Nat).ancestors? [] 1 = none := by decide

theorem cycle_refuses :
    (⟨[2], [⟨1, [2]⟩, ⟨2, [1]⟩]⟩ : CausalReceipt Nat).ancestors? [] 2 = none := by decide

end AncestryControls

private def independentReceipt : CausalReceipt Nat where
  roots := [2]
  events :=
    [ { event := 1, directCauses := [] }
    , { event := 2, directCauses := [] } ]

private def dependentReceipt : CausalReceipt Nat where
  roots := [2]
  events :=
    [ { event := 1, directCauses := [] }
    , { event := 2, directCauses := [1] } ]

/-- Positive discriminator: flattening retains both event occurrences in
their exported order. -/
example : dependentReceipt.flattenedSupport = [1, 2] := rfl

/-- Negative discriminator: an independent pair and a causal chain have the
same flattened support. -/
example : independentReceipt.flattenedSupport =
    dependentReceipt.flattenedSupport := rfl

theorem independentReceipt_ne_dependentReceipt :
    independentReceipt ≠ dependentReceipt := by
  intro equal
  have eventsEqual := congrArg CausalReceipt.events equal
  simp [independentReceipt, dependentReceipt] at eventsEqual

/-- Consequently, no decoder from flattened event support can recover the
causal receipt for every input. -/
theorem flattenedSupport_not_injective :
    ¬ Function.Injective
      (flattenedSupport : CausalReceipt Nat → List Nat) := by
  intro injective
  exact independentReceipt_ne_dependentReceipt
    (injective (by rfl))

end CausalReceipt

/-! ## Demand annotations -/

/-- Whether a cell observation was demanded while matching a left-hand side
or while evaluating the selected right-hand side. -/
inductive DemandRole where
  | lhs
  | rhs
deriving DecidableEq, Repr

/-- Candidate-local information required to replay why an event was demanded. -/
structure DemandAnnotation (Event ExpectedType : Type) where
  event : Event
  role : DemandRole
  expectedType : ExpectedType
deriving DecidableEq, Repr

namespace DemandAnnotation

/-- The event-only projection used when role and expected type are absent from
the wire observation. -/
def erase (annotation : DemandAnnotation Event ExpectedType) : Event :=
  annotation.event

private def lhsDemand : DemandAnnotation Nat Bool :=
  { event := 7, role := .lhs, expectedType := false }

private def rhsDemand : DemandAnnotation Nat Bool :=
  { event := 7, role := .rhs, expectedType := false }

private def otherTypeDemand : DemandAnnotation Nat Bool :=
  { event := 7, role := .lhs, expectedType := true }

/-- Positive discriminator: erasure retains the referenced event occurrence. -/
example : lhsDemand.erase = 7 := rfl

/-- The event-only projection cannot distinguish left- from right-hand-side
demand. -/
theorem erase_role_not_injective :
    ¬ Function.Injective
      (erase : DemandAnnotation Nat Bool → Nat) := by
  intro injective
  have equalAnnotations : lhsDemand = rhsDemand :=
    injective (by rfl)
  have equalRoles := congrArg DemandAnnotation.role equalAnnotations
  cases equalRoles

/-- Nor can the same projection reconstruct the expected type. -/
theorem erase_expectedType_not_injective :
    ¬ Function.Injective
      (erase : DemandAnnotation Nat Bool → Nat) := by
  intro injective
  have equalAnnotations : lhsDemand = otherTypeDemand :=
    injective (by rfl)
  have equalTypes := congrArg DemandAnnotation.expectedType equalAnnotations
  simp [lhsDemand, otherTypeDemand] at equalTypes

end DemandAnnotation

/-! ## Interrupted frontiers -/

/-- A resource-interrupted execution together with the live frontier known to
the producer.  The existing external observation retains the answers and
reason but may omit `pending`. -/
structure InterruptedRunWitness (State Answer : Type) where
  answers : List (Answer × List Nat)
  reason : ResourceInterruption
  pending : List State
deriving DecidableEq, Repr

namespace InterruptedRunWitness

/-- Erase a producer-side interrupted frontier to the public run observation. -/
def erase (witness : InterruptedRunWitness State Answer) :
    RunObservation State Answer where
  answers := witness.answers
  stop := .interrupted witness.reason

private def waitingAtOne : InterruptedRunWitness Nat Nat where
  answers := [(7, [0])]
  reason := .fuelExhausted
  pending := [1]

private def waitingAtTwo : InterruptedRunWitness Nat Nat where
  answers := [(7, [0])]
  reason := .fuelExhausted
  pending := [2]

/-- Positive discriminator: answer occurrences and interruption reason remain
observable after the frontier is erased. -/
example : waitingAtOne.erase.answers = [(7, [0])] := rfl

example : waitingAtOne.erase.stop.externalInterruption =
    some .fuelExhausted := rfl

/-- Negative discriminator: two different live frontiers produce the same
external interruption observation. -/
example : waitingAtOne.erase = waitingAtTwo.erase := rfl

theorem waitingAtOne_ne_waitingAtTwo : waitingAtOne ≠ waitingAtTwo := by
  intro equal
  have pendingEqual := congrArg InterruptedRunWitness.pending equal
  simp [waitingAtOne, waitingAtTwo] at pendingEqual

/-- Therefore an answer-and-reason observation cannot reconstruct the live
frontier of every interrupted execution. -/
theorem erase_not_injective :
    ¬ Function.Injective
      (erase : InterruptedRunWitness Nat Nat → RunObservation Nat Nat) := by
  intro injective
  exact waitingAtOne_ne_waitingAtTwo (injective (by rfl))

end InterruptedRunWitness

end Mettapedia.Machines

import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearHornAdequacy

/-!
# Static linear connections between selected occurrence ports

A layout is a finite collection of actual rule/occurrence choices equipped
with a proposed topological enumeration. Its conditions mention only port
shapes, declared rules, physical identities and one joint equation model.
They do not ask whether a transition or schedule executes.

Every take port has a supplier at the initial boundary or an earlier
production. Each physical identity has at most one producer and one consuming
use; productions are fresh from the boundary. Untaken identities are the
explicit residual boundary. These are the pure consume/produce connections,
without shared reads, checks or a general linear-mating correctness criterion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearConnectionLayout

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConditionalComposite

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

abbrev Event (T : Type uT) (O : Type uO) := ConditionalSchedule.Firing T O

def made (events : List (Event T O)) : Finset O :=
  (events.flatMap fun event => event.2.made).toFinset

def taken (events : List (Event T O)) : Finset O :=
  (events.flatMap fun event => event.2.taken).toFinset

@[simp] theorem made_nil : made ([] : List (Event T O)) = ∅ := rfl
@[simp] theorem taken_nil : taken ([] : List (Event T O)) = ∅ := rfl
@[simp] theorem made_cons (event : Event T O) (events : List (Event T O)) :
    made (event :: events) = event.2.made.toFinset ∪ made events := by
  simp [made]
@[simp] theorem taken_cons (event : Event T O) (events : List (Event T O)) :
    taken (event :: events) = event.2.taken.toFinset ∪ taken events := by
  simp [taken]

def residual (initial : Finset O) (events : List (Event T O)) : Finset O :=
  (initial ∪ made events) \ taken events

/-- The list order is a supplied topological enumeration of the producer/use
edges. An initial boundary occurrence has no event producer. -/
def Supplied (initial : Finset O) (events : List (Event T O)) : Prop :=
  ∀ (earlier : List (Event T O)) (event : Event T O) (suffix : List (Event T O)),
    events = earlier ++ event :: suffix →
    event.2.taken.toFinset ⊆ initial ∪ made earlier

theorem supplied_singleton_iff (initial : Finset O) (event : Event T O) :
    Supplied initial [event] ↔ event.2.taken.toFinset ⊆ initial := by
  constructor
  · intro supplied
    simpa using supplied [] event [] rfl
  · intro funded earlier selected later decomposition
    have earlierEmpty : earlier = [] := by
      have sizes := congrArg List.length decomposition
      simp only [List.length_append, List.length_cons, List.length_nil] at sizes
      exact List.length_eq_zero_iff.mp (by omega)
    subst earlier
    simp only [List.nil_append, List.cons.injEq, eq_comm (a := [])] at decomposition
    obtain ⟨rfl, rfl⟩ := decomposition
    simpa using funded

/-- Static port matching under one shared solution. Physical IDs, rather
than equal term labels, enforce linearity. Rule uses are list occurrences. -/
structure Certificate (A : SubstitutionAction T S) (program : Set (RuleInstance T))
    (assignment : S) (label : O → T) (before : Configuration T O)
    (events : List (Event T O)) : Prop where
  shapes : ∀ event ∈ events, (ShapeTest.ofSelection event.1 event.2).Holds label
  pure : LinearHornAdequacy.Pure events
  declared : LinearHornAdequacy.Declared program events
  produced_distinct : (events.flatMap fun event => event.2.made).Nodup
  consumed_distinct : (events.flatMap fun event => event.2.taken).Nodup
  fresh_boundary : Disjoint (made events) before.present
  supplied : Supplied before.present events
  incoming : A.Models assignment before.equations
  connections : ∀ event ∈ events,
    A.Models assignment (addedEquations label event.1 event.2)

/-- The final equation store is a conjunction of all port equations and
tells, interpreted by one assignment. It is independent of event order. -/
theorem models_follow_iff (A : SubstitutionAction T S) (assignment : S) (label : O → T) :
    ∀ (events : List (Event T O)) (before : Configuration T O),
      A.Models assignment (ConditionalSchedule.follow label before events).equations ↔
        A.Models assignment before.equations ∧
          ∀ event ∈ events, A.Models assignment (addedEquations label event.1 event.2)
  | [], _before => by simp [ConditionalSchedule.follow]
  | event :: events, before => by
      rw [ConditionalSchedule.follow, models_follow_iff A assignment label events,
        show (event.2.result label event.1 before).equations =
          before.equations ++ addedEquations label event.1 event.2 from problem_eq ..,
        A.models_append]
      simp only [List.forall_mem_cons]
      tauto

/-- A prefix can supply only initial occurrences and its own productions.
This does not assume that the prefix executes. -/
theorem present_follow_subset (label : O → T) :
    ∀ (events : List (Event T O)) (before : Configuration T O),
      (ConditionalSchedule.follow label before events).present ⊆ before.present ∪ made events
  | [], _before => by simp [ConditionalSchedule.follow]
  | event :: events, before => by
      intro o present
      have prior := present_follow_subset label events (event.2.result label event.1 before) present
      rcases Finset.mem_union.mp prior with current | created
      · rcases mem_fire.mp current with ⟨initial, _⟩ | produced
        · exact Finset.mem_union_left _ initial
        · exact Finset.mem_union_right _ (by simp [Selection.commit] at produced; simp [produced])
      · exact Finset.mem_union_right _ (by simp [created])

theorem valid_after_earlier (A : SubstitutionAction T S) (label : O → T) :
    ∀ (earlier : List (Event T O)) (event : Event T O) (later : List (Event T O))
      (before : Configuration T O),
      ConditionalSchedule.Executable A label before (earlier ++ event :: later) →
        event.2.Valid A label event.1 (ConditionalSchedule.follow label before earlier)
  | [], _event, _later, _before, executes => executes.1
  | first :: earlier, event, later, before, executes =>
      valid_after_earlier A label earlier event later (first.2.result label first.1 before) executes.2

/-- An actual run supplies each take from its initial boundary or a strict
earlier production. This supplies the connection certificate's acyclic order. -/
theorem supplied_of_executable (A : SubstitutionAction T S) (label : O → T)
    (events : List (Event T O)) (before : Configuration T O)
    (executes : ConditionalSchedule.Executable A label before events) : Supplied before.present events := by
  intro earlier event later decomposition o taken
  subst events
  have valid := valid_after_earlier A label earlier event later before executes
  exact present_follow_subset label earlier before (valid.occurrences.taken_subset taken)

theorem shapes_of_executable (A : SubstitutionAction T S) (label : O → T) :
    ∀ (events : List (Event T O)) (before : Configuration T O),
      ConditionalSchedule.Executable A label before events →
        ∀ event ∈ events, (ShapeTest.ofSelection event.1 event.2).Holds label
  | [], _before, _executes, _event, member => by cases member
  | first :: events, before, executes, event, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨executes.1.take_distinct, executes.1.output_distinct, executes.1.take_length,
          executes.1.read_length, executes.1.outputs⟩
      · exact shapes_of_executable A label events (first.2.result label first.1 before) executes.2 event later

namespace Certificate

variable {A : SubstitutionAction T S} {program : Set (RuleInstance T)}
  {assignment : S} {label : O → T} {before : Configuration T O}
  {event : Event T O} {events : List (Event T O)}

theorem head_valid (layout : Certificate A program assignment label before (event :: events)) :
    event.2.Valid A label event.1 before := by
  have shape := layout.shapes event (List.mem_cons_self ..)
  have pure := layout.pure event (List.mem_cons_self ..)
  have readEmpty : event.2.read = [] := by
    have count := shape.2.2.2.1
    change event.1.read.length = event.2.read.length at count
    rw [pure.1] at count
    exact List.length_eq_zero_iff.mp count.symm
  have headSupplied : event.2.taken.toFinset ⊆ before.present := by
    simpa using layout.supplied [] event events rfl
  have headFresh : Disjoint event.2.made.toFinset before.present := by
    exact Finset.disjoint_of_subset_left (by intro o member; simp [member]) layout.fresh_boundary
  refine ⟨shape.1, shape.2.1, shape.2.2.1, shape.2.2.2.1, shape.2.2.2.2, ?_, ?_, ?_⟩
  · refine ⟨headSupplied, ?_, ?_, headFresh, ?_⟩
    · simp [Selection.commit, readEmpty]
    · simp [Selection.commit, readEmpty]
    · intro query member
      cases member
  · refine ⟨assignment, ?_⟩
    rw [problem_eq, A.models_append]
    exact ⟨layout.incoming, layout.connections event (List.mem_cons_self ..)⟩
  · simp [pure.2]

theorem tail (layout : Certificate A program assignment label before (event :: events)) :
    Certificate A program assignment label (event.2.result label event.1 before) events := by
  have producerSplit := List.nodup_append.mp layout.produced_distinct
  have consumerSplit := List.nodup_append.mp layout.consumed_distinct
  refine ⟨?_, ?_, ?_, producerSplit.2.1, consumerSplit.2.1, ?_, ?_, ?_, ?_⟩
  · exact fun selected member => layout.shapes selected (List.mem_cons_of_mem _ member)
  · exact fun selected member => layout.pure selected (List.mem_cons_of_mem _ member)
  · exact fun selected member => layout.declared selected (List.mem_cons_of_mem _ member)
  · refine Finset.disjoint_left.mpr fun o inTail inResult => ?_
    rcases mem_fire.mp inResult with ⟨inBefore, _⟩ | inHead
    · exact Finset.disjoint_left.mp layout.fresh_boundary (by simp [inTail]) inBefore
    · have tailMember : o ∈ events.flatMap (fun selected => selected.2.made) := by
        simpa [made] using inTail
      have headMember : o ∈ event.2.made := by simpa [Selection.commit] using inHead
      exact producerSplit.2.2 o headMember o tailMember rfl
  · intro earlier selected suffix decomposition o inTake
    have oldSupply := layout.supplied (event :: earlier) selected suffix (by simp [decomposition]) inTake
    have selectedMember : selected ∈ events := by rw [decomposition]; simp
    have tailTake : o ∈ events.flatMap (fun selected => selected.2.taken) := by
      exact List.mem_flatMap.mpr ⟨selected, selectedMember, by simpa using inTake⟩
    have notHead : o ∉ event.2.taken.toFinset := by
      intro member
      exact consumerSplit.2.2 o (by simpa using member) o tailTake rfl
    simp only [made_cons, Finset.mem_union] at oldSupply
    rcases oldSupply with inBefore | inHead | inPrefix
    · exact Finset.mem_union_left _ (mem_fire.mpr (Or.inl ⟨inBefore, notHead⟩))
    · exact Finset.mem_union_left _ (mem_fire.mpr (Or.inr inHead))
    · exact Finset.mem_union_right _ inPrefix
  · rw [Selection.result, problem_eq, A.models_append]
    exact ⟨layout.incoming, layout.connections event (List.mem_cons_self ..)⟩
  · exact fun selected member => layout.connections selected (List.mem_cons_of_mem _ member)

/-- Static connections construct the real existing schedule; they are not
defined by schedule acceptance. The same assignment models its full result. -/
theorem executes : ∀ {events : List (Event T O)} {before : Configuration T O},
    Certificate A program assignment label before events →
      ConditionalSchedule.Executable A label before events ∧
      A.Models assignment (ConditionalSchedule.follow label before events).equations
  | [], _before, layout => ⟨⟨assignment, layout.incoming⟩, layout.incoming⟩
  | _ :: _, _before, layout =>
      let rest := layout.tail.executes
      ⟨⟨layout.head_valid, rest.1⟩, rest.2⟩

theorem residual_after_head
    (layout : Certificate A program assignment label before (event :: events)) :
    residual (event.2.result label event.1 before).present events =
      residual before.present (event :: events) := by
  have valid := layout.head_valid
  have noProducedTake : Disjoint (made (event :: events)) event.2.taken.toFinset :=
    Finset.disjoint_of_subset_right valid.occurrences.taken_subset layout.fresh_boundary
  ext o
  have apart : o ∈ made (event :: events) → o ∉ event.2.taken.toFinset :=
    fun member => Finset.disjoint_left.mp noProducedTake member
  simp only [residual, made_cons, taken_cons, Selection.result, fire,
    Selection.commit, Finset.mem_sdiff, Finset.mem_union]
  simp only [made_cons, Finset.mem_union] at apart
  tauto

/-- Every unconsumed physical occurrence remains at the explicit boundary.
Duplicate labels do not identify distinct boundary occurrences. -/
theorem final_rows : ∀ {events : List (Event T O)} {before : Configuration T O},
    Certificate A program assignment label before events →
      (ConditionalSchedule.follow label before events).present = residual before.present events
  | [], _before, _layout => by simp [ConditionalSchedule.follow, residual]
  | _ :: _, _before, layout => (final_rows layout.tail).trans layout.residual_after_head

theorem logical_proof [DecidableEq T] (structural : A.E = Eq)
    (layout : Certificate A program assignment label before events) :
    ∃ proof : LinearHornAdequacy.Proof A program assignment
        (labels (PositiveResourceProjection.realized A assignment label) before.present)
        (labels (PositiveResourceProjection.realized A assignment label) (residual before.present events)),
      proof.uses.map (LinearHornAdequacy.rawRule A program assignment) = events.map Prod.fst := by
  obtain ⟨executable, solved⟩ := layout.executes
  rw [← layout.final_rows]
  exact LinearHornAdequacy.proof_of_constraint_schedule A program assignment label structural
    events before executable layout.pure layout.declared solved

end Certificate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearConnectionLayout

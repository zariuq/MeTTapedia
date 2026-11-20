import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Events
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Product

/-!
# A counted local activation discipline in the existing world construction

The immutable environment supplies schema code and a capture-selection policy
on ordinary states. A choice retains the selected schema identity, output
identity, visibility proof and actual held-rule admission. Its successor is
the actual materialization result's ordinary state. The policy may be partial:
missing closure witnesses supply no admitted choice, rather than a solver oracle.

This is an explicit local discipline. Projection to ordinary states does not
claim that arbitrary held-rule metadata is reconstructible. Repeated-source
correspondences require capture-policy coherence; the concrete example below
checks that property on actual results. Isolation concerns the counted local
event system. The singleton world law is only for singleton-to-singleton
transitions with an empty shared space: fork and publication remain other moves.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.Worlds

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface (Frames)
open Interface.Frames (Frame)
open RuleOccurrences SchematicRows
open RuleSyntax.Worlds (Bag Move Joining LocalSteps Advances)

variable {S : Signature} {O R : Type} [DecidableEq O] [DecidableEq R]

/-- Captured arguments are supplied explicitly at the current state; code is
fixed independently of that state. No matching or admission result is a field. -/
def closures (catalogue : R → Schema (Contextual.Terms S))
    (arguments : (state : RuleSyntax.State (Contextual.Terms S) O) → R →
      List (Contextual.Terms S state.frame))
    (state : RuleSyntax.State (Contextual.Terms S) O) (selected : R) :
    Closure (Contextual.Terms S) state.frame :=
  ⟨catalogue selected, arguments state selected⟩

structure Choice (catalogue : R → Schema (Contextual.Terms S))
    (arguments : (state : RuleSyntax.State (Contextual.Terms S) O) → R →
      List (Contextual.Terms S state.frame)) (rows : Finset R)
    (program : Program (Contextual.Terms S)) (state : RuleSyntax.State (Contextual.Terms S) O) where
  selected : R
  output : O
  visible : (catalogue selected).toRule ∈ program
  admitted : (Rows.activation state rows (closures catalogue arguments state) selected output).Admits
    (Frames.contextual S) ∅

/-- A derived local materialization discipline; the event fibre retains origins
even when two schema occurrences produce the same observable result. -/
def activationEvents (catalogue : R → Schema (Contextual.Terms S))
    (arguments : (state : RuleSyntax.State (Contextual.Terms S) O) → R →
      List (Contextual.Terms S state.frame)) (rows : Finset R) :
    LocalSteps (Contextual.Terms S) O (Rule (Contextual.Terms S)) := fun program => {
  Choice := Choice catalogue arguments rows program
  next := fun state choice =>
    ((Rows.activation state rows (closures catalogue arguments state) choice.selected choice.output).result
      (Frames.contextual S)).toState
  action := fun _ choice => (catalogue choice.selected).toRule }

/-- A concrete capture policy reads named source occurrences. Its transport
law is proved from actual result labels, rather than supplied by the provider. -/
def anchoredArguments (anchors : R → List O)
    (state : RuleSyntax.State (Contextual.Terms S) O) (selected : R) :
    List (Contextual.Terms S state.frame) := (anchors selected).map state.label

theorem anchored_arguments_coherent
    (catalogue : R → Schema (Contextual.Terms S)) (anchors : R → List O) (rows : Finset R)
    (state : RuleSyntax.State (Contextual.Terms S) O) (selected other : R) (output : O)
    (separated : ∀ anchor ∈ anchors other, anchor ≠ output) :
    anchoredArguments anchors
        ((Rows.activation state rows (closures catalogue (anchoredArguments anchors) state)
          selected output).result (Frames.contextual S)).toState other =
      (anchoredArguments anchors state other).map
        (instantiateObservation (Contextual.weakenNames S state.frame (catalogue selected).locals)) := by
  simp only [anchoredArguments, List.map_map]
  apply List.map_congr_left
  intro anchor member
  exact Rows.activation_label_other state rows _ selected output anchor (separated anchor member)

theorem live_anchored_arguments_coherent
    (catalogue : R → Schema (Contextual.Terms S)) (anchors : R → List O) (rows : Finset R)
    (state : RuleSyntax.State (Contextual.Terms S) O) (selected other : R) (output : O)
    (live : ∀ anchor ∈ anchors other, anchor ∈ state.present) (fresh : output ∉ state.present) :
    anchoredArguments anchors
        ((Rows.activation state rows (closures catalogue (anchoredArguments anchors) state)
          selected output).result (Frames.contextual S)).toState other =
      (anchoredArguments anchors state other).map
        (instantiateObservation (Contextual.weakenNames S state.frame (catalogue selected).locals)) := by
  apply anchored_arguments_coherent catalogue anchors rows state selected other output
  intro anchor member same
  exact fresh (same ▸ live anchor member)

theorem choice_of_reading (catalogue : R → Schema (Contextual.Terms S))
    (arguments : (state : RuleSyntax.State (Contextual.Terms S) O) → R →
      List (Contextual.Terms S state.frame)) (rows : Finset R)
    (program : Program (Contextual.Terms S)) (state : RuleSyntax.State (Contextual.Terms S) O)
    (selected : R) (output : O) (visible : (catalogue selected).toRule ∈ program)
    (present : selected ∈ rows) (fresh : output ∉ state.present)
    (wellFormed : (closures catalogue arguments state selected).WellFormed) {target : Frame S}
    (caller : Assignment state.frame.arity target.arity)
    (known : (Frames.contextual S).Models caller state.knowledge)
    (value : Contextual.Terms S target)
    (reading : (closures catalogue arguments state selected).ReadsAt (Frames.contextual S) caller value) :
    Nonempty ((activationEvents catalogue arguments rows program).Choice state) := by
  exact ⟨⟨selected, output, visible,
    Rows.activation_admitted_of_reading state rows _ selected output present fresh wellFormed
      caller known value reading⟩⟩

/-- The event and its observed result are constructed from one source reading.
The provider never supplies an admission or a desired target execution. -/
theorem choice_realizes_reading (catalogue : R → Schema (Contextual.Terms S))
    (arguments : (state : RuleSyntax.State (Contextual.Terms S) O) → R →
      List (Contextual.Terms S state.frame)) (rows : Finset R)
    (program : Program (Contextual.Terms S)) (state : RuleSyntax.State (Contextual.Terms S) O)
    (selected : R) (output : O) (visible : (catalogue selected).toRule ∈ program)
    (present : selected ∈ rows) (fresh : output ∉ state.present)
    (wellFormed : (closures catalogue arguments state selected).WellFormed) {target : Frame S}
    (caller : Assignment state.frame.arity target.arity)
    (known : (Frames.contextual S).Models caller state.knowledge)
    (value : Contextual.Terms S target)
    (reading : (closures catalogue arguments state selected).ReadsAt (Frames.contextual S) caller value) :
    ∃ choice : (activationEvents catalogue arguments rows program).Choice state,
      choice.selected = selected ∧ choice.output = output ∧
      ∃ point : Assignment
          ((activationEvents catalogue arguments rows program).next state choice).frame.arity target.arity,
        (Frames.contextual S).Models point
          ((activationEvents catalogue arguments rows program).next state choice).knowledge ∧
        instantiateObservation point
          (((activationEvents catalogue arguments rows program).next state choice).label output) = value := by
  obtain ⟨admitted, point, model, _, observed⟩ := Rows.activation_realizes_reading state rows
    (closures catalogue arguments state) selected output present fresh wellFormed caller known value reading
  exact ⟨⟨selected, output, visible, admitted⟩, rfl, rfl, point, model, observed⟩

theorem local_program_monotone (catalogue : R → Schema (Contextual.Terms S))
    (arguments : (state : RuleSyntax.State (Contextual.Terms S) O) → R →
      List (Contextual.Terms S state.frame)) (rows : Finset R) :
    RuleSyntax.Worlds.ProgramMonotone (activationEvents catalogue arguments rows) := by
  intro first second inside before after advanced
  obtain ⟨choice, reached⟩ := advanced
  exact ⟨⟨choice.selected, choice.output, inside choice.visible, choice.admitted⟩, reached⟩

theorem local_no_events_at_inconsistent (catalogue : R → Schema (Contextual.Terms S))
    (arguments : (state : RuleSyntax.State (Contextual.Terms S) O) → R →
      List (Contextual.Terms S state.frame)) (rows : Finset R) :
    RuleSyntax.Worlds.NoEventsAtInconsistent (Frames.contextual S) (activationEvents catalogue arguments rows) := by
  intro program state dead
  refine ⟨?_⟩
  intro choice
  let firing := Rows.activation state rows (closures catalogue arguments state) choice.selected choice.output
  obtain ⟨_, _, ⟨target, point, solved⟩, _⟩ := choice.admitted
  have baseModel := ((Frames.models_append (X := Frames.contextual S) point _ _).mp solved).1
  exact dead ⟨target, _, Firing.knowledge_solved firing.base baseModel⟩

/-- This exact one-world statement excludes the other constructors of Move by
its singleton endpoint and empty-space hypotheses, not by dropping them. -/
theorem one_world_activation_iff (catalogue : R → Schema (Contextual.Terms S))
    (arguments : (state : RuleSyntax.State (Contextual.Terms S) O) → R →
      List (Contextual.Terms S state.frame)) (rows : Finset R)
    (join : Joining (Frames.contextual S) O)
    (before after : RuleSyntax.Equivalence.System (Contextual.Terms S) O) :
    Move (Frames.contextual S) join (activationEvents catalogue arguments rows)
        ⟨{before}, ∅⟩ ⟨{after}, ∅⟩ ↔
      after.program = before.program ∧
        ∃ choice : Choice catalogue arguments rows before.program before.state,
          ((Rows.activation before.state rows (closures catalogue arguments before.state)
            choice.selected choice.output).result (Frames.contextual S)).toState = after.state :=
  RuleSyntax.Worlds.one_world_local_moves before after

/-- Adding a fixed unrelated world changes no selected activation or result. -/
theorem activation_beside (catalogue : R → Schema (Contextual.Terms S))
    (arguments : (state : RuleSyntax.State (Contextual.Terms S) O) → R →
      List (Contextual.Terms S state.frame)) (rows : Finset R)
    (join : Joining (Frames.contextual S) O) (program : Program (Contextual.Terms S))
    (state : RuleSyntax.State (Contextual.Terms S) O)
    (choice : Choice catalogue arguments rows program state)
    (neighbour : RuleSyntax.Equivalence.System (Contextual.Terms S) O) :
    Move (Frames.contextual S) join (activationEvents catalogue arguments rows)
      ⟨{⟨program, state⟩, neighbour}, ∅⟩
      ⟨{⟨program, ((Rows.activation state rows (closures catalogue arguments state)
        choice.selected choice.output).result (Frames.contextual S)).toState⟩, neighbour}, ∅⟩ := by
  have visible : (catalogue choice.selected).toRule ∈ program ∪ ∅ :=
    Set.mem_union_left _ choice.visible
  exact Move.fire (X := Frames.contextual S) (J := join)
    (family := activationEvents catalogue arguments rows) {neighbour} ∅ ⟨program, state⟩
    ⟨choice.selected, choice.output, visible, choice.admitted⟩

/-- A Type-valued event-fibre bijection, not an endpoint-only simulation. -/
def dead_neighbour_comparison (catalogue : R → Schema (Contextual.Terms S))
    (arguments : (state : RuleSyntax.State (Contextual.Terms S) O) → R →
      List (Contextual.Terms S state.frame)) (rows : Finset R)
    (program otherProgram : Program (Contextual.Terms S)) :
    Interface.EventMultiplicity.Bisimulation
      (Interface.EventMultiplicity.asynchronous (activationEvents catalogue arguments rows program)
        (activationEvents catalogue arguments rows otherProgram))
      (activationEvents catalogue arguments rows program)
      (fun pair state => pair.1 = state ∧ ¬ (Frames.contextual S).Solvable pair.2.knowledge) :=
  RuleSyntax.Worlds.idleBeside (activationEvents catalogue arguments rows program)
    (activationEvents catalogue arguments rows otherProgram)
    (fun state : RuleSyntax.State (Contextual.Terms S) O => ¬ (Frames.contextual S).Solvable state.knowledge)
    (local_no_events_at_inconsistent catalogue arguments rows otherProgram)

theorem dead_neighbour_observer (catalogue : R → Schema (Contextual.Terms S))
    (arguments : (state : RuleSyntax.State (Contextual.Terms S) O) → R →
      List (Contextual.Terms S state.frame)) (rows : Finset R)
    (program otherProgram : Program (Contextual.Terms S))
    (state neighbour : RuleSyntax.State (Contextual.Terms S) O)
    (dead : ¬ (Frames.contextual S).Solvable neighbour.knowledge)
    {Output : Type} (observe : RuleSyntax.State (Contextual.Terms S) O → Output) (count : Nat)
    (run : (Interface.EventMultiplicity.asynchronous (activationEvents catalogue arguments rows program)
      (activationEvents catalogue arguments rows otherProgram)).Execution count (state, neighbour)) :
    (activationEvents catalogue arguments rows program).word
        ((dead_neighbour_comparison catalogue arguments rows program otherProgram).executions
          count ⟨rfl, dead⟩ run) =
      (Interface.EventMultiplicity.asynchronous (activationEvents catalogue arguments rows program)
        (activationEvents catalogue arguments rows otherProgram)).word run ∧
      observe ((activationEvents catalogue arguments rows program).last
        ((dead_neighbour_comparison catalogue arguments rows program otherProgram).executions
          count ⟨rfl, dead⟩ run)) =
        observe ((Interface.EventMultiplicity.asynchronous (activationEvents catalogue arguments rows program)
          (activationEvents catalogue arguments rows otherProgram)).last run).1 := by
  let comparison := dead_neighbour_comparison catalogue arguments rows program otherProgram
  refine ⟨comparison.execution_word ⟨rfl, dead⟩ run, ?_⟩
  exact congrArg observe (comparison.execution_last ⟨rfl, dead⟩ run).1.symm

/-- Publication transports the actual activation information. A reader must
solve its own knowledge and that information jointly at the supplied opening. -/
theorem activation_publication_models_iff
    (state : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (stored : R → Closure (Contextual.Terms S) state.frame) (selected : R) (output : O)
    (reader : RuleSyntax.State (Contextual.Terms S) O) (program : Program (Contextual.Terms S))
    (member : Hosting.Alternatives.Worlds.snapshot
      ((Rows.activation state rows stored selected output).result (Frames.contextual S)).toState
      (((Rows.activation state rows stored selected output).result (Frames.contextual S)).label output) ∈ program)
    (extra : Frame S)
    (opening : Assignment
      (Contextual.extend S state.frame (stored selected).schema.locals).arity
      (Contextual.extend S reader.frame extra).arity) (selection : Selection O)
    (seen : List (Finset O)) {target : Frame S}
    (point : Assignment (Contextual.extend S reader.frame extra).arity target.arity) :
    (Frames.contextual S).Models point
      ((⟨Hosting.Alternatives.Worlds.snapshot
        ((Rows.activation state rows stored selected output).result (Frames.contextual S)).toState
        (((Rows.activation state rows stored selected output).result (Frames.contextual S)).label output),
        member, extra, opening, selection, seen⟩ :
          Firing O (Contextual.declarations S) program reader.frame).information (Frames.contextual S) reader) ↔
      (Frames.contextual S).Models
          (Assignment.compose point (Contextual.weakenNames S reader.frame extra)) reader.knowledge ∧
        (Frames.contextual S).Models (Assignment.compose point opening)
          ((Rows.activation state rows stored selected output).result (Frames.contextual S)).knowledge :=
  RuleSyntax.Worlds.snapshot_models_iff (X := Frames.contextual S) (E := Contextual.declarations S)
    ((Rows.activation state rows stored selected output).result (Frames.contextual S)).toState reader
    (((Rows.activation state rows stored selected output).result (Frames.contextual S)).label output)
    member extra opening selection seen point

namespace Example

open Rows.Example (signature schema initial stored firstResult secondResult)

def catalogue (_ : Bool) := schema
def anchors (_ : Bool) : List Nat := [2]
abbrev policy := activationEvents catalogue (anchoredArguments anchors) ({false, true} : Finset Bool)
def program : Program (Contextual.Terms signature) := {schema.toRule}

def firstChoice : (policy program).Choice initial :=
  ⟨false, 0, Set.mem_singleton _, Rows.Example.first_admitted⟩

def otherOrigin : (policy program).Choice initial :=
  ⟨true, 0, Set.mem_singleton _,
    Rows.activation_admitted_of_reading initial {false, true} stored true 0
      (by decide) (by decide) rfl Rows.Example.caller Rows.Example.initial_known
      (observe (Rows.Example.closedBody 7 0)) (Rows.Example.reading 0)⟩

def secondChoice : (policy program).Choice firstResult.toState :=
  ⟨false, 1, Set.mem_singleton _, Rows.Example.second_admitted⟩

def repeatedEvents : (policy program).Execution 2 initial :=
  ⟨firstChoice, secondChoice, PUnit.unit⟩

theorem repeated_events_are_actual : (policy program).last repeatedEvents = secondResult.toState := rfl

/-- Identical code, action and successor do not erase the two authored schema
occurrences. Their distinct Type-valued choices remain separately countable. -/
theorem distinct_origins_same_successor :
    firstChoice ≠ otherOrigin ∧
      (policy program).action initial firstChoice = (policy program).action initial otherOrigin ∧
      (policy program).next initial firstChoice = (policy program).next initial otherOrigin := by
  refine ⟨?_, rfl, rfl⟩
  intro same
  have impossible := congrArg Choice.selected same
  cases impossible

theorem actual_provider_coherent :
    anchoredArguments anchors firstResult.toState false =
      (anchoredArguments anchors initial false).map
        (instantiateObservation (Contextual.weakenNames signature initial.frame schema.locals)) :=
  live_anchored_arguments_coherent catalogue anchors {false, true} initial false false 0
    (by intro anchor member; have same := List.mem_singleton.mp member; subst anchor; decide)
    (by decide)

def deadState : RuleSyntax.State (Contextual.Terms signature) Nat :=
  ⟨Rows.Example.target,
    [(observe (Rows.Example.atom (Names := Empty) (context := []) 0), observe (Rows.Example.atom (Names := Empty) (context := []) 1))],
    ∅, fun _ => observe (Rows.Example.atom (Names := Empty) (context := []) 0)⟩

theorem deadState_unsolvable : ¬ (Frames.contextual signature).Solvable deadState.knowledge := by
  rintro ⟨target, point, model⟩
  have unequal := model
    (observe (Rows.Example.atom (Names := Empty) (context := []) 0),
      observe (Rows.Example.atom (Names := Empty) (context := []) 1)) (List.mem_singleton_self _)
  change observe (Term.op (S := ContextualFamily.signature signature target.arity) (Γ := [])
      (.inl (.atom 0)) .nil) =
    observe (Term.op (S := ContextualFamily.signature signature target.arity) (Γ := [])
      (.inl (.atom 1)) .nil) at unequal
  have heads := (Term.op.inj (observe_injective unequal)).1
  have impossible : (0 : Nat) = 1 := Rows.Example.Operator.atom.inj (Sum.inl.inj heads)
  omega

theorem first_fires_beside_dead :
    RuleSyntax.Worlds.Fires policy
      ⟨{⟨program, initial⟩, ⟨program, deadState⟩}, ∅⟩
      ⟨{⟨program, firstResult.toState⟩, ⟨program, deadState⟩}, ∅⟩ := by
  exact RuleSyntax.Worlds.Fires.fire (family := policy) {⟨program, deadState⟩} ∅ ⟨program, initial⟩
    ⟨firstChoice.selected, firstChoice.output, Set.mem_union_left _ firstChoice.visible, firstChoice.admitted⟩

theorem counted_dead_neighbour :
    Interface.EventMultiplicity.Bisimilar
      (Interface.EventMultiplicity.asynchronous (policy program) (policy program))
      (initial, deadState) (policy program) initial :=
  ⟨_, ⟨dead_neighbour_comparison catalogue (anchoredArguments anchors) {false, true} program program⟩,
    rfl, deadState_unsolvable⟩

end Example

#print axioms local_program_monotone
#print axioms local_no_events_at_inconsistent
#print axioms one_world_activation_iff
#print axioms activation_beside
#print axioms dead_neighbour_comparison
#print axioms dead_neighbour_observer
#print axioms choice_realizes_reading
#print axioms anchored_arguments_coherent
#print axioms activation_publication_models_iff
#print axioms Example.repeated_events_are_actual
#print axioms Example.distinct_origins_same_successor
#print axioms Example.actual_provider_coherent
#print axioms Example.counted_dead_neighbour

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.Worlds

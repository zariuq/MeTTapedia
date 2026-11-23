import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.FailurePropagation

/-!
# A separate outcome channel and library handlers

The kernel preserves a producer's channel. It never decides control from the
spelling of a value. Library handlers implement sequencing and observation.
Incomplete is a third event, preserving partial occurrences and a cause rather
than pretending that enumeration finished.

The cost model counts base work, additional channel work and boundary setup
separately. Failure-free native transitions add no channel work or value
metadata. Installing a dynamic observation boundary is a separate constant;
the model does not call handler dispatch or processor instructions free.
These are interface/algebra contracts, not a C refinement theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Failures.OutcomeKernel

open Observation

inductive CutReason where
  | budget
  | fuel
  | noVerdict
  | cancelled
  | capacity
  | invalidated
  deriving DecidableEq, Repr

structure Cut where
  whereAt : Data
  reason : CutReason
  detail : Data
  deriving DecidableEq, Repr

def Cut.diagnostic (cut : Cut) : Diagnostic :=
  ⟨cut.whereAt, .incomplete, cut.detail⟩

/-- A producer event, distinct from its printable payload. -/
inductive Event where
  | value (payload : Data)
  | raised (diagnostic : Diagnostic)
  | incomplete (cut : Cut)
  deriving DecidableEq, Repr

abbrev Stream := List Event

def Event.asData : Event → Data
  | .value payload => payload
  | .raised diagnostic => diagnostic.surface
  | .incomplete cut => cut.diagnostic.surface

/-- Only explicit observation maps the channel to a data description. -/
def observeData (events : Stream) : List Data := events.map Event.asData

/-- Minimal finite kernel syntax. A handler sees the producer's actual event;
an observer delimits an ordered finite readout, including any unfinished cut. -/
inductive Program where
  | value (payload : Data)
  | zero
  | raised (diagnostic : Diagnostic)
  | incomplete (cut : Cut)
  | native (events : Stream)
  | choice (left right : Program)
  | handle (source : Program) (handler : Event → Program)
  | observe (source : Program) (observer : Stream → Program)

def run : Program → Stream
  | .value payload => [.value payload]
  | .zero => []
  | .raised diagnostic => [.raised diagnostic]
  | .incomplete cut => [.incomplete cut]
  | .native events => events
  | .choice left right => run left ++ run right
  | .handle source handler => (run source).flatMap fun event => run (handler event)
  | .observe source observer => run (observer (run source))

namespace Library

/-- This propagation policy belongs to the library, not ordinary evaluation. -/
def bind (source : Program) (next : Data → Program) : Program :=
  .handle source fun
    | .value payload => next payload
    | .raised diagnostic => .raised diagnostic
    | .incomplete cut => .incomplete cut

def catchFailure (source : Program) : Program :=
  .handle source fun event => .value event.asData

def collapse (source : Program) : Program :=
  .observe source fun events => .value (tuple (observeData events))

def emitValues : List Data → Program
  | [] => .zero
  | first :: rest => .choice (.value first) (emitValues rest)

def unique (source : Program) : Program :=
  .observe source fun events => emitValues (uniqueData [] (observeData events))

def observe2 (left right : Program) (operation : List Data → List Data → List Data) : Program :=
  .observe left fun first => .observe right fun second =>
    emitValues (operation (observeData first) (observeData second))

def intersection (left right : Program) : Program :=
  observe2 left right fun first second => first.filter fun value => value ∈ second

def subtraction (left right : Program) : Program :=
  observe2 left right fun first second => first.filter fun value => value ∉ second

def ifThenElse (condition : Program) (yes no : Program) (whereAt : Data) : Program :=
  bind condition fun
    | .boolean true => yes
    | .boolean false => no
    | other => .incomplete ⟨whereAt, .noVerdict, other⟩

end Library

def sequence (events : Stream) (next : Data → Stream) : Stream :=
  events.flatMap fun
    | .value payload => next payload
    | .raised diagnostic => [.raised diagnostic]
    | .incomplete cut => [.incomplete cut]

theorem library_bind_implements_sequence (source : Program) (next : Data → Program) :
    run (Library.bind source next) = sequence (run source) (fun value => run (next value)) := by
  simp only [Library.bind, run, sequence]
  apply List.flatMap_congr
  intro event member
  cases event <;> rfl

theorem propagation (diagnostic : Diagnostic) (next : Data → Program) :
    run (Library.bind (.raised diagnostic) next) = [.raised diagnostic] := rfl

theorem incomplete_is_not_a_value (cut : Cut) (next : Data → Program) :
    run (Library.bind (.incomplete cut) next) = [.incomplete cut] := rfl

theorem earliest_failure (first second : Diagnostic) (finish : Data → Program) :
    run (Library.bind (.raised first) (fun _ => Library.bind (.raised second) finish)) =
      [.raised first] := rfl

theorem choices_keep_failures (diagnostic : Diagnostic) (value : Data)
    (next : Data → Program) :
    run (Library.bind (.choice (.raised diagnostic) (.value value)) next) =
      .raised diagnostic :: run (next value) := by
  simp [Library.bind, run, List.flatMap]

theorem value_output_cannot_catch_a_raise (diagnostic : Diagnostic) :
    run (Library.bind (.raised diagnostic) Program.value) = [.raised diagnostic] := rfl

theorem error_data_is_ordinary (diagnostic : Diagnostic) (next : Data → Program) :
    run (Library.bind (.value diagnostic.surface) next) = run (next diagnostic.surface) := by
  simp [Library.bind, run]

theorem native_provenance_is_not_surface_syntax (diagnostic : Diagnostic) :
    run (.native [.value diagnostic.surface]) ≠ run (.native [.raised diagnostic]) := by
  simp [run]

theorem catch_observes_a_failure (diagnostic : Diagnostic) :
    run (Library.catchFailure (.raised diagnostic)) = [.value diagnostic.surface] := rfl

theorem catch_does_not_run_a_later_consumer (first later : Diagnostic) :
    run (Library.bind (Library.catchFailure (.raised first)) (fun _ => .raised later)) =
      [.raised later] := rfl

theorem collapse_preserves_all_occurrences (events : Stream) :
    run (Library.collapse (.native events)) = [.value (tuple (observeData events))] := rfl

theorem observation_preserves_length (events : Stream) :
    (observeData events).length = events.length := by simp [observeData]

theorem collapse_keeps_partial_progress (prior : Stream) (cut : Cut) :
    run (Library.collapse (.native (prior ++ [.incomplete cut]))) =
      [.value (tuple (observeData prior ++ [cut.diagnostic.surface]))] := by
  simp [Library.collapse, run, observeData, Event.asData]

theorem zero_unit_empty_are_distinct (scope : Data) :
    run .zero = [] ∧ run (.value .unit) = [.value .unit] ∧
      run (.value (.empty scope)) = [.value (.empty scope)] ∧
      run .zero ≠ run (.value (.empty scope)) := by simp [run]

theorem incomplete_is_not_zero (cut : Cut) :
    run (.incomplete cut) ≠ run .zero := by simp [run]

theorem incomplete_observation_keeps_its_kind (cut : Cut) :
    cut.diagnostic.kind = .incomplete := rfl

theorem sequence_preserves_each_raised_occurrence (events : Stream)
    (diagnostic : Diagnostic) (present : Event.raised diagnostic ∈ events)
    (next : Data → Stream) : Event.raised diagnostic ∈ sequence events next := by
  apply List.mem_flatMap.mpr
  exact ⟨.raised diagnostic, present, by simp⟩

theorem sequence_preserves_each_incomplete_occurrence (events : Stream)
    (cut : Cut) (present : Event.incomplete cut ∈ events)
    (next : Data → Stream) : Event.incomplete cut ∈ sequence events next := by
  apply List.mem_flatMap.mpr
  exact ⟨.incomplete cut, present, by simp⟩

/-- Sequence neither rewrites an existing diagnostic's kind nor converts
an exhausted branch into zero. New failures may come from the continuation. -/
theorem sequence_keeps_duplicate_failures (diagnostic : Diagnostic)
    (next : Data → Stream) :
    sequence [.raised diagnostic, .raised diagnostic] next =
      [.raised diagnostic, .raised diagnostic] := rfl

theorem error_data_and_raised_share_only_their_description (diagnostic : Diagnostic) :
    Event.asData (.value diagnostic.surface) = Event.asData (.raised diagnostic) ∧
      Event.value diagnostic.surface ≠ Event.raised diagnostic := by
  exact ⟨rfl, by simp⟩

theorem emitted_values_are_values (values : List Data) :
    run (Library.emitValues values) = values.map Event.value := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [Library.emitValues, run, ih]

theorem unique_is_a_data_handler (source : Program) :
    run (Library.unique source) =
      (uniqueData [] (observeData (run source))).map Event.value := by
  simp [Library.unique, run, emitted_values_are_values]

theorem unique_keeps_one_whole_diagnostic (diagnostic : Diagnostic) :
    run (Library.unique (.choice (.raised diagnostic) (.raised diagnostic))) =
      [.value diagnostic.surface] := by
  simp [unique_is_a_data_handler, run, observeData, Event.asData, uniqueData]

theorem intersection_handles_failures_as_data (diagnostic : Diagnostic) :
    run (Library.intersection (.raised diagnostic) (.raised diagnostic)) =
      [.value diagnostic.surface] := by
  simp [Library.intersection, Library.observe2, run, observeData, Event.asData,
    emitted_values_are_values]

theorem subtraction_can_exclude_observed_failure (diagnostic : Diagnostic) :
    run (Library.subtraction (.raised diagnostic) (.raised diagnostic)) = [] := by
  simp [Library.subtraction, Library.observe2, run, observeData, Event.asData,
    emitted_values_are_values]

theorem no_verdict_is_incomplete (whereAt other : Data)
    (notTrue : other ≠ .boolean true) (notFalse : other ≠ .boolean false) (yes no : Program) :
    run (Library.ifThenElse (.value other) yes no whereAt) =
      [.incomplete ⟨whereAt, .noVerdict, other⟩] := by
  cases other <;> simp_all [Library.ifThenElse, Library.bind, run]

/-- Failure-free base computations use their usual value algebra. -/
inductive Base where
  | value (payload : Data)
  | zero
  | choice (left right : Base)
  | bind (source : Base) (next : Data → Base)

def baseRun : Base → List Data
  | .value payload => [payload]
  | .zero => []
  | .choice left right => baseRun left ++ baseRun right
  | .bind source next => (baseRun source).flatMap fun value => baseRun (next value)

def liftBase : Base → Program
  | .value payload => .value payload
  | .zero => .zero
  | .choice left right => .choice (liftBase left) (liftBase right)
  | .bind source next => Library.bind (liftBase source) fun value => liftBase (next value)

theorem conservative_extension (base : Base) :
    run (liftBase base) = (baseRun base).map Event.value := by
  induction base with
  | value payload => rfl
  | zero => rfl
  | choice left right il ir => simp [liftBase, run, baseRun, il, ir]
  | bind source next isource inext =>
    simp [liftBase, Library.bind, run, baseRun, isource, inext,
      List.flatMap_map, List.map_flatMap]

/-- Values, including diagnostic-shaped data, need no new channel metadata.
The base native step already provides its value and its charged work. -/
structure BaseState where
  values : List Data := []
  work : Nat := 0
  deriving DecidableEq

structure KernelState where
  base : BaseState := {}
  controls : Stream := []
  channelWork : Nat := 0
  boundaries : Nat := 0

def baseStep (state : BaseState) (value : Data) (work : Nat) : BaseState :=
  ⟨state.values ++ [value], state.work + work⟩

def kernelStep (state : KernelState) (event : Event) (work : Nat) : KernelState :=
  match event with
  | .value value => { state with base := baseStep state.base value work }
  | .raised diagnostic =>
      { state with
        base := { state.base with work := state.base.work + work }
        controls := state.controls ++ [.raised diagnostic]
        channelWork := state.channelWork + 1 }
  | .incomplete cut =>
      { state with
        base := { state.base with work := state.base.work + work }
        controls := state.controls ++ [.incomplete cut]
        channelWork := state.channelWork + 1 }

def baseSteps (state : BaseState) : List (Data × Nat) → BaseState
  | [] => state
  | (value, work) :: rest => baseSteps (baseStep state value work) rest

def kernelValueSteps (state : KernelState) : List (Data × Nat) → KernelState
  | [] => state
  | (value, work) :: rest => kernelValueSteps (kernelStep state (.value value) work) rest

theorem value_steps_preserve_base_work (state : KernelState) (steps : List (Data × Nat)) :
    (kernelValueSteps state steps).base = baseSteps state.base steps := by
  induction steps generalizing state with
  | nil => rfl
  | cons step rest ih => cases step; simp [kernelValueSteps, baseSteps, kernelStep, ih]

theorem failure_free_steps_add_no_channel_work (state : KernelState)
    (steps : List (Data × Nat)) :
    (kernelValueSteps state steps).channelWork = state.channelWork ∧
      (kernelValueSteps state steps).controls = state.controls ∧
      (kernelValueSteps state steps).boundaries = state.boundaries := by
  induction steps generalizing state with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons step rest ih =>
    rcases step with ⟨value, work⟩
    simpa [kernelValueSteps, kernelStep] using (ih (kernelStep state (.value value) work))

def installBoundary (state : KernelState) : KernelState :=
  { state with boundaries := state.boundaries + 1 }

theorem boundary_setup_is_not_hidden (state : KernelState) :
    (installBoundary state).boundaries = state.boundaries + 1 := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Failures.OutcomeKernel

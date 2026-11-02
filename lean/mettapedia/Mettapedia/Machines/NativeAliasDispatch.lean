import Mettapedia.Machines.NativeCallReturn
import Mettapedia.Machines.OwnedPullDriver

/-!
# Native aliases preserve entered control and occurrence delivery

The source distinguishes refusal before entry from a producer that entered and
returned failure, interrupted control, a suspended answer, or a value frontier.
The target executes the chosen producer with the maintained explicit child
driver and delivers its original source with the maintained array cursor.
Public-call presentation changes scalar packets only; a frontier container is
never mistaken for one scalar error, and delayed obligations stay attached.

The refinement preserves arbitrary committed producer effects, the actual world,
ordered publications, residual occurrences, context and terminal cause. Fallback
is selected before producer entry and cannot be inferred from a missing atom.
The primitive worker, error-blame predicate, C pointer/arena lifetime and native
implementation correspondence remain qualification obligations. Expression-role
occurrences retain their role here; this model does not execute pending syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NativeAliasDispatch

open NativeCallReturn

variable {Value Fault Delay Context Effect World : Type}

structure Presentation (Value Fault : Type) where
  value : Value → Value
  fault : Fault → Fault

def Presentation.identity : Presentation Value Fault := ⟨id, id⟩

def presentPacket (presentation : Presentation Value Fault) :
    Packet Value Fault Delay → Packet Value Fault Delay
  | .value role value => .value role (presentation.value value)
  | .raised fault => .raised (presentation.fault fault)
  | .conditional value delayed => .conditional (presentation.value value) delayed

/-- Only a scalar packet is eligible for public-call presentation. A frontier
is a source of occurrences, regardless of the spelling of its first element. -/
def presentSource (presentation : Presentation Value Fault) :
    Source Value Fault Delay → Source Value Fault Delay
  | .one packet => .one (presentPacket presentation packet)
  | .frontier role values => .frontier role values
  | .failure => .failure
  | .interrupted => .interrupted
  | .invalid => .invalid

def presentCursor (presentation : Presentation Value Fault)
    (cursor : Cursor Value Fault Delay Context) : Cursor Value Fault Delay Context :=
  {cursor with source := presentSource presentation cursor.source}

def presentReturned (presentation : Presentation Value Fault)
    (source : Source Value Fault Delay) (item : Returned Value Fault Delay Context) :
    Returned Value Fault Delay Context :=
  match source with
  | .one _ => ⟨item.1, presentPacket presentation item.2⟩
  | _ => item

/-- The target indexes the original producer storage and carries its actual
cursor forward; presentation neither admits nor executes the producer. -/
def next (presentation : Presentation Value Fault)
    (cursor : Cursor Value Fault Delay Context) :
    Pull (Returned Value Fault Delay Context) (Cursor Value Fault Delay Context) :=
  match NativeCallReturn.read cursor with
  | .returned item rest => .returned (presentReturned presentation cursor.source item) rest
  | .stopped reason => .stopped reason

theorem next_present (presentation : Presentation Value Fault)
    (cursor : Cursor Value Fault Delay Context) :
    (next presentation cursor).mapState (presentCursor presentation) =
      NativeCallReturn.read (presentCursor presentation cursor) := by
  rcases cursor with ⟨source, context, position⟩
  cases source with
  | one packet =>
      by_cases first : position = 0 <;>
        simp [next, NativeCallReturn.read, first, presentCursor, presentSource,
          presentReturned, Pull.mapState]
  | frontier role values =>
      cases found : values[position]? <;>
        simp [next, NativeCallReturn.read, found, presentCursor, presentSource,
          presentReturned, Pull.mapState]
  | failure => rfl
  | interrupted => rfl
  | invalid => rfl

def residual (presentation : Presentation Value Fault)
    (cursor : Cursor Value Fault Delay Context) :=
  NativeCallReturn.residual (presentCursor presentation cursor)

private theorem mapState_twice {Item State Other Last : Type}
    (first : State → Other) (second : Other → Last) (pull : Pull Item State) :
    (pull.mapState first).mapState second = pull.mapState (second ∘ first) := by
  cases pull <;> rfl

/-- The source consumes a presented occurrence list; the native alias reads
its unmodified producer cursor. Every next transition commutes with decoding. -/
theorem next_refines (presentation : Presentation Value Fault)
    (cursor : Cursor Value Fault Delay Context) :
    (next presentation cursor).mapState (residual presentation) =
      referenceRead (residual presentation cursor) := by
  have concrete := congrArg (Pull.mapState NativeCallReturn.residual)
    (next_present presentation cursor)
  rw [NativeCallReturn.read_refines] at concrete
  simp only [mapState_twice, Function.comp_def] at concrete
  exact concrete

def advance (presentation : Presentation Value Fault) :
    Nat → Cursor Value Fault Delay Context →
      List (Returned Value Fault Delay Context) × Cursor Value Fault Delay Context
  | 0, cursor => ([], cursor)
  | count + 1, cursor =>
      match next presentation cursor with
      | .stopped _ => ([], cursor)
      | .returned item rest =>
          let later := advance presentation count rest
          (item :: later.1, later.2)

private theorem advance_present (presentation : Presentation Value Fault)
    (allowance : Nat) (cursor : Cursor Value Fault Delay Context) :
    (advance presentation allowance cursor).1 =
        (NativeCallReturn.advance allowance (presentCursor presentation cursor)).1 ∧
      presentCursor presentation (advance presentation allowance cursor).2 =
        (NativeCallReturn.advance allowance (presentCursor presentation cursor)).2 := by
  induction allowance generalizing cursor with
  | zero => exact ⟨rfl, rfl⟩
  | succ allowance ih =>
      have commutes := next_present presentation cursor
      cases step : next presentation cursor with
      | stopped reason =>
          simp only [step, Pull.mapState] at commutes
          simp [advance, step, NativeCallReturn.advance, ← commutes]
      | returned item rest =>
          simp only [step, Pull.mapState] at commutes
          obtain ⟨values, state⟩ := ih rest
          simp [advance, step, NativeCallReturn.advance, ← commutes, values, state]

/-- Bounded alias delivery keeps the precise unpublished suffix and terminal
cause, including duplicates and suspended obligations. -/
theorem advance_refines (presentation : Presentation Value Fault)
    (allowance : Nat) (cursor : Cursor Value Fault Delay Context) :
    (advance presentation allowance cursor).1 = (residual presentation cursor).1.take allowance ∧
      residual presentation (advance presentation allowance cursor).2 =
        ((residual presentation cursor).1.drop allowance, (residual presentation cursor).2) := by
  obtain ⟨published, retained⟩ := advance_present presentation allowance cursor
  obtain ⟨initial, suffix⟩ := NativeCallReturn.advance_exact allowance
    (presentCursor presentation cursor)
  exact ⟨published.trans initial, by simpa only [residual, retained] using suffix⟩

/-- A physical delivery split resumes the retained cursor. Earlier occurrences
are neither republished nor obtained by re-entering the producer. -/
theorem advance_add (presentation : Presentation Value Fault)
    (first later : Nat) (cursor : Cursor Value Fault Delay Context) :
    advance presentation (first + later) cursor =
      let earlier := advance presentation first cursor
      let suffix := advance presentation later earlier.2
      (earlier.1 ++ suffix.1, suffix.2) := by
  induction first generalizing cursor with
  | zero => simp [advance]
  | succ first ih =>
      cases step : next presentation cursor with
      | stopped reason =>
          have inert : advance presentation later cursor = ([], cursor) := by
            cases later <;> simp [advance, step]
          simp [advance, step, inert, Nat.succ_add]
      | returned item rest =>
          simp [advance, step, Nat.succ_add, ih rest, List.cons_append]

/-- Admission names the route before its work runs. Entered failure has no
constructor that could be confused with this pre-entry refusal. -/
inductive Attempt (Value Fault Delay Effect : Type) where
  | declined (fallback : OwnedPullDriver.Program (Source Value Fault Delay) Effect)
  | entered (producer : OwnedPullDriver.Program (Source Value Fault Delay) Effect)

inductive Runs : Attempt Value Fault Delay Effect → List Effect →
    Source Value Fault Delay → Bool → Prop where
  | declined {work : OwnedPullDriver.Program (Source Value Fault Delay) Effect}
      {effects : List Effect} {source : Source Value Fault Delay}
      (run : OwnedPullDriver.Runs work effects source) :
      Runs (.declined work) effects source true
  | entered {work : OwnedPullDriver.Program (Source Value Fault Delay) Effect}
      {effects : List Effect} {source : Source Value Fault Delay}
      (run : OwnedPullDriver.Runs work effects source) :
      Runs (.entered work) effects source false

structure Observation (Value Fault Delay Context Effect World : Type) where
  world : World
  effects : List Effect
  published : List (Returned Value Fault Delay Context)
  pending : List (Returned Value Fault Delay Context)
  stop : Stop
  fallback : Bool
  deriving DecidableEq, Repr

/-- Recursive producer derivation followed by independent occurrence meaning. -/
def reference (action : Effect → World → World)
    (presentation : Presentation Value Fault) (context : Context)
    (world : World) (effects : List Effect) (source : Source Value Fault Delay)
    (fallback : Bool) (allowance : Nat) :
    Observation Value Fault Delay Context Effect World :=
  let presented := if fallback then source else presentSource presentation source
  let returns := meaning presented context
  ⟨OwnedPullDriver.interpret action effects world, effects,
    returns.1.take allowance, returns.1.drop allowance, returns.2, fallback⟩

/-- Entry selects one retained producer. Producer completion then creates one
occurrence cursor, even when the reached source contains no value at all. -/
def target (action : Effect → World → World)
    (presentation : Presentation Value Fault) (context : Context)
    (world : World) (attempt : Attempt Value Fault Delay Effect)
    (fuel allowance : Nat) : Option (Observation Value Fault Delay Context Effect World) :=
  let chosen := match attempt with
    | .declined work => (true, work)
    | .entered work => (false, work)
  let reached := OwnedPullDriver.Session.resume action fuel
    (OwnedPullDriver.Session.begin chosen.2 world)
  match reached.residual with
  | some ⟨.done source, []⟩ =>
      let policy := if chosen.1 then Presentation.identity else presentation
      let cursor : Cursor Value Fault Delay Context := ⟨source, context, 0⟩
      let delivered := advance policy allowance cursor
      let retained := residual policy delivered.2
      some ⟨reached.world, reached.committed, delivered.1,
        retained.1, retained.2, chosen.1⟩
  | _ => none

private theorem identity_source (source : Source Value Fault Delay) :
    presentSource Presentation.identity source = source := by
  cases source with
  | one packet => cases packet <;> rfl
  | frontier => rfl
  | failure => rfl
  | interrupted => rfl
  | invalid => rfl

private theorem delivered_reference (presentation : Presentation Value Fault)
    (context : Context) (source : Source Value Fault Delay) (allowance : Nat) :
    let cursor : Cursor Value Fault Delay Context := ⟨source, context, 0⟩
    (advance presentation allowance cursor).1 =
        (meaning (presentSource presentation source) context).1.take allowance ∧
      residual presentation (advance presentation allowance cursor).2 =
        ((meaning (presentSource presentation source) context).1.drop allowance,
         (meaning (presentSource presentation source) context).2) := by
  simpa [residual, NativeCallReturn.residual, presentCursor] using
    advance_refines presentation allowance
      (⟨source, context, 0⟩ : Cursor Value Fault Delay Context)

/-- Actual explicit producer transitions refine the independent recursive
execution. No post-entry packet shape can introduce fallback or replay. -/
theorem dispatch_refines (action : Effect → World → World)
    (presentation : Presentation Value Fault) (context : Context) (world : World)
    {attempt : Attempt Value Fault Delay Effect} {effects : List Effect}
    {source : Source Value Fault Delay} {fallback : Bool}
    (run : Runs attempt effects source fallback) (allowance : Nat) :
    ∃ fuel, target action presentation context world attempt fuel allowance =
      some (reference action presentation context world effects source fallback allowance) := by
  cases run with
  | declined run =>
      obtain ⟨fuel, reached⟩ := OwnedPullDriver.Session.refines_runs action world run
      refine ⟨fuel, ?_⟩
      obtain ⟨published, retained⟩ := delivered_reference
        (Presentation.identity : Presentation Value Fault) context source allowance
      simp only [identity_source] at published retained
      simp only [target, reached]
      simp only [reference, ↓reduceIte]
      rw [published, retained]
  | entered run =>
      obtain ⟨fuel, reached⟩ := OwnedPullDriver.Session.refines_runs action world run
      refine ⟨fuel, ?_⟩
      obtain ⟨published, retained⟩ := delivered_reference presentation context source allowance
      simp only [target, reached]
      simp only [reference, Bool.false_eq_true, ↓reduceIte]
      rw [published, retained]

/-- Entered empty answers, interruption and malformed returns cannot turn into
pre-entry refusal. This invariant does not assume that the packet has an atom. -/
theorem entered_never_falls_back (action : Effect → World → World)
    (presentation : Presentation Value Fault) (context : Context) (world : World)
    (producer : OwnedPullDriver.Program (Source Value Fault Delay) Effect)
    (fuel allowance : Nat) (observed : Observation Value Fault Delay Context Effect World)
    (reached : target action presentation context world (.entered producer) fuel allowance =
      some observed) : observed.fallback = false := by
  simp only [target] at reached
  split at reached
  · cases reached
    rfl
  · contradiction

namespace Controls

inductive Payload where
  | plain (value : Nat)
  | error (call : Nat) (payload : Nat)
  deriving DecidableEq, Repr

abbrev TestSource := Source Payload Nat Nat
abbrev TestCursor := Cursor Payload Nat Nat Nat
abbrev TestAttempt := Attempt Payload Nat Nat Nat
abbrev TestObservation := Observation Payload Nat Nat Nat Nat (List Nat)

def presentation : Presentation Payload Nat := {
  value := fun value => match value with
    | .error _ payload => .error 99 payload
    | value => value
  fault := fun _ => 99 }

def action (event : Nat) (world : List Nat) : List Nat := world ++ [event]

def failureWork : TestAttempt := .entered (.emit 7 (.done .failure))
def malformedWork : TestAttempt := .entered (.emit 7 (.done .invalid))
def fallbackWork : TestAttempt := .declined (.emit 8 (.done (.one (.value .completed (.plain 1)))))

theorem entered_failure_keeps_effect_and_never_falls_back :
    let observed := target action presentation 4 [] failureWork 2 10
    observed = some (⟨[7], [7], [], [], .complete, false⟩ : TestObservation) ∧
      target action presentation 4 [] fallbackWork 2 10 =
        some (⟨[8], [8], [(4, .value .completed (.plain 1))], [], .complete, true⟩ : TestObservation) := by
  decide +kernel

theorem null_atom_fallback_would_replay_effects :
    let observed := target action presentation 4 [] failureWork 2 10
    observed.map Observation.world = some [7] ∧
      some (action 7 [7]) = some [7, 7] ∧
      some (action 7 [7]) ≠ observed.map Observation.world := by
  decide +kernel

theorem empty_frontier_is_entered_not_refused :
    let work : TestAttempt := .entered (.emit 7 (.done (.frontier .completed #[])))
    target action presentation 4 [] work 2 10 =
      some (⟨[7], [7], [], [], .complete, false⟩ : TestObservation) := by
  decide +kernel

theorem raised_tag_and_context_survive_presentation :
    let source : TestSource := .one (.raised 2)
    next presentation (⟨source, 4, 0⟩ : TestCursor) =
      .returned (4, .raised 99) ⟨source, 4, 1⟩ := by
  decide +kernel

theorem scalar_presentation_keeps_suspension :
    let source : TestSource := .one (.conditional (.error 2 3) 77)
    next presentation (⟨source, 4, 0⟩ : TestCursor) =
      .returned (4, .conditional (.error 99 3) 77) ⟨source, 4, 1⟩ ∧
      presentPacket presentation (.conditional (.error 2 3) 77) ≠
        (.value .completed (.error 99 3) : Packet Payload Nat Nat) := by
  decide +kernel

theorem frontier_is_not_one_scalar_error :
    let source : TestSource := .frontier .completed #[.error 2 3, .plain 5, .plain 5]
    (advance presentation 2 (⟨source, 4, 0⟩ : TestCursor)).1 =
      [(4, .value .completed (.error 2 3)), (4, .value .completed (.plain 5))] ∧
      (residual presentation (advance presentation 2
        (⟨source, 4, 0⟩ : TestCursor)).2).1 = [(4, .value .completed (.plain 5))] := by
  decide +kernel

theorem malformed_and_interrupted_are_not_exhaustion :
    target action presentation 4 [] malformedWork 2 10 =
      some (⟨[7], [7], [], [], .hostFailure, false⟩ : TestObservation) ∧
      (residual presentation (⟨.interrupted, 4, 0⟩ : TestCursor)).2 = .cancelled ∧
      (residual presentation (⟨.failure, 4, 0⟩ : TestCursor)).2 = .complete := by
  decide +kernel

theorem code_and_error_data_keep_their_tags :
    let code : TestSource := .one (.value .expression (.plain 4))
    let data : TestSource := .one (.value .completed (.error 2 3))
    next presentation (⟨code, 4, 0⟩ : TestCursor) =
      .returned (4, .value .expression (.plain 4)) ⟨code, 4, 1⟩ ∧
      next presentation (⟨data, 4, 0⟩ : TestCursor) =
      .returned (4, .value .completed (.error 99 3)) ⟨data, 4, 1⟩ := by
  decide +kernel

theorem physical_zero_leaves_occurrences_pending :
    let source : TestSource := .one (.conditional (.plain 5) 77)
    advance presentation 0 (⟨source, 4, 0⟩ : TestCursor) = ([], ⟨source, 4, 0⟩) ∧
      (residual presentation (⟨source, 4, 0⟩ : TestCursor)).1 =
        [(4, .conditional (.plain 5) 77)] := by
  decide +kernel

end Controls
end Mettapedia.Machines.NativeAliasDispatch

#print axioms Mettapedia.Machines.NativeAliasDispatch.next_present
#print axioms Mettapedia.Machines.NativeAliasDispatch.next_refines
#print axioms Mettapedia.Machines.NativeAliasDispatch.advance_refines
#print axioms Mettapedia.Machines.NativeAliasDispatch.dispatch_refines
#print axioms Mettapedia.Machines.NativeAliasDispatch.advance_add
#print axioms Mettapedia.Machines.NativeAliasDispatch.entered_never_falls_back
#print axioms Mettapedia.Machines.NativeAliasDispatch.Controls.entered_failure_keeps_effect_and_never_falls_back
#print axioms Mettapedia.Machines.NativeAliasDispatch.Controls.null_atom_fallback_would_replay_effects
#print axioms Mettapedia.Machines.NativeAliasDispatch.Controls.scalar_presentation_keeps_suspension
#print axioms Mettapedia.Machines.NativeAliasDispatch.Controls.frontier_is_not_one_scalar_error
#print axioms Mettapedia.Machines.NativeAliasDispatch.Controls.malformed_and_interrupted_are_not_exhaustion
#print axioms Mettapedia.Machines.NativeAliasDispatch.Controls.physical_zero_leaves_occurrences_pending

#print axioms Mettapedia.Machines.NativeAliasDispatch.Controls.code_and_error_data_keep_their_tags

#print axioms Mettapedia.Machines.NativeAliasDispatch.Controls.empty_frontier_is_entered_not_refused
#print axioms Mettapedia.Machines.NativeAliasDispatch.Controls.raised_tag_and_context_survive_presentation

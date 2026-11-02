import Mettapedia.Machines.NativeCallReturn
import Mettapedia.Machines.OwnedPullDriver

/-!
# Owned foreign callbacks: interruption before guest continuation

The recursive reference observes an evaluator's completion and raised-control
fields before admitting any guest continuation. The target runs the maintained
explicit child driver, reads completed occurrences through `NativeCallReturn`,
then retains or releases the callback lease. An incomplete callback releases
that lease and yields to its query owner. A resume reports the same interruption
without retaining a computation that could be replayed. Owner close prunes any
remaining callback lease and executes the query's cleanup effects once.

The main refinement preserves the source entry, every ordered producer effect,
guest observation, actual world, cleanup effect, completion cause and final
ownership account. Effects and their world action are arbitrary; in particular
cleanup is neither assumed pure nor treated as rollback. Completed empty answers
are logical failure, completed Error-shaped payloads are data, and raised faults
remain available to a guest handler. Interruption admits none of those choices.

This is the owned yield-and-close protocol. It does not assert that a reserved
backend unwind bypasses catch recovery effects. Native SWI yieldability, foreign
control tags, pointer lifetimes, source debits, query-close failure, the supplied
cleanup trace and the C correspondence retain separate obligations. Guest-origin
yields and the nonyieldable backend-unwind fallback are outside this model.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ForeignCallbackInterruption

variable {Source Value Fault Cause Effect Owner World : Type}

structure Outcome (Value Fault Cause : Type) where
  values : Array Value
  incomplete : Option Cause
  raised : Option Fault
  deriving DecidableEq, Repr

inductive Decision (Value Fault Cause : Type) where
  | answers (values : List Value)
  | failure
  | raised (fault : Fault)
  | interrupted (cause : Cause)
  deriving DecidableEq, Repr

/-- Reference classification uses the evaluator's provenance, never the syntax
of a returned value. An incomplete frontier cannot certify logical failure. -/
def referenceDecision (outcome : Outcome Value Fault Cause) : Decision Value Fault Cause :=
  match outcome.incomplete, outcome.raised with
  | some cause, _ => .interrupted cause
  | none, some fault => .raised fault
  | none, none =>
      match outcome.values.toList with
      | [] => .failure
      | first :: rest => .answers (first :: rest)

private def completedValue (item : NativeCallReturn.Returned Value Fault Empty Unit) :
    Option Value :=
  match item.2 with
  | .value .completed value => some value
  | _ => none

/-- Private native delivery indexes the backing array. This operation does not
interpret source syntax or give partial values guest publication authority. -/
def nativeValues (values : Array Value) : List Value :=
  let cursor : NativeCallReturn.Cursor Value Fault Empty Unit :=
    ⟨.frontier .completed values, (), 0⟩
  (NativeCallReturn.advance values.size cursor).1.filterMap completedValue

private theorem native_values_exact (values : Array Value) :
    nativeValues (Fault := Fault) values = values.toList := by
  dsimp only [nativeValues]
  rw [(NativeCallReturn.advance_exact values.size
    (⟨.frontier .completed values, (), 0⟩ :
      NativeCallReturn.Cursor Value Fault Empty Unit)).1]
  have takeAll : values.toList.take values.size = values.toList :=
    List.take_of_length_le (by simp)
  simp [NativeCallReturn.residual, NativeCallReturn.meaning, ← List.map_take,
    List.filterMap_map, Function.comp_def, completedValue, takeAll]

def targetDecision (outcome : Outcome Value Fault Cause) : Decision Value Fault Cause :=
  match outcome.incomplete with
  | some cause => .interrupted cause
  | none =>
      match outcome.raised with
      | some fault => .raised fault
      | none =>
          match nativeValues (Fault := Fault) outcome.values with
          | [] => .failure
          | first :: rest => .answers (first :: rest)

/-- Completion-first native occurrence delivery refines direct classification. -/
theorem decision_refines (outcome : Outcome Value Fault Cause) :
    targetDecision outcome = referenceDecision outcome := by
  rcases outcome with ⟨values, incomplete, raised⟩
  cases incomplete <;> cases raised <;>
    simp [targetDecision, referenceDecision, native_values_exact]

inductive GuestEvent (Value Fault : Type) where
  | successBranch
  | failureBranch
  | published (values : List Value)
  | caught (fault : Fault)
  | uncaught (fault : Fault)
  deriving DecidableEq, Repr

/-- A caller chooses its behavior for completed answers, logical failure and
ordinary raised control. No caller continuation is supplied for interruption. -/
structure Guest (Value Fault : Type) where
  answers : List Value → List (GuestEvent Value Fault)
  failure : List (GuestEvent Value Fault)
  raised : Fault → List (GuestEvent Value Fault)
  keepAlternatives : Bool

def Guest.branch : Guest Value Fault where
  answers _ := [.successBranch]
  failure := [.failureBranch]
  raised fault := [.uncaught fault]
  keepAlternatives := true

def Guest.collect : Guest Value Fault where
  answers values := [.published values]
  failure := [.published []]
  raised fault := [.uncaught fault]
  keepAlternatives := false

def Guest.catchRaised : Guest Value Fault where
  answers values := [.published values]
  failure := [.published []]
  raised fault := [.caught fault]
  keepAlternatives := false

def guestTrace (guest : Guest Value Fault) : Decision Value Fault Cause →
    List (GuestEvent Value Fault)
  | .answers values => guest.answers values
  | .failure => guest.failure
  | .raised fault => guest.raised fault
  | .interrupted _ => []

private def keepsCallback (guest : Guest Value Fault) : Decision Value Fault Cause → Bool
  | .answers (_ :: _ :: _) => guest.keepAlternatives
  | _ => false

inductive Event (Source Value Fault Effect : Type) where
  | entered (source : Source)
  | producer (effect : Effect)
  | guest (event : GuestEvent Value Fault)
  | cleanup (effect : Effect)
  deriving DecidableEq, Repr

inductive Resource (Owner : Type) where
  | callback (owner : Owner)
  | query (owner : Owner)
  deriving DecidableEq, Repr

/-- A settled callback retains no evaluator program. Callback and query leases
are distinct even if the host uses the same owner identifier for both. -/
structure Session (Source Value Fault Cause Effect Owner World : Type) where
  decision : Decision Value Fault Cause
  callback : Option Owner
  query : Option Owner
  cleanup : List Effect
  world : World
  events : List (Event Source Value Fault Effect)
  released : List (Resource Owner)
  closed : Bool
  deriving DecidableEq, Repr

def prune (session : Session Source Value Fault Cause Effect Owner World) :
    Session Source Value Fault Cause Effect Owner World :=
  match session.callback with
  | none => session
  | some owner => { session with
      callback := none
      released := session.released ++ [.callback owner] }

/-- Only a live query lease owns the cleanup trace. Pruning callback storage
does not interpret that trace, and repeating owner close cannot interpret it. -/
def close (action : Event Source Value Fault Effect → World → World)
    (session : Session Source Value Fault Cause Effect Owner World) :
    Session Source Value Fault Cause Effect Owner World :=
  let settled := prune session
  match settled.query with
  | none => { settled with closed := true }
  | some owner =>
      let effects := settled.cleanup.map Event.cleanup
      { settled with
        query := none
        world := OwnedPullDriver.interpret action effects settled.world
        events := settled.events ++ effects
        released := settled.released ++ [.query owner]
        closed := true }

inductive Signal (Value Fault Cause : Type) where
  | yielded (cause : Cause)
  | finished (decision : Decision Value Fault Cause)
  deriving DecidableEq, Repr

/-- Terminal resume only reports retained control. In particular there is no
source expression or producer program here from which to restart evaluation. -/
def resume (session : Session Source Value Fault Cause Effect Owner World) :
    Signal Value Fault Cause × Session Source Value Fault Cause Effect Owner World :=
  (match session.decision with
    | .interrupted cause => .yielded cause
    | decision => .finished decision, session)

def resumeMany : Nat → Session Source Value Fault Cause Effect Owner World →
    List (Signal Value Fault Cause) × Session Source Value Fault Cause Effect Owner World
  | 0, session => ([], session)
  | count + 1, session =>
      let current := resume session
      let later := resumeMany count current.2
      (current.1 :: later.1, later.2)

def finish (action : Event Source Value Fault Effect → World → World)
    (guest : Guest Value Fault) (outcome : Outcome Value Fault Cause)
    (callback query : Owner) (cleanup : List Effect) (world : World)
    (earlier : List (Event Source Value Fault Effect)) :
    Session Source Value Fault Cause Effect Owner World :=
  let decision := targetDecision outcome
  let events := (guestTrace guest decision).map Event.guest
  let session : Session Source Value Fault Cause Effect Owner World :=
    ⟨decision, some callback, some query, cleanup,
      OwnedPullDriver.interpret action events world, earlier ++ events, [], false⟩
  if keepsCallback guest decision then session else prune session

private theorem closed_finish
    (action : Event Source Value Fault Effect → World → World)
    (guest : Guest Value Fault) (outcome : Outcome Value Fault Cause)
    (callback query : Owner) (cleanup : List Effect) (world : World)
    (earlier : List (Event Source Value Fault Effect)) :
    close action (finish action guest outcome callback query cleanup world earlier) =
      ⟨referenceDecision outcome, none, none, cleanup,
        OwnedPullDriver.interpret action
          ((guestTrace guest (referenceDecision outcome)).map Event.guest ++
            cleanup.map Event.cleanup) world,
        earlier ++ (guestTrace guest (referenceDecision outcome)).map Event.guest ++
          cleanup.map Event.cleanup,
        [.callback callback, .query query], true⟩ := by
  cases kept : keepsCallback guest (referenceDecision outcome) <;>
    simp [finish, decision_refines, kept, close, prune,
      OwnedPullDriver.interpret_append]

/-- The independent recursive account publishes only completed guest events;
its final ownership account contains exactly the two delimited leases. -/
def reference (action : Event Source Value Fault Effect → World → World)
    (guest : Guest Value Fault) (source : Source) (effects : List Effect)
    (outcome : Outcome Value Fault Cause) (callback query : Owner)
    (cleanup : List Effect) (world : World) :
    Session Source Value Fault Cause Effect Owner World :=
  let decision := referenceDecision outcome
  let events := [.entered source] ++ effects.map Event.producer ++
    (guestTrace guest decision).map Event.guest ++ cleanup.map Event.cleanup
  ⟨decision, none, none, cleanup, OwnedPullDriver.interpret action events world,
    events, [.callback callback, .query query], true⟩

/-- A driver budget merely advances the actual producer. It is not itself an
evaluator completion certificate; only a returned `Outcome` reaches `finish`. -/
def target (action : Event Source Value Fault Effect → World → World)
    (guest : Guest Value Fault) (source : Source)
    (work : OwnedPullDriver.Program (Outcome Value Fault Cause) Effect)
    (fuel : Nat) (callback query : Owner) (cleanup : List Effect) (world : World) :
    Option (Session Source Value Fault Cause Effect Owner World) :=
  let produced := OwnedPullDriver.Session.resume
    (fun effect => action (.producer effect)) fuel
    (OwnedPullDriver.Session.begin work (action (.entered source) world))
  match produced.residual with
  | some ⟨.done outcome, []⟩ =>
      some (finish action guest outcome callback query cleanup produced.world
        ([.entered source] ++ produced.committed.map Event.producer))
  | _ => none

private theorem interpret_map {Input Output State : Type}
    (action : Output → State → State) (map : Input → Output)
    (events : List Input) (world : State) :
    OwnedPullDriver.interpret action (events.map map) world =
      OwnedPullDriver.interpret (fun event => action (map event)) events world := by
  induction events generalizing world with
  | nil => rfl
  | cons event rest ih => simp only [List.map_cons, OwnedPullDriver.interpret_cons, ih]

/-- Actual explicit frames refine the recursive child derivation. The entire
world and occurrence trace agree after owner close, including non-idempotent
producer and cleanup effects. No event is deduplicated or reordered. -/
theorem owned_trace_refines
    (action : Event Source Value Fault Effect → World → World)
    (guest : Guest Value Fault) (source : Source)
    {work : OwnedPullDriver.Program (Outcome Value Fault Cause) Effect}
    {effects : List Effect} {outcome : Outcome Value Fault Cause}
    (run : OwnedPullDriver.Runs work effects outcome)
    (callback query : Owner) (cleanup : List Effect) (world : World) :
    ∃ fuel, (target action guest source work fuel callback query cleanup world).map
      (close action) =
        some (reference action guest source effects outcome callback query cleanup world) := by
  obtain ⟨fuel, reached⟩ := OwnedPullDriver.Session.refines_runs
    (fun effect => action (.producer effect)) (action (.entered source) world) run
  refine ⟨fuel, ?_⟩
  simp only [target, reached, Option.map_some, closed_finish]
  congr 1
  simp [reference, OwnedPullDriver.interpret_append, OwnedPullDriver.interpret_cons,
    interpret_map, List.append_assoc]

/-- Partial values, a simultaneous raised tag and arbitrary guest handlers do
not run a guest branch or publisher. The callback lease is gone before yield;
the committed producer world and trace remain intact. -/
theorem interruption_suppresses_guest
    (action : Event Source Value Fault Effect → World → World)
    (guest : Guest Value Fault) (values : Array Value) (cause : Cause)
    (raised : Option Fault) (callback query : Owner) (cleanup : List Effect)
    (world : World) (earlier : List (Event Source Value Fault Effect)) :
    finish action guest ⟨values, some cause, raised⟩ callback query cleanup world earlier =
      ⟨.interrupted cause, none, some query, cleanup, world, earlier,
        [.callback callback], false⟩ := by
  simp [finish, targetDecision, guestTrace, keepsCallback, prune]

/-- Every unexpected resume yields the original reason again. It repeats no
source entry, guest observation, producer effect, cleanup or resource release. -/
theorem repeated_resume_no_replay
    (session : Session Source Value Fault Cause Effect Owner World) (cause : Cause)
    (interrupted : session.decision = .interrupted cause) (count : Nat) :
    resumeMany count session = (List.replicate count (.yielded cause), session) := by
  induction count with
  | zero => rfl
  | succ count ih => simp [resumeMany, resume, interrupted, ih, List.replicate_succ]

/-- A callback prune releases its lease once. It commutes with the owner's
later close because that close also prunes any still-live callback lease. -/
theorem prune_then_owner_close
    (action : Event Source Value Fault Effect → World → World)
    (session : Session Source Value Fault Cause Effect Owner World) :
    prune (prune session) = prune session ∧
      close action (prune session) = close action session := by
  cases session with
  | mk decision callback query cleanup world events released closed =>
      cases callback <;> simp [prune, close]

/-- Closing an owned query a second time is inert even for non-idempotent
cleanup actions. Neither resource can be released for a second time. -/
theorem owner_close_idempotent
    (action : Event Source Value Fault Effect → World → World)
    (session : Session Source Value Fault Cause Effect Owner World) :
    close action (close action session) = close action session := by
  cases session with
  | mk decision callback query cleanup world events released closed =>
      cases callback <;> cases query <;> simp [close, prune]

/-- A live query executes precisely its cleanup trace after the current world,
then retires its lease. Existing effects survive and callback storage is
released separately, whether before close or by its prune. -/
theorem cleanup_effects_once
    (action : Event Source Value Fault Effect → World → World)
    (session : Session Source Value Fault Cause Effect Owner World) (owner : Owner)
    (live : session.query = some owner) :
    (close action session).world = OwnedPullDriver.interpret action
        (session.cleanup.map Event.cleanup) session.world ∧
      (close action session).events = session.events ++ session.cleanup.map Event.cleanup ∧
      (close action session).callback = none ∧ (close action session).query = none ∧
      (close action session).released = session.released ++
        session.callback.toList.map Resource.callback ++ [.query owner] ∧
      close action (close action session) = close action session := by
  cases session with
  | mk decision callback query cleanup world events released closed =>
      simp only at live
      subst query
      cases callback <;>
        simp [close, prune, List.append_assoc]

namespace Controls

inductive Payload where
  | number (value : Nat)
  | error (value : Nat)
  deriving DecidableEq, Repr

abbrev TestOutcome := Outcome Payload String String
abbrev TestEvent := Event Nat Payload String Nat
abbrev TestSession := Session Nat Payload String String Nat Nat (List Nat)

def dataError : TestOutcome := ⟨#[.error 7], none, none⟩
def raisedError : TestOutcome := ⟨#[.error 7], none, some "raised"⟩
def incompleteValues : TestOutcome := ⟨#[.number 1], some "fuel", some "raised"⟩
def emptyInterrupted : TestOutcome := ⟨#[], some "fuel", none⟩
def emptyComplete : TestOutcome := ⟨#[], none, none⟩

def action : TestEvent → List Nat → List Nat
  | .entered source, world => world ++ [source]
  | .producer effect, world => world ++ [effect]
  | .guest _, world => world ++ [777]
  | .cleanup effect, world => world ++ [effect + 1000]

theorem data_error_and_catchable_raise_separate :
    targetDecision dataError = .answers [.error 7] ∧
      guestTrace Guest.catchRaised (targetDecision dataError) = [.published [.error 7]] ∧
      targetDecision raisedError = .raised "raised" ∧
      guestTrace Guest.catchRaised (targetDecision raisedError) = [.caught "raised"] := by
  decide +kernel

/-- These controls reject both old Boolean projections: an empty interrupted
frontier is not failure, and a nonempty one is not a completed partial list. -/
theorem interruption_is_neither_failure_nor_partial_publication :
    guestTrace Guest.branch (targetDecision emptyComplete) = [.failureBranch] ∧
      guestTrace Guest.collect (targetDecision emptyComplete) = [.published []] ∧
      guestTrace Guest.branch (targetDecision emptyInterrupted) = [] ∧
      guestTrace Guest.collect (targetDecision incompleteValues) = [] ∧
      targetDecision emptyInterrupted ≠ .failure ∧
      targetDecision incompleteValues ≠ .answers [.number 1] := by
  decide +kernel

def interruptedWork : OwnedPullDriver.Program TestOutcome Nat :=
  .child (.emit 1 (.done incompleteValues)) fun _ => .emit 1 (.done incompleteValues)

/-- Two equal effects are two occurrences. Cleanup has a real additional
effect, while guest control, callback replay and rollback would change this
result. Source entry also occurs exactly once. -/
theorem interrupted_effects_and_cleanup_are_real :
    let produced := target action Guest.branch 9 interruptedWork 5 10 20 [3] []
    (produced.map (close action)).map Session.world = some [9, 1, 1, 1003] ∧
      (produced.map (close action)).map Session.released =
        some [.callback 10, .query 20] ∧
      (produced.map (close action)).map (fun session =>
        (close action session).world) = some [9, 1, 1, 1003] := by
  decide +kernel

theorem alternatives_pruned_but_collector_exhausts :
    let outcome : TestOutcome := ⟨#[.number 1, .number 1], none, none⟩
    let branch : TestSession := finish action Guest.branch outcome 10 20 [] [] []
    let collect : TestSession := finish action Guest.collect outcome 10 20 [] [] []
    branch.callback = some 10 ∧ collect.callback = none ∧
      branch.released = [] ∧ collect.released = [.callback 10] ∧
      (close action branch).released = [.callback 10, .query 20] ∧
      (close action collect).released = [.callback 10, .query 20] := by
  decide +kernel

theorem interrupted_handler_is_not_entered_and_resume_is_terminal :
    let session : TestSession := finish action Guest.catchRaised incompleteValues 10 20 [3] [9, 1] []
    session.world = [9, 1] ∧ session.events = [] ∧
      resumeMany 3 session = ([.yielded "fuel", .yielded "fuel", .yielded "fuel"], session) ∧
      (close action session).world = [9, 1, 1003] ∧
      (close action session).decision = .interrupted "fuel" := by
  decide +kernel

end Controls
end Mettapedia.Machines.ForeignCallbackInterruption

#print axioms Mettapedia.Machines.ForeignCallbackInterruption.decision_refines
#print axioms Mettapedia.Machines.ForeignCallbackInterruption.owned_trace_refines
#print axioms Mettapedia.Machines.ForeignCallbackInterruption.interruption_suppresses_guest
#print axioms Mettapedia.Machines.ForeignCallbackInterruption.repeated_resume_no_replay
#print axioms Mettapedia.Machines.ForeignCallbackInterruption.prune_then_owner_close
#print axioms Mettapedia.Machines.ForeignCallbackInterruption.owner_close_idempotent
#print axioms Mettapedia.Machines.ForeignCallbackInterruption.cleanup_effects_once
#print axioms Mettapedia.Machines.ForeignCallbackInterruption.Controls.data_error_and_catchable_raise_separate
#print axioms Mettapedia.Machines.ForeignCallbackInterruption.Controls.interruption_is_neither_failure_nor_partial_publication
#print axioms Mettapedia.Machines.ForeignCallbackInterruption.Controls.interrupted_effects_and_cleanup_are_real
#print axioms Mettapedia.Machines.ForeignCallbackInterruption.Controls.alternatives_pruned_but_collector_exhausts
#print axioms Mettapedia.Machines.ForeignCallbackInterruption.Controls.interrupted_handler_is_not_entered_and_resume_is_terminal

import Mettapedia.Machines.SourceProducerCardinality.Core

/-!
# Shared and weighted body/call execution

Shared and weighted body/call execution: loans, coefficients, histories, handoff, the
authored weighted call and authored publication.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceProducerCardinality

open AnswerCardinality RecursiveFiniteProducer SourceProducerAdmission
universe u v
variable {Item : Type u} {Value : Type v}

namespace BodyCallShared

/-- The common cold transfer preserves a Call, seeds its already issued loan
and starts only new reader positions. It performs no provider operation. -/
def retainedAdopt {Loan Saved Stored Context Owner : Type} {clients : Nat}
    (context : Context) (limit : Nat)
    (call : Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved)) :
    Cursor.ProducerOccurrenceLog.Configuration
      (Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved))
      (Nat × Loan) Stored Context Owner Empty Loan clients :=
  ⟨some ⟨call, call.2.1.pending.map (fun loan => (call.2.1.accepted, loan)), 0, .active⟩,
    context, ⟨Cursor.SharedOccurrenceLog.initial limit, ∅⟩⟩

/-- Handback uses the same pending/captured distinction for every retained
loan representation. The supplied action is the existing acknowledgment. -/
def retainedRelease {Loan Saved Stored Context Owner : Type} {clients : Nat}
    (acknowledge : Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved) →
      Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved))
    (state : Cursor.ProducerOccurrenceLog.Configuration
      (Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved))
      (Nat × Loan) Stored Context Owner Empty Loan clients) :=
  (state.execution.map (fun execution =>
    if execution.pending.isNone && execution.producer.2.1.pending.isSome then
      acknowledge execution.producer else execution.producer),
    (Cursor.ProducerOccurrenceLog.detach state).2)


/-- Common retained-call choice. The existing occurrence-log engine owns
capture/admission/delivery; this only selects terminal, acknowledgment or poll. -/
def retainedStep {Loan Saved : Type}
    (inspect : Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved) →
      Cursor.ProducerOccurrenceLog.ProducerOutcome
        (Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved)) (Nat × Loan) Empty Loan)
    (acknowledge poll : Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved) →
      Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved))
    (call : Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved)) :=
  if call.2.1.terminal.isSome then inspect call
  else match call.2.1.pending with
    | some _ => .progress (acknowledge call)
    | none => inspect (poll call)

open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory

variable {Input Output Context : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)

abbrev Call := BodyCallAdmission.Call construct callbackConstruct fallback (Context := Context)
abbrev Loan := BodyCallOwned.Returned construct callbackConstruct fallback
abbrev Borrowed := Nat × Loan construct callbackConstruct fallback
abbrev Stored := Nat × List (List Output)
abbrev Move := Cursor.ProducerOccurrenceLog.ProducerOutcome
  (Call construct callbackConstruct fallback (Context := Context))
  (Borrowed construct callbackConstruct fallback) Empty (Loan construct callbackConstruct fallback)

def refuse (context : Context) (_ : Loan construct callbackConstruct fallback) : Bool × Context :=
  (false, context)

def accept (context : Context) (_ : Loan construct callbackConstruct fallback) : Bool × Context :=
  (true, context)

abbrev charge (quantum : Nat)
    (consumer : Context → Loan construct callbackConstruct fallback → Bool × Context) :
    Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer) :=
  fun _ _ => 1

/-- Read the actual owned callback boundary. A held reply is indexed by its
existing successful-return position; it is not producer exhaustion. -/
def inspect (call : Call construct callbackConstruct fallback (Context := Context)) :
    Move construct callbackConstruct fallback (Context := Context) :=
  if BodyCallAdmission.complete construct callbackConstruct fallback call then .completed call
  else match call.2.1.terminal with
    | some returned => match returned.2.1 with
      | .decline _ => .interrupted call
      | .handoff _ => .handoff returned call
      | _ => .yielded call
    | none => match call.2.1.pending with
      | some returned => .returned (call.2.1.accepted, returned) call
      | none => .yielded call

theorem inspect_next (call : Call construct callbackConstruct fallback (Context := Context)) :
    (inspect construct callbackConstruct fallback call).next = call := by
  unfold inspect
  split
  · rfl
  · cases call.2.1.terminal with
    | some returned => cases mode : returned.2.1 <;> simp [mode, Cursor.ProducerOccurrenceLog.ProducerOutcome.next]
    | none => cases call.2.1.pending <;> rfl

/-- A public loan is the actual retained source reply, before acknowledgment. -/
def Coherent (call : Call construct callbackConstruct fallback (Context := Context)) : Prop :=
  ∀ loan, call.2.1.pending = some loan →
    call.2.1.terminal = none ∧ call.2.2.computation.2 = .done loan ∧
      BodyCallOwned.isReturn construct callbackConstruct fallback loan = true

open Cursor.Fold.OwnedSequence.CallbackBoundary

private theorem retainedCallbacks_coherent
    {Input Output Context : Type}
    (source : Cursor.Provider (BodyCallProtocol.protocol (Item := Input) (Value := Output)))
    (sourceCharge : Cursor.Charge source) (quantum : Nat)
    (isReturn : Cursor.Finished source (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit) → Bool)
    (rearm : Cursor.Finished source (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit) →
      Cursor.Packet source BodyCallProtocol.client (⟨()⟩ : ULift Unit))
    (consume : Context → Cursor.Finished source (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit) → Bool × Context)
    (terminalAfter : Cursor.Finished source (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit) →
      Option (Cursor.Finished source (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit)))
    (charges : Cursor.Charge (Cursor.Fold.OwnedSequence.CallbackBoundary.Retained.provider source BodyCallProtocol.client
      ⟨()⟩ sourceCharge quantum isReturn rearm consume))
    (allowance accepted : Nat)
    (held : Option (Cursor.Finished source (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit)))
    (state : Cursor.Fold.OwnedSequence.CallbackBoundary.Retained.State source BodyCallProtocol.client ⟨()⟩ Context)
    (aligned : ∀ loan, held = some loan → state.computation.2 = .done loan ∧ isReturn loan = true) :
    let actual := Cursor.Fold.OwnedSequence.CallbackBoundary.fromCallbacks
      (Cursor.Fold.OwnedSequence.CallbackBoundary.Retained.provider source BodyCallProtocol.client
        ⟨()⟩ sourceCharge quantum isReturn rearm consume)
      charges allowance held accepted state terminalAfter
    ∀ loan, actual.2.1.pending = some loan → actual.2.1.terminal = none ∧
      actual.2.2.computation.2 = .done loan ∧ isReturn loan = true := by
  dsimp only
  induction allowance generalizing accepted held state with
  | zero =>
      intro loan pending
      exact ⟨rfl, aligned loan pending⟩
  | succ allowance ih =>
      cases held with
      | some loan =>
          obtain ⟨ready, produced⟩ := aligned loan rfl
          cases decision : (consume state.context loan).1 with
          | false =>
              simp [fromCallbacks, Retained.provider, ready, produced,
                decision]
          | true =>
              cases final : terminalAfter loan with
              | some reason =>
                  simp [fromCallbacks, Retained.provider, ready, produced,
                    decision, final]
              | none =>
                  simpa [fromCallbacks, Retained.provider, ready, produced,
                    decision, final] using
                    ih (accepted + 1) none _ (by intro next impossible; cases impossible)
      | none =>
          cases outcome : (Cursor.resume (source)
              BodyCallProtocol.client (sourceCharge)
              quantum state.computation).2 with
          | paused saved =>
              simp [fromCallbacks, Retained.provider, outcome]
          | done returned =>
              cases produced : isReturn returned with
              | false =>
                  simp [fromCallbacks, Retained.provider, outcome, produced]
              | true =>
                  cases decision : (consume state.context returned).1 with
                  | false =>
                      simp [fromCallbacks, Retained.provider, outcome, produced,
                        decision]
                  | true =>
                      cases final : terminalAfter returned with
                      | some reason =>
                          simp [fromCallbacks, Retained.provider, outcome, produced,
                            decision, final]
                      | none =>
                          simpa [fromCallbacks, Retained.provider, outcome, produced,
                            decision, final] using
                            ih (accepted + 1) none _ (by intro next impossible; cases impossible)

/-- Ordered rows already exposed at the source-to-log boundary. A held loan
is counted once, even before its later zero-source acknowledgment. -/
def publishedRows (call : Call construct callbackConstruct fallback (Context := Context)) : List (List Output) :=
  call.2.2.context.1 ++ call.2.1.pending.toList.flatMap (fun loan => loan.2.1.rows)

def residualRows (call : Call construct callbackConstruct fallback (Context := Context)) : List (List Output) :=
  match call.2.1.pending with
  | some _ => BodyCall.workRows construct callbackConstruct (BodyCallProtocol.stateView
      construct callbackConstruct fallback call.2.2.computation.2).work
  | none => BodyCallProtocol.unacceptedRows construct callbackConstruct fallback call.2.2.computation.2

theorem open_coherent (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (context : Context) :
    Coherent construct callbackConstruct fallback
      (BodyCallAdmission.openCall construct callbackConstruct fallback authored items parameter context) := by
  intro loan pending
  cases pending

theorem published_residual_eq_view (call : Call construct callbackConstruct fallback (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback call) :
    publishedRows construct callbackConstruct fallback call ++ residualRows construct callbackConstruct fallback call =
      BodyCallOwned.view construct callbackConstruct fallback call.2.2 := by
  cases pending : call.2.1.pending with
  | none => simp [publishedRows, residualRows, pending, BodyCallOwned.view]
  | some loan =>
      have held := coherent loan pending
      simp [publishedRows, residualRows, pending, BodyCallOwned.view, held.2.1,
        BodyCallProtocol.unacceptedRows, BodyCallProtocol.moveView, List.append_assoc]

theorem poll_shape (quantum : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (running : call.2.1.terminal = none) (empty : call.2.1.pending = none) :
    let later := BodyCallAdmission.resume construct callbackConstruct fallback quantum 1
      (refuse construct callbackConstruct fallback) (charge construct callbackConstruct fallback _ _) call
    later.2.2.context = call.2.2.context ∧ later.2.1.accepted = call.2.1.accepted ∧
      Coherent construct callbackConstruct fallback later := by
  cases outcome : (Cursor.resume (BodyCallProtocol.provider construct callbackConstruct fallback)
      BodyCallProtocol.client (BodyCallProtocol.requestCharge construct callbackConstruct fallback)
      quantum call.2.2.computation).2 with
  | paused packet =>
      simp [BodyCallAdmission.resume, resumeCall, running, empty, fromCallbacks,
        BodyCallOwned.provider, Retained.provider, outcome, Coherent]
  | done returned =>
      cases produced : BodyCallOwned.isReturn construct callbackConstruct fallback returned <;>
        simp [BodyCallAdmission.resume, resumeCall, running, empty, fromCallbacks,
          BodyCallOwned.provider, Retained.provider, outcome, produced, BodyCallOwned.consume,
          refuse, Coherent]

theorem acknowledge_shape (call : Call construct callbackConstruct fallback (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback call)
    (loan : Loan construct callbackConstruct fallback) (pending : call.2.1.pending = some loan) :
    let later := BodyCallAdmission.resume construct callbackConstruct fallback 0 1
      (accept construct callbackConstruct fallback) (charge construct callbackConstruct fallback _ _) call
    later.2.1.pending = none ∧ later.2.2.context.1 = call.2.2.context.1 ++ loan.2.1.rows ∧
      later.2.1.accepted = call.2.1.accepted + 1 ∧ Coherent construct callbackConstruct fallback later := by
  have held := coherent loan pending
  cases final : BodyCallOwned.terminalAfter construct callbackConstruct fallback loan <;>
    simp [BodyCallAdmission.resume, resumeCall, held.1, pending, fromCallbacks,
      BodyCallOwned.provider, Retained.provider, held.2.1, held.2.2, BodyCallOwned.consume,
      accept, final, Coherent]

theorem inspect_returns (call : Call construct callbackConstruct fallback (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback call) :
    (inspect construct callbackConstruct fallback call).returns =
      call.2.1.pending.toList.map (fun loan => (call.2.1.accepted, loan)) := by
  cases pending : call.2.1.pending with
  | some loan =>
      have held := coherent loan pending
      simp [inspect, BodyCallAdmission.complete, pending, held.1,
        Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]
  | none =>
      unfold inspect
      split
      · rfl
      · cases terminal : call.2.1.terminal with
        | none => simp [pending, Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]
        | some returned =>
            cases mode : returned.2.1 <;>
              simp [mode, Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]

variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    {size : Nat} (before current : OrderedDependencyStore.Store (Equation Output) size)
    (reader : Fin size) (point : IndexedAuthority.Point authority)
    (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]

/-- One real owned-source action. A captured loan is acknowledged without
another source inspection. Only new production enters the current authority
gate. The enclosing shared-log pump blocks this action while capture waits. -/
def step (quantum : Nat) (call : Call construct callbackConstruct fallback (Context := Context)) :
    Move construct callbackConstruct fallback (Context := Context) :=
  retainedStep (inspect construct callbackConstruct fallback)
    (fun saved => BodyCallAdmission.resume construct callbackConstruct fallback 0 1
      (accept construct callbackConstruct fallback) (charge construct callbackConstruct fallback _ _) saved)
    (fun saved => (BodyCallAdmission.CurrentAuthority.resume construct callbackConstruct fallback authority before current reader
      point required quantum 1 (refuse construct callbackConstruct fallback)
      (charge construct callbackConstruct fallback _ _) saved).2) call

def capture (borrowed : Borrowed construct callbackConstruct fallback) : Option (Stored (Output := Output)) :=
  some (borrowed.1, borrowed.2.2.1.rows)

abbrev Configuration (Owner : Type) (clients : Nat) := Cursor.ProducerOccurrenceLog.Configuration
  (Call construct callbackConstruct fallback (Context := Context))
  (Borrowed construct callbackConstruct fallback) (Stored (Output := Output))
  (OrderedDependencyStore.Store (Equation Output) size) Owner Empty
  (Loan construct callbackConstruct fallback) clients

/-- Buffered pure data belongs to its retained capture. New source work has
the separate current-world/authority gate in `step`. -/
def initial (authoredItems : List Input) (parameter : Nat) (context : Context)
    (Owner : Type) (clients limit : Nat) :
    Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients :=
  Cursor.ProducerOccurrenceLog.initial
    (BodyCallAdmission.openCall construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) authoredItems parameter context) before limit

theorem step_preserves_captured (quantum : Nat) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter call) :
    BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter
      (step construct callbackConstruct fallback authority before current reader point required quantum call).next := by
  unfold step retainedStep
  split
  · simpa only [inspect_next] using safe
  · cases call.2.1.pending with
    | some loan =>
        exact BodyCallAdmission.resume_captured construct callbackConstruct fallback 0 1
          (accept construct callbackConstruct fallback) (charge construct callbackConstruct fallback _ _)
          _ items parameter call safe
    | none =>
        rw [inspect_next]
        exact BodyCallAdmission.CurrentAuthority.preserves_captured construct callbackConstruct fallback authority
          before current reader point required quantum 1 (refuse construct callbackConstruct fallback)
          (charge construct callbackConstruct fallback _ _) items parameter call safe

theorem step_preserves_coherent (quantum : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback call) :
    Coherent construct callbackConstruct fallback
      (step construct callbackConstruct fallback authority before current reader point required quantum call).next := by
  unfold step retainedStep
  split
  · simpa only [inspect_next] using coherent
  · cases pending : call.2.1.pending with
    | some loan => exact (acknowledge_shape construct callbackConstruct fallback call coherent loan pending).2.2.2
    | none =>
        rw [inspect_next]
        unfold BodyCallAdmission.CurrentAuthority.resume
        split
        · split
          · exact (poll_shape construct callbackConstruct fallback quantum call
              (by simpa using ‹¬call.2.1.terminal.isSome = true›) pending).2.2
          · exact coherent
        · exact coherent

/-- The source boundary exposes each actual reply once. A later successful
capture is acknowledged without republishing the reply or requesting source. -/
theorem step_rows (quantum : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback call) :
    publishedRows construct callbackConstruct fallback
        (step construct callbackConstruct fallback authority before current reader point required quantum call).next =
      publishedRows construct callbackConstruct fallback call ++
        (step construct callbackConstruct fallback authority before current reader point required quantum call).returns.flatMap
          (fun borrowed => borrowed.2.2.1.rows) := by
  unfold step retainedStep
  split
  · rw [inspect_next, inspect_returns construct callbackConstruct fallback call coherent]
    have empty : call.2.1.pending = none := by
      cases pending : call.2.1.pending with
      | none => rfl
      | some loan =>
          have held := coherent loan pending
          simp [held.1] at ‹call.2.1.terminal.isSome = true›
    simp [empty]
  · cases pending : call.2.1.pending with
    | some loan =>
        have shape := acknowledge_shape construct callbackConstruct fallback call coherent loan pending
        simp [Cursor.ProducerOccurrenceLog.ProducerOutcome.next,
          Cursor.ProducerOccurrenceLog.ProducerOutcome.returns, publishedRows, shape.1, shape.2.1, pending]
    | none =>
        by_cases fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true
        · by_cases permitted : FrameUpdate point.authority required
          · simp only [BodyCallAdmission.CurrentAuthority.resume, fresh, permitted, ↓reduceIte]
            have shape := poll_shape construct callbackConstruct fallback quantum call
              (by simpa using ‹¬call.2.1.terminal.isSome = true›) pending
            rw [inspect_next, inspect_returns construct callbackConstruct fallback _ shape.2.2]
            simp [publishedRows, shape.1, shape.2.1, pending, List.flatMap_map]
          · simp only [BodyCallAdmission.CurrentAuthority.resume, fresh, permitted, ↓reduceIte]
            rw [inspect_next, inspect_returns construct callbackConstruct fallback call coherent]
            simp [pending]
        · simp only [BodyCallAdmission.CurrentAuthority.resume, fresh, Bool.false_eq_true, ↓reduceIte]
          rw [inspect_next, inspect_returns construct callbackConstruct fallback call coherent]
          simp [pending]

/-- A path of the actual saved source computation has its exact ordered row
prefix, not an assumed equality between accepted rows and future answers. -/
theorem path_rows (quantum : Nat)
    {first last : Call construct callbackConstruct fallback (Context := Context)}
    {returns : List (Borrowed construct callbackConstruct fallback)}
    (path : Cursor.ProducerOccurrenceLog.ProducerPath
      (step construct callbackConstruct fallback authority before current reader point required quantum) first returns last)
    (coherent : Coherent construct callbackConstruct fallback first) :
    Coherent construct callbackConstruct fallback last ∧
      publishedRows construct callbackConstruct fallback last =
        publishedRows construct callbackConstruct fallback first ++ returns.flatMap (fun loan => loan.2.2.1.rows) := by
  induction path with
  | refl => exact ⟨coherent, by simp⟩
  | @next first move later returns transition tail ih =>
      have kept := step_preserves_coherent construct callbackConstruct fallback authority before current reader
        point required quantum first coherent
      have row := step_rows construct callbackConstruct fallback authority before current reader point required
        quantum first coherent
      rw [transition] at kept row
      have rest := ih kept
      refine ⟨rest.1, ?_⟩
      rw [rest.2, row, List.flatMap_append, List.append_assoc]

theorem path_preserves_captured (quantum : Nat) (items : List Input) (parameter : Nat)
    {first last : Call construct callbackConstruct fallback (Context := Context)}
    {returns : List (Borrowed construct callbackConstruct fallback)}
    (path : Cursor.ProducerOccurrenceLog.ProducerPath
      (step construct callbackConstruct fallback authority before current reader point required quantum) first returns last)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter first) :
    BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter last := by
  induction path with
  | refl => exact safe
  | next transition tail ih =>
      apply ih
      have kept := step_preserves_captured construct callbackConstruct fallback authority before current reader
        point required quantum items parameter _ safe
      simpa only [transition] using kept

theorem run_keeps_actual_source {Owner : Type} {clients : Nat}
    (quantum ticks : Nat) (capacity : Stored (Output := Output) → Bool)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (execution : Cursor.ProducerOccurrenceLog.Execution
      (Call construct callbackConstruct fallback (Context := Context))
      (Borrowed construct callbackConstruct fallback) Empty (Loan construct callbackConstruct fallback))
    (attached : state.execution = some execution) (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer) :
    ∃ next, (Cursor.ProducerOccurrenceLog.run
        (step construct callbackConstruct fallback authority before current reader point required quantum)
        (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks state).2.execution = some next ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter next.producer := by
  obtain ⟨next, retained, actual⟩ := Cursor.ProducerOccurrenceLog.run_producer_path
    (step construct callbackConstruct fallback authority before current reader point required quantum)
    (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks state execution attached
  exact ⟨next, retained, path_preserves_captured construct callbackConstruct fallback authority before current reader
    point required quantum items parameter actual safe⟩

/-- Every finite shared-source run exposes an ordered authored-source prefix
and keeps the actual unevaluated residual and the complete captured Call. -/
theorem run_open_source {Owner : Type} {clients : Nat}
    (quantum ticks limit : Nat) (capacity : Stored (Output := Output) → Bool)
    (items : List Input) (parameter : Nat) (context : Context) :
    let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
    let actual := Cursor.ProducerOccurrenceLog.run
      (step construct callbackConstruct fallback authority before current reader point required quantum)
      (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks start
    ∃ next, actual.2.execution = some next ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter next.producer ∧
      (actual.1.flatMap Cursor.ProducerOccurrenceLog.returned).flatMap (fun loan => loan.2.2.1.rows) ++
        residualRows construct callbackConstruct fallback next.producer =
          source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  dsimp only
  let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
  obtain ⟨next, retained, path⟩ := Cursor.ProducerOccurrenceLog.run_producer_path
    (step construct callbackConstruct fallback authority before current reader point required quantum)
    (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks start _ rfl
  have coherent := open_coherent construct callbackConstruct fallback
    (OrderedDependencyStore.query before reader) items parameter context
  have rows := path_rows construct callbackConstruct fallback authority before current reader point required
    quantum path coherent
  have safe := path_preserves_captured construct callbackConstruct fallback authority before current reader
    point required quantum items parameter path
    (BodyCallAdmission.open_captured construct callbackConstruct fallback _ items parameter context)
  refine ⟨next, retained, safe, ?_⟩
  have view := published_residual_eq_view construct callbackConstruct fallback next.producer rows.1
  rw [rows.2] at view
  simpa [start, initial, Cursor.ProducerOccurrenceLog.initial, publishedRows, BodyCallAdmission.openCall,
    BodyCallOwned.openState, safe.2.2] using view.trans safe.2.2

/-- Actual captured log contents, the borrowed return awaiting admission,
and the actual source residual partition the independent authored answers.
The equation uses the existing append/conservation laws for this concrete
capture; it does not assume an accepted-equals-source oracle. -/
theorem run_open_log_source {Owner : Type} {clients : Nat}
    (quantum ticks limit : Nat) (capacity : Stored (Output := Output) → Bool)
    (items : List Input) (parameter : Nat) (context : Context) :
    let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
    let actual := Cursor.ProducerOccurrenceLog.run
      (step construct callbackConstruct fallback authority before current reader point required quantum)
      (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks start
    ∃ next, actual.2.execution = some next ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter next.producer ∧
      actual.2.delivery.log.rows.flatMap (·.2) ++
        (Cursor.ProducerOccurrenceLog.pending actual.2).toList.flatMap (fun loan => loan.2.2.1.rows) ++
        residualRows construct callbackConstruct fallback next.producer =
          source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  dsimp only
  let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
  let actual := Cursor.ProducerOccurrenceLog.run
    (step construct callbackConstruct fallback authority before current reader point required quantum)
    (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks start
  obtain ⟨next, retained, safe, sourceEq⟩ := run_open_source construct callbackConstruct fallback authority
    before current reader point required quantum ticks limit capacity items parameter context (Owner := Owner) (clients := clients)
  have conservation := Cursor.ProducerOccurrenceLog.run_conservation
    (fun (loan : Borrowed construct callbackConstruct fallback) => loan.2.2.1.rows)
    (fun (stored : Stored (Output := Output)) => stored.2)
    (step construct callbackConstruct fallback authority before current reader point required quantum)
    (capture construct callbackConstruct fallback) capacity (fun _ => true)
    (by intro loan stored captured; cases captured; rfl) ticks start
  have flat := congrArg (List.flatMap id) conservation
  simp only [List.flatMap_append, List.flatMap_map] at flat
  have stored := Cursor.ProducerOccurrenceLog.run_rows
    (step construct callbackConstruct fallback authority before current reader point required quantum)
    (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks start
  have empty : start.delivery.log.rows = [] := rfl
  have noLoan : Cursor.ProducerOccurrenceLog.pending start = none := rfl
  rw [empty, List.nil_append] at stored
  simp only [noLoan, Option.toList_none, List.flatMap_nil, List.nil_append] at flat
  rw [← stored] at flat
  refine ⟨next, retained, safe, ?_⟩
  exact (congrArg (· ++ residualRows construct callbackConstruct fallback next.producer) flat.symm).trans sourceEq

/-- Arbitrary interleaved producer requests and consumer acknowledgments
retain the real Call, its independent captured-source view, and loan coherence. -/
theorem actions_keep_actual_source {Owner : Type} {clients : Nat}
    [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : Stored (Output := Output) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (execution : Cursor.ProducerOccurrenceLog.Execution
      (Call construct callbackConstruct fallback (Context := Context))
      (Borrowed construct callbackConstruct fallback) Empty (Loan construct callbackConstruct fallback))
    (attached : state.execution = some execution) (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer)
    (coherent : Coherent construct callbackConstruct fallback execution.producer) :
    ∃ next, (Cursor.ProducerOccurrenceLog.Accounting.runActions
        (step construct callbackConstruct fallback authority before current reader point required quantum)
        (capture construct callbackConstruct fallback) capacity (fun _ => true) actions state).execution = some next ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter next.producer ∧
      Coherent construct callbackConstruct fallback next.producer := by
  induction actions generalizing state execution with
  | nil => exact ⟨execution, attached, safe, coherent⟩
  | cons action rest ih =>
      cases action with
      | pump =>
          obtain ⟨next, retained, path⟩ := Cursor.ProducerOccurrenceLog.pump_producer_path
            (step construct callbackConstruct fallback authority before current reader point required quantum)
            (capture construct callbackConstruct fallback) capacity (fun _ => true) state execution attached
          exact ih _ next retained
            (path_preserves_captured construct callbackConstruct fallback authority before current reader point required
              quantum items parameter path safe)
            (path_rows construct callbackConstruct fallback authority before current reader point required
              quantum path coherent).1
      | deliver client owner =>
          apply ih _ execution _ safe coherent
          simpa [Cursor.ProducerOccurrenceLog.deliver] using attached

/-- Cancelling one consumer commutes with any interleaved schedule that does
not deliver to that cancelled consumer. The whole actual source Call and its
captured world, the paid production/delivery account, and the other consumer's
ordered unread values agree. -/
theorem independent_retirement {Owner : Type} {clients : Nat}
    [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : Stored (Output := Output) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (account : Cursor.ProducerOccurrenceLog.Accounting.ProtocolAccount)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (retired other : Fin clients) (position : Nat) (distinct : other ≠ retired)
    (live : state.delivery.log.positions other = some position)
    (spares : Cursor.ProducerOccurrenceLog.Accounting.sparesRetired retired actions) :
    let original := Cursor.ProducerOccurrenceLog.Accounting.count
      (step construct callbackConstruct fallback authority before current reader point required quantum)
      (capture construct callbackConstruct fallback) capacity (fun _ => true) actions account state
    let cancelled := Cursor.ProducerOccurrenceLog.Accounting.count
      (step construct callbackConstruct fallback authority before current reader point required quantum)
      (capture construct callbackConstruct fallback) capacity (fun _ => true) actions account
      (Cursor.ProducerOccurrenceLog.retireConsumer state retired)
    cancelled.1.execution = original.1.execution ∧ cancelled.1.context = original.1.context ∧
      cancelled.2 = original.2 ∧
      Cursor.SharedOccurrenceLog.peek cancelled.1.delivery.log other =
        Cursor.SharedOccurrenceLog.peek original.1.delivery.log other ∧
      Cursor.SharedOccurrenceLog.unread cancelled.1.delivery.log other =
        Cursor.SharedOccurrenceLog.unread original.1.delivery.log other := by
  dsimp only
  rw [Cursor.ProducerOccurrenceLog.Accounting.count_after_retained_demand
    (step construct callbackConstruct fallback authority before current reader point required quantum)
    (capture construct callbackConstruct fallback) capacity (fun _ => true) actions account state
    retired other position distinct live spares]
  exact ⟨rfl, rfl, rfl,
    (Cursor.ProducerOccurrenceLog.retireConsumer_releases_only_its_retention _ retired).2.2 other distinct⟩

/-- The heap law applies to the other consumer's actual unread payload graph.
Native discovery of that graph and agreement with compiled layout are supplied
services; this statement does not replace them with source syntax. -/
theorem retirement_keeps_payload_graph {Owner Cell : Type} {clients : Nat}
    [DecidableEq Output] [DecidableEq Owner]
    (heap : ResourceOwnership.Heap (Stored (Output := Output)) Cell)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (retired other : Fin clients) (valid : Cursor.SharedOccurrenceLog.Valid state.delivery.log)
    (distinct : other ≠ retired) (location : Stored (Output := Output))
    (live : ResourceOwnership.Live heap
      (Cursor.OwnedLifecycle.answerRoots (Sum.inl other : Sum (Fin clients) Owner)
        (Cursor.SharedOccurrenceLog.unread state.delivery.log other)) location) :
    (ResourceOwnership.collect heap
      (Cursor.SharedOccurrenceOwnership.roots
        (Cursor.SharedOccurrenceOwnership.trimLog
          (Cursor.SharedOccurrenceOwnership.cancelConsumer state.delivery retired)))).lookup location =
      heap.lookup location :=
  Cursor.ProducerOccurrenceLog.retireConsumer_retains_other_ready_graph heap state retired other valid distinct location live

namespace Coefficients

open Mettapedia.Algebra.SharedCoefficientLedger

/-- An admission-position observer with a supplied per-return coefficient.
It is distinct from source firing factors in `BodyCallShared.Weighted`.
No execution, delivery journal or alternate account is stored. -/
def ledger {Owner V : Type} {clients : Nat} (coefficient : Stored (Output := Output) → V)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients) :
    Ledger Nat (OrderedDependencyStore.ReadStamp size) V :=
  (state.delivery.log.rows.zipIdx state.delivery.log.base).map fun occurrence =>
    ⟨occurrence.2, OrderedDependencyStore.readStamp state.context reader, coefficient occurrence.1⟩

theorem ledger_valid {Owner V : Type} {clients : Nat} (coefficient : Stored (Output := Output) → V)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients) :
    Valid (ledger construct callbackConstruct fallback reader coefficient state) := by
  simp only [ledger, Valid, identities, List.map_map, Function.comp_def]
  rw [List.zipIdx_map_snd]
  exact List.nodup_range'

theorem retirement_keeps_factors {Owner V : Type} {clients : Nat}
    (coefficient : Stored (Output := Output) → V)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (retired : Fin clients) :
    ledger construct callbackConstruct fallback reader coefficient (Cursor.ProducerOccurrenceLog.retireConsumer state retired) =
      ledger construct callbackConstruct fallback reader coefficient state := rfl

theorem delivery_keeps_factors {Owner V : Type} {clients : Nat}
    [DecidableEq Output] [DecidableEq Owner] (coefficient : Stored (Output := Output) → V)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (client : Fin clients) (owner : Owner) :
    ledger construct callbackConstruct fallback reader coefficient
      (Cursor.ProducerOccurrenceLog.deliver (fun _ => true) state client owner).2 =
      ledger construct callbackConstruct fallback reader coefficient state := by
  cases reply : Cursor.SharedOccurrenceLog.peek state.delivery.log client <;>
    simp [ledger, Cursor.ProducerOccurrenceLog.deliver, Cursor.SharedOccurrenceOwnership.advance,
      Cursor.SharedOccurrenceOwnership.prepare, Cursor.SharedOccurrenceOwnership.acknowledge,
      Cursor.SharedOccurrenceLog.pull, reply, Cursor.SharedOccurrenceLog.setPosition]

/-- Two consumer views merge the one paid production ledger once. Successful
delivery is a separate use and never appends another copy of its factors. -/
theorem shared_factors_once {Owner V : Type} {clients : Nat} [DecidableEq V]
    (coefficient : Stored (Output := Output) → V)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients) :
    merge? (ledger construct callbackConstruct fallback reader coefficient state)
      (ledger construct callbackConstruct fallback reader coefficient state) =
        some (ledger construct callbackConstruct fallback reader coefficient state) :=
  merge_self _ (ledger_valid construct callbackConstruct fallback reader coefficient state)

/-- A repeated delivery does not create another physical production identity,
even if the coefficient and payload of another return happen to be equal. -/
theorem existing_factor_cannot_be_reappended {Owner V : Type} {clients : Nat}
    (coefficient : Stored (Output := Output) → V)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (factor : Factor Nat (OrderedDependencyStore.ReadStamp size) V)
    (present : factor ∈ ledger construct callbackConstruct fallback reader coefficient state) :
    append? (ledger construct callbackConstruct fallback reader coefficient state) factor = none := by
  have member : factor.identity ∈ identities (ledger construct callbackConstruct fallback reader coefficient state) :=
    List.mem_map.mpr ⟨factor, present, rfl⟩
  simp [append?, member]

end Coefficients


#print axioms inspect_next
#print axioms step_preserves_captured
#print axioms actions_keep_actual_source
#print axioms independent_retirement
#print axioms retirement_keeps_payload_graph
#print axioms Coefficients.ledger_valid
#print axioms Coefficients.retirement_keeps_factors
#print axioms Coefficients.delivery_keeps_factors
#print axioms Coefficients.shared_factors_once
#print axioms Coefficients.existing_factor_cannot_be_reappended
#print axioms open_coherent
#print axioms published_residual_eq_view
#print axioms poll_shape
#print axioms acknowledge_shape
#print axioms inspect_returns
#print axioms step_preserves_coherent
#print axioms step_rows
#print axioms path_rows
#print axioms run_open_source
#print axioms run_open_log_source
#print axioms path_preserves_captured
#print axioms run_keeps_actual_source

namespace History

open Cursor.ProducerOccurrenceLog
open Cursor.ProducerOccurrenceLog.Accounting
open Mettapedia.GSLT.Core.InferenceControl.Recording

variable {Owner : Type} {clients : Nat} [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : Stored (Output := Output) → Bool)

local notation "sourceStep" => step construct callbackConstruct fallback authority before current reader point required quantum
local notation "sourceCapture" => capture construct callbackConstruct fallback
local notation "Cfg" => Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients
local notation "Action" => Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients
local notation "Occurrence" => CausalEvent (HistoryOccurrence clients)

/-- The existing ordinary action runner, with the actual retained source. -/
abbrev execute (actions : List Action) (state : Cfg) :=
  runActions sourceStep sourceCapture capacity (fun _ => true) actions state

/-- A specification word of the actual source path. The bounded recorder
below remains the existing streaming worker and does not construct this word. -/
def events (actions : List Action) (state : Cfg) : List Occurrence :=
  pathOccurrences sourceStep sourceCapture capacity (fun _ => true)
    (actionPath sourceStep sourceCapture capacity (fun _ => true) actions state)

/-- Observer selection reuses the existing entry and its ordinary no-observer
branch. No history or numerical account is added to the source Call. -/
abbrev observe (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (state : Cfg) :=
  enterActionObservers sourceStep sourceCapture capacity (fun _ => true) history account actions state

theorem observe_erases (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (state : Cfg) :
    (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
      history account actions state).2.2 =
      execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state :=
  enterActionObservers_erases sourceStep sourceCapture capacity (fun _ => true) history account actions state

/-- Lawful erasure preserves the actual source computation, not just its
written answers or a trace-defined surrogate. -/
theorem observe_keeps_actual_source (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (state : Cfg)
    (execution : Execution (Call construct callbackConstruct fallback (Context := Context))
      (Borrowed construct callbackConstruct fallback) Empty (Loan construct callbackConstruct fallback))
    (attached : state.execution = some execution) (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer)
    (coherent : Coherent construct callbackConstruct fallback execution.producer) :
    ∃ next, (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
        history account actions state).2.2.execution = some next ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter next.producer ∧
      Coherent construct callbackConstruct fallback next.producer := by
  rw [observe_erases]
  exact actions_keep_actual_source construct callbackConstruct fallback authority before current reader point required
    quantum capacity actions state execution attached items parameter safe coherent

set_option backward.isDefEq.respectTransparency false in
/-- The maintained path account and chronological occurrence account read the
same actual operations as the joint observer. Scheduler microsteps, source
inspections and successful consumer deliveries remain separate quantities. -/
theorem source_accounts (actions : List Action) (record : Prefix Occurrence)
    (account : ProtocolAccount) (state : Cfg) :
    letI : Quiver.{0} Cfg := actionQuiver (Output := Owner) (clients := clients) sourceStep sourceCapture capacity (fun _ => true)
    observeActions sourceStep sourceCapture capacity (fun _ => true) actions record account state =
      (Prefix.append record
        (events construct callbackConstruct fallback authority before current reader point required quantum capacity actions state),
        execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state,
        account * (splitAccount (Output := Owner) (clients := clients) sourceStep sourceCapture capacity (fun _ => true)).of
          (actionPath sourceStep sourceCapture capacity (fun _ => true) actions state)) :=
  observeActions_eq_source_accounts sourceStep sourceCapture capacity (fun _ => true) actions record account state

/-- From the real open Call, every recorded source occurrence is an ordered
admission or delivery, with the actual source invariant at its retained end. -/
theorem open_history_source (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (items : List Input) (parameter : Nat) (context : Context) (limit : Nat) :
    let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
    let word := events construct callbackConstruct fallback authority before current reader point required quantum capacity actions start
    let final := (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
      history account actions start).2.2
    ProtocolSync word final ∧ CausalReceipt.Ordered [] word ∧
      CausalReceipt.WellFormed [] (protocolReceipt word) ∧
      ∃ next, final.execution = some next ∧
        BodyCallAdmission.captured construct callbackConstruct fallback
          (OrderedDependencyStore.query before reader) items parameter next.producer ∧
        Coherent construct callbackConstruct fallback next.producer := by
  dsimp only
  rw [observe_erases]
  have protocol := protocol_from_initial sourceStep sourceCapture capacity (fun _ => true)
    (BodyCallAdmission.openCall construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter context) before limit actions
  refine ⟨protocol.1, protocol.2.1, protocol.2.2.1, ?_⟩
  exact actions_keep_actual_source construct callbackConstruct fallback authority before current reader point required
    quantum capacity actions _ _ rfl items parameter
    (BodyCallAdmission.open_captured construct callbackConstruct fallback _ items parameter context)
    (open_coherent construct callbackConstruct fallback _ items parameter context)

/-- Forgetting a bounded diary retains the same actual continuation and paid
account. The reference word is neither replayed nor reconstructed at runtime. -/
theorem forget_history (record : Prefix Occurrence) (account : ProtocolAccount)
    (first second : List Action) (state : Cfg) :
    observe construct callbackConstruct fallback authority before current reader point required quantum capacity none
      (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
        (some record) (some account) first state).2.1 second
      (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
        (some record) (some account) first state).2.2 =
      (none, some (count sourceStep sourceCapture capacity (fun _ => true) (first ++ second) account state).2,
        execute construct callbackConstruct fallback authority before current reader point required quantum capacity
          (first ++ second) state) := by
  unfold observe execute
  rw [forget_action_history_preserves_account]
  rw [count_erases]

/-- Resuming observation uses its retained capacity, accounts and actual saved
Call. This fixed-context law does not combine grants across authority changes. -/
theorem observe_append (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (first second : List Action) (state : Cfg) :
    observe construct callbackConstruct fallback authority before current reader point required quantum capacity
      history account (first ++ second) state =
      observe construct callbackConstruct fallback authority before current reader point required quantum capacity
        (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
          history account first state).1
        (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
          history account first state).2.1 second
        (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
          history account first state).2.2 :=
  enterActionObservers_append sourceStep sourceCapture capacity (fun _ => true) history account first second state

/-- A diary occurrence has an actual admission/delivery operation at an actual
saved prefix of this source execution. Membership is not replay permission. -/
theorem event_has_actual_operation (actions : List Action) (state : Cfg) {event : Occurrence}
    (present : event ∈ events construct callbackConstruct fallback authority before current reader point required quantum capacity
      actions state) :
    ∃ done action later, actions = done ++ action :: later ∧
      (actionResult sourceStep sourceCapture capacity (fun _ => true) action
        (execute construct callbackConstruct fallback authority before current reader point required quantum capacity done state)).occurrence =
        some event :=
  projected_occurrence_is_a_source_reply sourceStep sourceCapture capacity (fun _ => true) actions state present

set_option backward.isDefEq.respectTransparency false in
/-- The history map retains actual path endpoints and sends composition to
chronological concatenation through the maintained occurrence RunAccount. -/
theorem path_composition {first middle last : Cfg} :
    letI : Quiver.{0} Cfg := actionQuiver (Output := Owner) (clients := clients)
      sourceStep sourceCapture capacity (fun _ => true)
    ∀ (left : Quiver.Path first middle) (right : Quiver.Path middle last),
      pathOccurrences sourceStep sourceCapture capacity (fun _ => true) (left.comp right) =
        pathOccurrences sourceStep sourceCapture capacity (fun _ => true) left ++
          pathOccurrences sourceStep sourceCapture capacity (fun _ => true) right :=
  pathOccurrences_comp sourceStep sourceCapture capacity (fun _ => true)

/-- A resumed diary contains only actual suffix events. Its earlier event
identities are an explicit causal boundary and are not fabricated replay. -/
theorem open_suffix_boundary (first second : List Action) (items : List Input)
    (parameter : Nat) (context : Context) (limit : Nat) :
    let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
    let prefixWord := events construct callbackConstruct fallback authority before current reader point required quantum capacity first start
    let mid := execute construct callbackConstruct fallback authority before current reader point required quantum capacity first start
    let suffix := events construct callbackConstruct fallback authority before current reader point required quantum capacity second mid
    events construct callbackConstruct fallback authority before current reader point required quantum capacity (first ++ second) start =
      prefixWord ++ suffix ∧
      CausalReceipt.WellFormed (prefixWord.map CausalEvent.event) (protocolReceipt suffix) ∧
      (∀ event ∈ prefixWord, event ∉ suffix) := by
  have result := protocol_suffix_boundary sourceStep sourceCapture capacity (fun _ => true)
    (BodyCallAdmission.openCall construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter context) before limit first second
  exact ⟨result.1, result.2.1, result.2.2.2.1⟩

theorem execute_context (actions : List Action) (state : Cfg) :
    (execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state).context =
      state.context := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | pump =>
          exact (ih (pump sourceStep sourceCapture capacity (fun _ => true) state).2).trans
            (pump_preserves_context_cursors_publications sourceStep sourceCapture capacity (fun _ => true) state).1
      | deliver client owner =>
          exact (ih (deliver (fun _ => true) state client owner).2).trans rfl

namespace Scopes

open Mettapedia.Algebra.SharedCoefficientLedger

variable {V Observer : Type} [DecidableEq V] [DecidableEq Observer]
    (coefficient : Stored (Output := Output) → V)

local notation "sourceLedger" => Coefficients.ledger construct callbackConstruct fallback reader coefficient
local notation "Account" => Scoped Nat (OrderedDependencyStore.ReadStamp size) V Observer

omit [DecidableEq V] in
/-- Actual execution extends the existing factor ledger in order. Dependency
and coefficient fields are retained along with occurrence identity. -/
theorem execute_ledger_extends (actions : List Action) (state : Cfg) :
    ∃ suffix, sourceLedger
      (execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state) =
      sourceLedger state ++ suffix := by
  obtain ⟨suffix, rows⟩ := runActions_extends_rows sourceStep sourceCapture capacity (fun _ => true) actions state
  have base := runActions_preserves_base sourceStep sourceCapture capacity (fun _ => true) actions state
  have context := execute_context construct callbackConstruct fallback authority before current reader point required
    quantum capacity actions state
  refine ⟨(suffix.zipIdx (state.delivery.log.base + state.delivery.log.rows.length)).map
    (fun occurrence => ⟨occurrence.2, OrderedDependencyStore.readStamp state.context reader, coefficient occurrence.1⟩), ?_⟩
  simp only [Coefficients.ledger, rows, base, context, List.zipIdx_append, List.map_append]

/-- Start observation of the real buffered account with no acquired claims. -/
def begin (state : Cfg) : Account := ⟨sourceLedger state, fun _ => none⟩

/-- Extend only the production field using the actual reached source state;
previous scope claims are retained, not reissued as execution authority. -/
def carry (entry : Account) (state : Cfg) : Account := ⟨sourceLedger state, entry.claims⟩

def resume (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer) :
    Option (Account × Ledger Nat (OrderedDependencyStore.ReadStamp size) V) × Cfg :=
  if entry.productions = sourceLedger state then
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    (Scoped.handleSince? entry (carry construct callbackConstruct fallback reader coefficient entry actual) observer, actual)
  else (none, state)

theorem carry_extends (actions : List Action) (state : Cfg) (entry : Account)
    (agrees : entry.productions = sourceLedger state) :
    Scoped.extendsOccurrenceCapture entry
      (carry construct callbackConstruct fallback reader coefficient entry
        (execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state)) = true := by
  obtain ⟨suffix, extended⟩ := execute_ledger_extends construct callbackConstruct fallback authority before current reader point required
    quantum capacity coefficient actions state
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    exact ⟨Coefficients.ledger_valid construct callbackConstruct fallback reader coefficient _,
      by change entry.productions.Sublist (sourceLedger _); rw [agrees, extended]; exact List.sublist_append_left _ _⟩
  · apply List.all_eq_true.mpr
    intro factor present
    cases claim : entry.claims factor.identity <;> simp [carry, claim]

/-- The captured ledger is validated against the actual starting source state
before any new source operation. A mismatch cannot reset or replay the source. -/
theorem resume_refused (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer)
    (mismatch : entry.productions ≠ sourceLedger state) :
    resume construct callbackConstruct fallback authority before current reader point required quantum capacity coefficient
      actions state entry observer = (none, state) := by
  simp [resume, mismatch]

/-- For a matching captured account, admission follows the actual source
continuation and the existing scoped snapshot claim operation. -/
theorem resume_granted (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer)
    (agrees : entry.productions = sourceLedger state) :
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    let world := carry construct callbackConstruct fallback reader coefficient entry actual
    resume construct callbackConstruct fallback authority before current reader point required quantum capacity coefficient
      actions state entry observer =
      (some (Scoped.handleSince entry.productions observer world,
        Scoped.selectedSince entry.productions world), actual) := by
  simp only [resume, agrees, ↓reduceIte, Scoped.handleSince?]
  rw [carry_extends construct callbackConstruct fallback authority before current reader point required quantum capacity
    coefficient actions state entry agrees]
  rfl

omit [DecidableEq Output] [DecidableEq Owner] [DecidableEq V] [DecidableEq Observer] in
theorem begin_supported (state : Cfg) :
    (begin construct callbackConstruct fallback reader coefficient state (Observer := Observer)).Supported := by
  intro identity observer claimed
  cases claimed

omit [DecidableEq V] [DecidableEq Observer] in
/-- Supported claims remain attached to actual productions after extension
and after claiming the fresh snapshot. -/
theorem carry_supported (actions : List Action) (state : Cfg) (entry : Account)
    (agrees : entry.productions = sourceLedger state) (supported : entry.Supported) :
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    let world := carry construct callbackConstruct fallback reader coefficient entry actual
    world.Supported := by
  dsimp only
  intro identity prior claimed
  have member := supported identity prior claimed
  obtain ⟨suffix, extended⟩ := execute_ledger_extends construct callbackConstruct fallback authority before current reader point required
    quantum capacity coefficient actions state
  have beforeMember : identity ∈ identities (sourceLedger state) := agrees ▸ member
  change identity ∈ identities (sourceLedger _ )
  rw [extended, identities, List.map_append]
  exact List.mem_append_left _ beforeMember

omit [DecidableEq V] [DecidableEq Observer] in
theorem granted_supported (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer)
    (agrees : entry.productions = sourceLedger state) (supported : entry.Supported) :
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    let world := carry construct callbackConstruct fallback reader coefficient entry actual
    (Scoped.handleSince entry.productions observer world).Supported :=
  Scoped.handleSince_supported _ _ _
    (carry_supported construct callbackConstruct fallback authority before current reader point required quantum capacity
      coefficient actions state entry agrees supported)

omit [DecidableEq V] [DecidableEq Observer] in
/-- Selection is by genuine post-capture admission identity, not value
inequality; equal answers can remain distinct fresh factors. -/
theorem selected_is_actual_fresh (actions : List Action) (state : Cfg) (entry : Account)
    (factor : Factor Nat (OrderedDependencyStore.ReadStamp size) V) :
    factor ∈ Scoped.selectedSince entry.productions
      (carry construct callbackConstruct fallback reader coefficient entry
        (execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state)) ↔
      factor ∈ sourceLedger (execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state) ∧
        entry.claims factor.identity = none ∧ factor.identity ∉ identities entry.productions :=
  Scoped.mem_selectedSince _ _ _

omit [DecidableEq V] [DecidableEq Observer] in
theorem prior_claims_kept (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer)
    (identity : Nat) (prior : Observer) (claimed : entry.claims identity = some prior) :
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    (Scoped.handleSince entry.productions observer
      (carry construct callbackConstruct fallback reader coefficient entry actual)).claims identity = some prior :=
  Scoped.handleSince_prior_claim_preserved _ _ _ claimed

omit [DecidableEq V] [DecidableEq Observer] in
theorem snapshot_not_reselected (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer) :
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    let world := carry construct callbackConstruct fallback reader coefficient entry actual
    Scoped.selectedSince entry.productions (Scoped.handleSince entry.productions observer world) = [] :=
  Scoped.selectedSince_after_handle _ _ _

/-- Both account refusal and successful scoped resumption preserve the actual
independent source view and full saved Call. -/
theorem resume_keeps_source (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer)
    (execution : Execution (Call construct callbackConstruct fallback (Context := Context))
      (Borrowed construct callbackConstruct fallback) Empty (Loan construct callbackConstruct fallback))
    (attached : state.execution = some execution) (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer)
    (coherent : Coherent construct callbackConstruct fallback execution.producer) :
    ∃ next, (resume construct callbackConstruct fallback authority before current reader point required quantum capacity coefficient
        actions state entry observer).2.execution = some next ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter next.producer ∧
      Coherent construct callbackConstruct fallback next.producer := by
  by_cases agrees : entry.productions = sourceLedger state
  · rw [resume_granted construct callbackConstruct fallback authority before current reader point required quantum capacity
      coefficient actions state entry observer agrees]
    exact actions_keep_actual_source construct callbackConstruct fallback authority before current reader point required
      quantum capacity actions state execution attached items parameter safe coherent
  · rw [resume_refused construct callbackConstruct fallback authority before current reader point required quantum capacity
      coefficient actions state entry observer agrees]
    exact ⟨execution, attached, safe, coherent⟩

omit [DecidableEq V] [DecidableEq Observer] in
/-- Every factor of an actual open-source run cites an actual admission edge.
Its origin is obtained from the maintained protocol invariant and source path. -/
theorem factor_has_actual_operation (actions : List Action) (items : List Input) (parameter : Nat)
    (context : Context) (limit : Nat) (factor : Factor Nat (OrderedDependencyStore.ReadStamp size) V)
    (present : factor ∈ sourceLedger
      (execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions
        (initial construct callbackConstruct fallback before reader items parameter context Owner clients limit))) :
    let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
    ∃ event done action later,
      event.event = HistoryOccurrence.admission factor.identity ∧
      actions = done ++ action :: later ∧
      (actionResult sourceStep sourceCapture capacity (fun _ => true) action
        (execute construct callbackConstruct fallback authority before current reader point required quantum capacity done start)).occurrence = some event := by
  dsimp only
  let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
  let final := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions start
  let word := events construct callbackConstruct fallback authority before current reader point required quantum capacity actions start
  have protocol := protocol_from_initial sourceStep sourceCapture capacity (fun _ => true)
    (BodyCallAdmission.openCall construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter context) before limit actions
  have identified : identities (sourceLedger final) = List.range final.delivery.log.rows.length := by
    simp only [Coefficients.ledger, identities, List.map_map, Function.comp_def]
    rw [List.zipIdx_map_snd]
    have anchored : final.delivery.log.base = 0 := protocol.1.anchored
    rw [anchored, List.range_eq_range']
  have factorId : factor.identity ∈ List.range final.delivery.log.rows.length := by
    rw [← identified]
    exact List.mem_map.mpr ⟨factor, present, rfl⟩
  have root : HistoryOccurrence.admission factor.identity ∈ (protocolReceipt word).roots := by
    have roots : (protocolReceipt word).roots =
        (List.range final.delivery.log.rows.length).map HistoryOccurrence.admission := protocol.2.2.2
    rw [roots]
    exact List.mem_map.mpr ⟨factor.identity, factorId, rfl⟩
  obtain ⟨event, member, identity⟩ := List.mem_map.mp (admissionIdentity_in_support word root)
  obtain ⟨done, action, later, schedule, actual⟩ := event_has_actual_operation construct callbackConstruct fallback authority
    before current reader point required quantum capacity actions start member
  exact ⟨event, done, action, later, identity, schedule, actual⟩

/-- Read an older scope capture against the current actual source ledger.
This operation never advances the producer; the existing admission validates
captured factors and claims before acquiring the fresh snapshot. -/
def readScope (state : Cfg) (captured currentAccount : Account) (observer : Observer) :
    Option (Account × Ledger Nat (OrderedDependencyStore.ReadStamp size) V) :=
  if currentAccount.productions = sourceLedger state then
    Scoped.handleSince? captured currentAccount observer
  else none

omit [DecidableEq Output] [DecidableEq Owner] in
theorem readScope_refused (state : Cfg) (captured currentAccount : Account) (observer : Observer)
    (mismatch : currentAccount.productions ≠ sourceLedger state) :
    readScope construct callbackConstruct fallback reader coefficient state captured currentAccount observer = none := by
  simp [readScope, mismatch]

omit [DecidableEq Output] [DecidableEq Owner] in
/-- Accepted nested observation retains the actual production account and
cannot select the same snapshot again. -/
theorem readScope_spec (state : Cfg) (captured currentAccount result : Account)
    (observer : Observer) (observed : Ledger Nat (OrderedDependencyStore.ReadStamp size) V)
    (accepted : readScope construct callbackConstruct fallback reader coefficient state captured currentAccount observer =
      some (result, observed)) :
    result.productions = sourceLedger state ∧
      observed = Scoped.selectedSince captured.productions currentAccount ∧
      Scoped.selectedSince captured.productions result = [] := by
  unfold readScope at accepted
  split at accepted
  · rename_i agrees
    have spec := Scoped.handleSince_spec accepted
    exact ⟨spec.1.trans agrees, spec.2⟩
  · cases accepted

omit [DecidableEq Output] [DecidableEq Owner] in
/-- A stale factor capture or a lost prior claim is a refusal of the existing
scoped admission, even if the current row payloads have not changed. -/
theorem readScope_bad_capture (state : Cfg) (captured currentAccount : Account) (observer : Observer)
    (refused : Scoped.extendsOccurrenceCapture captured currentAccount = false) :
    readScope construct callbackConstruct fallback reader coefficient state captured currentAccount observer = none := by
  unfold readScope
  split
  · simp [Scoped.handleSince?, refused]
  · rfl

omit [DecidableEq Output] [DecidableEq Owner] in
theorem readScope_prior_claim (state : Cfg) (captured currentAccount result : Account)
    (observer prior : Observer) (identity : Nat)
    (observed : Ledger Nat (OrderedDependencyStore.ReadStamp size) V)
    (accepted : readScope construct callbackConstruct fallback reader coefficient state captured currentAccount observer =
      some (result, observed))
    (claimed : currentAccount.claims identity = some prior) : result.claims identity = some prior := by
  unfold readScope at accepted
  split at accepted
  · unfold Scoped.handleSince? at accepted
    split at accepted
    · cases accepted
      exact Scoped.handleSince_prior_claim_preserved _ _ _ claimed
    · cases accepted
  · cases accepted

section Transport

variable {Identity' Dependency' Observer' : Type} [DecidableEq Identity']

/-- Transport the existing scoped account using its finite production support.
The claim lookup ranges over actual factors, so unsupported copied labels do
not gain a transported claim. No producer or recorder is executed. -/
def transport (name : Nat → Identity') (dependency : OrderedDependencyStore.ReadStamp size → Dependency')
    (owner : Observer → Observer') (account : Account) : Scoped Identity' Dependency' V Observer' :=
  ⟨rename name dependency account.productions,
    fun identity => (account.productions.find? (fun factor => decide (name factor.identity = identity))).bind
      (fun factor => (account.claims factor.identity).map owner)⟩

omit [DecidableEq V] [DecidableEq Observer] in
theorem transport_claims (name : Nat → Identity')
    (dependency : OrderedDependencyStore.ReadStamp size → Dependency') (owner : Observer → Observer')
    (account : Account) (supported : account.Supported) (names : Function.Injective name) (identity : Nat) :
    (transport name dependency owner account).claims (name identity) = (account.claims identity).map owner := by
  cases found : account.productions.find? (fun factor => decide (name factor.identity = name identity)) with
  | some factor =>
      have predicate : decide (name factor.identity = name identity) = true :=
        List.find?_some (p := fun (factor : Factor Nat (OrderedDependencyStore.ReadStamp size) V) =>
          decide (name factor.identity = name identity)) found
      have equal := names (of_decide_eq_true predicate)
      simp [transport, found, equal]
  | none =>
      cases claimed : account.claims identity with
      | none => simp [transport, found]
      | some prior =>
          obtain ⟨factor, present, equal⟩ := List.mem_map.mp (supported identity prior claimed)
          have absent := (List.find?_eq_none.mp found) factor present
          simp [equal] at absent

omit [DecidableEq V] [DecidableEq Observer] in
theorem transport_supported (name : Nat → Identity')
    (dependency : OrderedDependencyStore.ReadStamp size → Dependency') (owner : Observer → Observer')
    (account : Account) : (transport name dependency owner account).Supported := by
  intro identity observer claimed
  cases found : account.productions.find? (fun factor => decide (name factor.identity = identity)) with
  | none => simp [transport, found] at claimed
  | some factor =>
      have predicate : decide (name factor.identity = identity) = true :=
        List.find?_some (p := fun (factor : Factor Nat (OrderedDependencyStore.ReadStamp size) V) =>
          decide (name factor.identity = identity)) found
      have equal := of_decide_eq_true predicate
      have present := List.mem_of_find?_eq_some found
      change identity ∈ identities (rename name dependency account.productions)
      rw [identities_rename]
      exact List.mem_map.mpr ⟨factor.identity, List.mem_map.mpr ⟨factor, present, rfl⟩, equal⟩

omit [DecidableEq V] [DecidableEq Observer] in
/-- Selection of actual post-capture factors commutes with the constructed
transport. Injectivity prevents different production identities coalescing. -/
theorem transport_selection (name : Nat → Identity')
    (dependency : OrderedDependencyStore.ReadStamp size → Dependency') (owner : Observer → Observer')
    (capture : Ledger Nat (OrderedDependencyStore.ReadStamp size) V) (account : Account)
    (supported : account.Supported) (names : Function.Injective name) :
    Scoped.selectedSince (rename name dependency capture) (transport name dependency owner account) =
      rename name dependency (Scoped.selectedSince capture account) :=
  Scoped.selectedSince_transport names dependency owner capture account
    (transport name dependency owner account) rfl (transport_claims name dependency owner account supported names)

omit [DecidableEq V] [DecidableEq Observer] in
theorem transport_handled_claim (name : Nat → Identity')
    (dependency : OrderedDependencyStore.ReadStamp size → Dependency') (owner : Observer → Observer')
    (capture : Ledger Nat (OrderedDependencyStore.ReadStamp size) V) (account : Account)
    (supported : account.Supported) (names : Function.Injective name) (observer : Observer) (identity : Nat) :
    (Scoped.handleSince (rename name dependency capture) (owner observer)
      (transport name dependency owner account)).claims (name identity) =
      ((Scoped.handleSince capture observer account).claims identity).map owner :=
  Scoped.handleSince_claim_transport names dependency owner capture account
    (transport name dependency owner account) rfl (transport_claims name dependency owner account supported names) observer identity

omit [DecidableEq V] [DecidableEq Observer] in
/-- Ordered coefficient readout is unchanged, without commutative or
cancellation assumptions. This does not identify coefficients with native work. -/
theorem transport_denotation [Monoid V] (name : Nat → Identity')
    (dependency : OrderedDependencyStore.ReadStamp size → Dependency') (owner : Observer → Observer')
    (capture : Ledger Nat (OrderedDependencyStore.ReadStamp size) V) (account : Account)
    (supported : account.Supported) (names : Function.Injective name) :
    denote (Scoped.selectedSince (rename name dependency capture) (transport name dependency owner account)) =
      denote (Scoped.selectedSince capture account) := by
  rw [transport_selection name dependency owner capture account supported names, denote_rename]

omit [DecidableEq V] [DecidableEq Observer] in
/-- The constructed transport applies to the actual fresh source factors
before their scoped claim, including noncommutative and zero coefficients. -/
theorem transport_actual_fresh [Monoid V] (name : Nat → Identity')
    (dependency : OrderedDependencyStore.ReadStamp size → Dependency') (owner : Observer → Observer')
    (actions : List Action) (state : Cfg) (entry : Account)
    (agrees : entry.productions = sourceLedger state) (supported : entry.Supported)
    (names : Function.Injective name) :
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    let world := carry construct callbackConstruct fallback reader coefficient entry actual
    denote (Scoped.selectedSince (rename name dependency entry.productions) (transport name dependency owner world)) =
      denote (Scoped.selectedSince entry.productions world) :=
  transport_denotation name dependency owner _ _
    (carry_supported construct callbackConstruct fallback authority before current reader point required quantum capacity
      coefficient actions state entry agrees supported) names

end Transport

#print axioms execute_ledger_extends
#print axioms carry_supported
#print axioms transport_actual_fresh
#print axioms carry_extends
#print axioms readScope_refused
#print axioms readScope_spec
#print axioms readScope_bad_capture
#print axioms readScope_prior_claim
#print axioms transport_claims
#print axioms transport_supported
#print axioms transport_selection
#print axioms transport_handled_claim
#print axioms transport_denotation
#print axioms resume_refused
#print axioms resume_granted
#print axioms begin_supported
#print axioms granted_supported
#print axioms selected_is_actual_fresh
#print axioms prior_claims_kept
#print axioms snapshot_not_reselected
#print axioms resume_keeps_source
#print axioms factor_has_actual_operation

end Scopes


#print axioms path_composition
#print axioms open_suffix_boundary
#print axioms execute_context
#print axioms observe_erases
#print axioms observe_keeps_actual_source
#print axioms source_accounts
#print axioms open_history_source
#print axioms forget_history
#print axioms observe_append
#print axioms event_has_actual_operation

end History

end BodyCallShared

/-! Physical equation activation accounts decorate the maintained body/call
provider. The client, replies, phase indices and source instructions are the
existing ones. Proof-only invariants connect saved cursor lineages to paid
activations; neither completion nor valuation runs future source work. -/
namespace BodyCallWeighted

open Mettapedia.Algebra.SharedCoefficientLedger
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Cursor.Fold.OwnedSequence.CallbackBoundary

variable {Input Output Weight Context : Type} [Semiring Weight]
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (clause : WeighClause Weight (BodyCall.Graded.Activation Input Output))

abbrev CheckedState := { state : BodyCall.Graded.State Input Output Weight //
  BodyCall.Graded.Sound clause state ∧ BodyCall.Graded.Authentic state ∧ BodyCall.Graded.Aligned state }

def provider : Cursor.Provider (BodyCallProtocol.protocol (Item := Input) (Value := Output)) where
  State _ phase := { state : CheckedState clause // state.val.core.phase = phase.down }
  step state _ :=
    let moved := BodyCall.Graded.step construct callbackConstruct fallback clause state.val.val
    ⟨moved.1, ⟨⟨moved.2,
      BodyCall.Graded.step_sound construct callbackConstruct fallback clause _ state.val.property.1,
      BodyCall.Graded.step_authentic construct callbackConstruct fallback clause _ state.val.property.2.1,
      BodyCall.Graded.step_aligned construct callbackConstruct fallback clause _ state.val.property.2.2⟩,
      congrArg BodyCall.State.phase (BodyCall.Graded.step_link construct callbackConstruct fallback clause _)⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Erasing grading preserves every actual reply and exact saved source state. -/
def erase : Cursor.Hom (provider construct callbackConstruct fallback clause)
    (BodyCallProtocol.provider construct callbackConstruct fallback) where
  map state := ⟨state.val.val.core, state.property⟩
  step state request := by
    change (⟨(BodyCall.Graded.step construct callbackConstruct fallback clause state.val.val).1,
      ⟨(BodyCall.Graded.step construct callbackConstruct fallback clause state.val.val).2.core, _⟩⟩ :
        Σ moved : BodyCall.Move Input Output, { core : BodyCall.State Input Output // core.phase = moved.next.phase }) =
      ⟨BodyCall.step construct callbackConstruct fallback state.val.val.core,
        ⟨(BodyCall.step construct callbackConstruct fallback state.val.val.core).next, rfl⟩⟩
    calc
      _ = ⟨(BodyCall.Graded.step construct callbackConstruct fallback clause state.val.val).1,
          ⟨(BodyCall.Graded.step construct callbackConstruct fallback clause state.val.val).1.next, rfl⟩⟩ := by
        apply congrArg (Sigma.mk _)
        exact Subtype.ext (BodyCall.Graded.step_link construct callbackConstruct fallback clause _)
      _ = _ := congrArg (fun moved : BodyCall.Move Input Output =>
        (⟨moved, ⟨moved.next, rfl⟩⟩ : Σ moved : BodyCall.Move Input Output,
          { core : BodyCall.State Input Output // core.phase = moved.next.phase }))
          (BodyCall.Graded.step_move construct callbackConstruct fallback clause _)

abbrev Packet := Cursor.Packet (provider construct callbackConstruct fallback clause)
  (BodyCallProtocol.client (Item := Input) (Value := Output)) (⟨()⟩ : ULift Unit)
abbrev Outcome := Cursor.Outcome (provider construct callbackConstruct fallback clause)
  (BodyCallProtocol.client (Item := Input) (Value := Output)) (⟨()⟩ : ULift Unit)
abbrev Returned := Cursor.Finished (provider construct callbackConstruct fallback clause)
  (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit)

def packet (state : CheckedState clause) : Packet construct callbackConstruct fallback clause :=
  ⟨⟨state.val.core.phase⟩, ⟨.advance state.val.core, rfl⟩, ⟨state, rfl⟩⟩

def openChecked (authored : List (Equation Output)) (items : List Input) (parameter : Nat) : CheckedState clause :=
  ⟨BodyCall.Graded.openState authored items parameter (.observe .noAnswers),
    BodyCall.Graded.open_sound clause authored items parameter _,
    BodyCall.Graded.open_authentic authored items parameter _,
    BodyCall.Graded.open_aligned authored items parameter _⟩

def requestCharge : Cursor.Charge (provider construct callbackConstruct fallback clause) := fun _ _ => 1

def eraseOutcome : Outcome construct callbackConstruct fallback clause →
    BodyCallProtocol.Outcome construct callbackConstruct fallback :=
  (erase construct callbackConstruct fallback clause).outcome
    (BodyCallProtocol.client (Item := Input) (Value := Output))

def stateView : Outcome construct callbackConstruct fallback clause → CheckedState clause
  | .paused packet => packet.2.2.val
  | .done returned => returned.2.2.val

def run (fuel : Nat) (state : CheckedState clause) :=
  Cursor.advance (provider construct callbackConstruct fallback clause) BodyCallProtocol.client
    (requestCharge construct callbackConstruct fallback clause) fuel
    (packet construct callbackConstruct fallback clause state)

def resume (fuel : Nat) (previous : Nat × Outcome construct callbackConstruct fallback clause) :=
  Cursor.resume (provider construct callbackConstruct fallback clause) BodyCallProtocol.client
    (requestCharge construct callbackConstruct fallback clause) fuel previous

theorem run_zero (state : CheckedState clause) :
    run construct callbackConstruct fallback clause 0 state =
      (0, .paused (packet construct callbackConstruct fallback clause state)) := rfl

theorem resume_done (fuel paid : Nat) (returned : Returned construct callbackConstruct fallback clause) :
    resume construct callbackConstruct fallback clause fuel (paid, .done returned) = (paid, .done returned) := rfl

#print axioms run_zero
#print axioms resume_done

theorem run_projection (fuel : Nat) (state : CheckedState clause) :
    ((run construct callbackConstruct fallback clause fuel state).1,
      eraseOutcome construct callbackConstruct fallback clause
        (run construct callbackConstruct fallback clause fuel state).2) =
      BodyCallProtocol.run construct callbackConstruct fallback fuel state.val.core :=
  (erase construct callbackConstruct fallback clause).advance_account
    BodyCallProtocol.client (requestCharge construct callbackConstruct fallback clause)
    (BodyCallProtocol.requestCharge construct callbackConstruct fallback) (fun _ _ => rfl) fuel _

theorem resume_projection (fuel : Nat) (previous : Nat × Outcome construct callbackConstruct fallback clause) :
    ((resume construct callbackConstruct fallback clause fuel previous).1,
      eraseOutcome construct callbackConstruct fallback clause
        (resume construct callbackConstruct fallback clause fuel previous).2) =
      BodyCallProtocol.resume construct callbackConstruct fallback fuel
        (previous.1, eraseOutcome construct callbackConstruct fallback clause previous.2) :=
  (erase construct callbackConstruct fallback clause).resume_account
    BodyCallProtocol.client (requestCharge construct callbackConstruct fallback clause)
    (BodyCallProtocol.requestCharge construct callbackConstruct fallback) (fun _ _ => rfl) fuel _

theorem run_split (earlier later : Nat) (state : CheckedState clause) :
    run construct callbackConstruct fallback clause (earlier + later) state =
      resume construct callbackConstruct fallback clause later
        (run construct callbackConstruct fallback clause earlier state) :=
  Cursor.advance_add _ _ _ earlier later _

theorem run_open_source (fuel : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat) :
    let actual := run construct callbackConstruct fallback clause fuel (openChecked clause authored items parameter)
    BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
      (eraseOutcome construct callbackConstruct fallback clause actual.2) =
        source construct callbackConstruct authored items parameter := by
  have projection := congrArg Prod.snd (run_projection construct callbackConstruct fallback clause fuel
    (openChecked clause authored items parameter))
  dsimp only at projection
  dsimp only
  rw [projection]
  simpa only [BodyCallProtocol.unacceptedRows, ← BodyCallProtocol.rows_view, openChecked, BodyCall.Graded.openState] using
    BodyCallProtocol.run_open_preserves_source construct callbackConstruct fallback fuel authored items parameter

/-- Every actual outcome carries valid, licensed branch factors valued at
its captured activation; equal-valued answers do not identify their factors. -/
theorem outcome_source_factors (outcome : Outcome construct callbackConstruct fallback clause) :
    let actual := (stateView construct callbackConstruct fallback clause outcome).val
    Valid actual.paid ∧ Valid actual.loan ∧
      (∀ produced ∈ actual.loan, BodyCall.Graded.Licensed produced.dependency) ∧
      actual.loan.map Factor.coefficient = actual.loan.map (fun produced => WeighClause.eval produced.dependency clause) := by
  let checked := stateView construct callbackConstruct fallback clause outcome
  exact ⟨BodyCall.Graded.paid_valid clause _ checked.property.1,
    BodyCall.Graded.loan_valid clause _ checked.property.1,
    fun produced present => checked.property.2.1 produced (checked.property.1.2.2.2.subset present),
    BodyCall.Graded.loan_source_coefficients clause _ checked.property.1⟩

#print axioms run_projection
#print axioms resume_projection
#print axioms run_split
#print axioms run_open_source
#print axioms outcome_source_factors

namespace Compact

private def packed (result : BodyCall.Move Input Output × BodyCall.Graded.Compact.State Input Output Weight)
    (linked : result.2.core = result.1.next) :
    Σ moved : BodyCall.Move Input Output,
      { state : BodyCall.Graded.Compact.State Input Output Weight // state.core.phase = moved.next.phase } :=
  ⟨result.1, ⟨result.2, congrArg BodyCall.State.phase linked⟩⟩

omit [Semiring Weight] in
private theorem packed_ext
    (first second : BodyCall.Move Input Output × BodyCall.Graded.Compact.State Input Output Weight)
    (firstLink : first.2.core = first.1.next) (secondLink : second.2.core = second.1.next)
    (same : first = second) : packed first firstLink = packed second secondLink := by
  cases same
  rfl

/-- The compact provider shares one optional-attachment transition. -/
def providerWith (attachment : BodyCall.Graded.Activation Input Output → Option Weight) :
    Cursor.Provider (BodyCallProtocol.protocol (Item := Input) (Value := Output)) where
  State _ phase := { state : BodyCall.Graded.Compact.State Input Output Weight // state.core.phase = phase.down }
  step state _ := packed (BodyCall.Graded.Compact.stepWith construct callbackConstruct fallback attachment state.val)
    (BodyCall.Graded.Compact.stepWith_link construct callbackConstruct fallback attachment state.val)

def provider : Cursor.Provider (BodyCallProtocol.protocol (Item := Input) (Value := Output)) :=
  providerWith construct callbackConstruct fallback (fun activation => some (WeighClause.eval activation clause))

/-- The executable cursor needs live lineages and one fresh ordinal, not a
stored ledger of earlier failed activations. -/
def erase : Cursor.Hom (BodyCallWeighted.provider construct callbackConstruct fallback clause)
    (provider construct callbackConstruct fallback clause) where
  map state := ⟨BodyCall.Graded.Compact.erase state.val.val, state.property⟩
  step _state _request :=
    packed_ext _ _ (BodyCall.Graded.step_link construct callbackConstruct fallback clause _)
      (BodyCall.Graded.Compact.step_link construct callbackConstruct fallback clause _)
      (BodyCall.Graded.Compact.step_erases construct callbackConstruct fallback clause _)

theorem advance_erases (fuel : Nat) (value : Packet construct callbackConstruct fallback clause) :
    ((Cursor.advance (BodyCallWeighted.provider construct callbackConstruct fallback clause) BodyCallProtocol.client
        (requestCharge construct callbackConstruct fallback clause) fuel value).1,
      (erase construct callbackConstruct fallback clause).outcome BodyCallProtocol.client
        (Cursor.advance (BodyCallWeighted.provider construct callbackConstruct fallback clause) BodyCallProtocol.client
          (requestCharge construct callbackConstruct fallback clause) fuel value).2) =
      Cursor.advance (provider construct callbackConstruct fallback clause) BodyCallProtocol.client
        (fun _ _ => 1) fuel ((erase construct callbackConstruct fallback clause).packet BodyCallProtocol.client value) :=
  (erase construct callbackConstruct fallback clause).advance_account BodyCallProtocol.client
    (requestCharge construct callbackConstruct fallback clause) (fun _ _ => 1) (fun _ _ => rfl) fuel value

theorem resume_erases (fuel : Nat) (previous : Nat × Outcome construct callbackConstruct fallback clause) :
    ((BodyCallWeighted.resume construct callbackConstruct fallback clause fuel previous).1,
      (erase construct callbackConstruct fallback clause).outcome BodyCallProtocol.client
        (BodyCallWeighted.resume construct callbackConstruct fallback clause fuel previous).2) =
      Cursor.resume (provider construct callbackConstruct fallback clause) BodyCallProtocol.client
        (fun _ _ => 1) fuel (previous.1,
          (erase construct callbackConstruct fallback clause).outcome BodyCallProtocol.client previous.2) :=
  (erase construct callbackConstruct fallback clause).resume_account BodyCallProtocol.client
    (requestCharge construct callbackConstruct fallback clause) (fun _ _ => 1) (fun _ _ => rfl) fuel previous

theorem returned_loan_erases (returned : Returned construct callbackConstruct fallback clause) :
    ((erase construct callbackConstruct fallback clause).finished returned).2.2.val.loan =
        returned.2.2.val.val.loan ∧
      denote ((erase construct callbackConstruct fallback clause).finished returned).2.2.val.loan =
        BodyCall.Graded.loanWeight returned.2.2.val.val := ⟨rfl, rfl⟩

#print axioms advance_erases
#print axioms resume_erases
#print axioms returned_loan_erases

namespace Attachment

variable (selection : BodyCall.Graded.Activation Input Output →
  Option (WeighClause Weight (BodyCall.Graded.Activation Input Output)))

def erase : Cursor.Hom
    (Compact.provider construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection))
    (providerWith construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.values selection)) where
  map state := ⟨BodyCall.Graded.Compact.Attachment.erase selection state.val, state.property⟩
  step state _request :=
    packed_ext
      ((BodyCall.Graded.Compact.step construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.valuation selection) state.val).1,
        BodyCall.Graded.Compact.Attachment.erase selection
          (BodyCall.Graded.Compact.step construct callbackConstruct fallback
            (BodyCall.Graded.Compact.Attachment.valuation selection) state.val).2)
      _ (BodyCall.Graded.Compact.step_link construct callbackConstruct fallback _ state.val)
      (BodyCall.Graded.Compact.stepWith_link construct callbackConstruct fallback _ _)
      (BodyCall.Graded.Compact.Attachment.step_erases construct callbackConstruct fallback selection state.val)

/-- Compose the existing compact erasure with optional attachment selection.
The result runs one actual source provider, with no failed-history storage. -/
def fromSource :=
  (Compact.erase construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)).comp
    (erase construct callbackConstruct fallback selection)

abbrev SparseProvider := providerWith construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.values selection)
abbrev SourceOutcome := Outcome construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)

theorem advance_erases (fuel : Nat)
    (value : Packet construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)) :
    ((Cursor.advance (BodyCallWeighted.provider construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.valuation selection)) BodyCallProtocol.client
        (requestCharge construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)) fuel value).1,
      (fromSource construct callbackConstruct fallback selection).outcome BodyCallProtocol.client
        (Cursor.advance (BodyCallWeighted.provider construct callbackConstruct fallback
          (BodyCall.Graded.Compact.Attachment.valuation selection)) BodyCallProtocol.client
          (requestCharge construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)) fuel value).2) =
      Cursor.advance (SparseProvider construct callbackConstruct fallback selection) BodyCallProtocol.client
        (fun _ _ => 1) fuel ((fromSource construct callbackConstruct fallback selection).packet BodyCallProtocol.client value) :=
  (fromSource construct callbackConstruct fallback selection).advance_account BodyCallProtocol.client
    (requestCharge construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection))
    (fun _ _ => 1) (fun _ _ => rfl) fuel value

theorem resume_erases (fuel : Nat) (previous : Nat × SourceOutcome construct callbackConstruct fallback selection) :
    ((BodyCallWeighted.resume construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.valuation selection) fuel previous).1,
      (fromSource construct callbackConstruct fallback selection).outcome BodyCallProtocol.client
        (BodyCallWeighted.resume construct callbackConstruct fallback
          (BodyCall.Graded.Compact.Attachment.valuation selection) fuel previous).2) =
      Cursor.resume (SparseProvider construct callbackConstruct fallback selection) BodyCallProtocol.client
        (fun _ _ => 1) fuel (previous.1,
          (fromSource construct callbackConstruct fallback selection).outcome BodyCallProtocol.client previous.2) :=
  (fromSource construct callbackConstruct fallback selection).resume_account BodyCallProtocol.client
    (requestCharge construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection))
    (fun _ _ => 1) (fun _ _ => rfl) fuel previous

theorem returned_source_weight
    (returned : Returned construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)) :
    denote ((fromSource construct callbackConstruct fallback selection).finished returned).2.2.val.loan =
      BodyCall.Graded.loanWeight returned.2.2.val.val ∧
      Valid ((fromSource construct callbackConstruct fallback selection).finished returned).2.2.val.loan := by
  exact ⟨BodyCall.Graded.Compact.Attachment.loan_denote selection _ returned.2.2.val.property.1,
    BodyCall.Graded.Compact.Attachment.selected_valid selection _
      (BodyCall.Graded.loan_valid _ _ returned.2.2.val.property.1)⟩

/-- Every materialized factor is selected at its actual captured activation;
absence cannot masquerade as an explicit unit annotation. -/
theorem returned_factor_has_attachment
    (returned : Returned construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection))
    (produced : Factor Nat (BodyCall.Graded.Activation Input Output) Weight)
    (present : produced ∈ ((fromSource construct callbackConstruct fallback selection).finished returned).2.2.val.loan) :
    BodyCall.Graded.Licensed produced.dependency ∧
      ∃ expression, selection produced.dependency = some expression ∧
        produced.coefficient = WeighClause.eval produced.dependency expression := by
  change produced ∈ BodyCall.Graded.Compact.Attachment.selected selection returned.2.2.val.val.loan at present
  have included := List.mem_filter.mp present
  have paid := returned.2.2.val.property.1.2.2.2.subset included.1
  have coefficient := returned.2.2.val.property.1.2.1 produced paid
  constructor
  · exact returned.2.2.val.property.2.1 produced paid
  · cases attached : selection produced.dependency with
    | none => simp [attached] at included
    | some expression =>
        exact ⟨expression, rfl, by simpa [BodyCall.Graded.Compact.Attachment.valuation,
          BodyCall.Graded.Compact.Attachment.values, WeighClause.eval, attached] using coefficient⟩

#print axioms advance_erases
#print axioms resume_erases
#print axioms returned_source_weight
#print axioms returned_factor_has_attachment

abbrev SparseOutcome := Cursor.Outcome (SparseProvider construct callbackConstruct fallback selection)
  (BodyCallProtocol.client (Item := Input) (Value := Output)) (⟨()⟩ : ULift Unit)
abbrev SparseReturned := Cursor.Finished (SparseProvider construct callbackConstruct fallback selection)
  (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit)

def forget : SparseOutcome construct callbackConstruct fallback selection →
    BodyCallProtocol.Outcome construct callbackConstruct fallback :=
  Cursor.Outcome.mapState (source := SparseProvider construct callbackConstruct fallback selection)
    (target := BodyCallProtocol.provider construct callbackConstruct fallback)
    BodyCallProtocol.client (fun state => ⟨state.val.core, state.property⟩)

theorem forget_fromSource (outcome : SourceOutcome construct callbackConstruct fallback selection) :
    forget construct callbackConstruct fallback selection
      ((fromSource construct callbackConstruct fallback selection).outcome BodyCallProtocol.client outcome) =
      eraseOutcome construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.valuation selection) outcome := by
  cases outcome <;> rfl

def openPacket (authored : List (Equation Output)) (items : List Input) (parameter : Nat) :=
  (fromSource construct callbackConstruct fallback selection).packet BodyCallProtocol.client
    (packet construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)
      (openChecked (BodyCall.Graded.Compact.Attachment.valuation selection) authored items parameter))

def run (fuel : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat) :=
  Cursor.advance (SparseProvider construct callbackConstruct fallback selection) BodyCallProtocol.client
    (fun _ _ => 1) fuel (openPacket construct callbackConstruct fallback selection authored items parameter)

theorem run_account (fuel : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat) :
    ((BodyCallWeighted.run construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.valuation selection) fuel
        (openChecked (BodyCall.Graded.Compact.Attachment.valuation selection) authored items parameter)).1,
      (fromSource construct callbackConstruct fallback selection).outcome BodyCallProtocol.client
        (BodyCallWeighted.run construct callbackConstruct fallback
          (BodyCall.Graded.Compact.Attachment.valuation selection) fuel
          (openChecked (BodyCall.Graded.Compact.Attachment.valuation selection) authored items parameter)).2) =
      run construct callbackConstruct fallback selection fuel authored items parameter :=
  advance_erases construct callbackConstruct fallback selection fuel _

/-- The sparse runtime provider keeps the independent authored answer view;
attachment presence neither guesses completion nor runs future source rows. -/
theorem run_open_source (fuel : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat) :
    BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
      (forget construct callbackConstruct fallback selection
        (run construct callbackConstruct fallback selection fuel authored items parameter).2) =
      source construct callbackConstruct authored items parameter := by
  have same := congrArg Prod.snd (run_account construct callbackConstruct fallback selection fuel authored items parameter)
  dsimp only at same
  rw [← same, forget_fromSource]
  exact BodyCallWeighted.run_open_source construct callbackConstruct fallback _ fuel authored items parameter

/-- Every actual sparse returned loan has an actual source-run witness, not
just caller-supplied coefficient evidence. The firing ordinal counts all work. -/
theorem run_done_weight (fuel : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (actual : SparseReturned construct callbackConstruct fallback selection)
    (done : (run construct callbackConstruct fallback selection fuel authored items parameter).2 = .done actual) :
    ∃ reference : Returned construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection),
      (BodyCallWeighted.run construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.valuation selection) fuel
        (openChecked (BodyCall.Graded.Compact.Attachment.valuation selection) authored items parameter)).2 = .done reference ∧
      (fromSource construct callbackConstruct fallback selection).finished reference = actual ∧
      denote actual.2.2.val.loan = BodyCall.Graded.loanWeight reference.2.2.val.val ∧
      actual.2.2.val.nextOrdinal = reference.2.2.val.val.paid.length := by
  have same := congrArg Prod.snd (run_account construct callbackConstruct fallback selection fuel authored items parameter)
  dsimp only at same
  rw [done] at same
  cases observed : (BodyCallWeighted.run construct callbackConstruct fallback
      (BodyCall.Graded.Compact.Attachment.valuation selection) fuel
      (openChecked (BodyCall.Graded.Compact.Attachment.valuation selection) authored items parameter)).2 with
  | paused held =>
      simp only [observed, Cursor.Hom.outcome, Cursor.Outcome.mapState] at same
      cases same
  | done reference =>
      have found : (fromSource construct callbackConstruct fallback selection).finished reference = actual := by
        simpa only [observed, Cursor.Hom.outcome, Cursor.Hom.finished, Cursor.Outcome.mapState, Cursor.Outcome.done.injEq] using same
      refine ⟨reference, rfl, found, ?_, ?_⟩
      · rw [← found]
        exact (returned_source_weight construct callbackConstruct fallback selection reference).1
      · rw [← found]
        rfl

#print axioms forget_fromSource
#print axioms run_account
#print axioms run_open_source
#print axioms run_done_weight

abbrev OwnedState := Retained.State (SparseProvider construct callbackConstruct fallback selection)
  (BodyCallProtocol.client (Item := Input) (Value := Output)) ⟨()⟩ (List (List Output) × Context)

def isReturn (returned : SparseReturned construct callbackConstruct fallback selection) : Bool :=
  match returned.2.1 with
  | .yield _ _ => true
  | .finish rows _ => !rows.isEmpty
  | _ => false

def terminalAfter (returned : SparseReturned construct callbackConstruct fallback selection) :
    Option (SparseReturned construct callbackConstruct fallback selection) :=
  match returned.2.1 with | .yield _ _ => none | _ => some returned

def rearm (returned : SparseReturned construct callbackConstruct fallback selection) :
    Cursor.Packet (SparseProvider construct callbackConstruct fallback selection)
      (BodyCallProtocol.client (Item := Input) (Value := Output)) (⟨()⟩ : ULift Unit) :=
  ⟨returned.1, ⟨.advance returned.2.2.val.core, returned.2.2.property⟩, returned.2.2⟩

def consume (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (context : List (List Output) × Context) (returned : SparseReturned construct callbackConstruct fallback selection) :=
  let decision := accept context.2 returned
  (decision.1, (if decision.1 then context.1 ++ returned.2.1.rows else context.1, decision.2))

/-- The same retained adapter executes the sparse provider directly. Its
saved computation contains live lineages and a counter, with no paid history. -/
def ownedProvider (quantum : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context) :=
  Retained.provider (SparseProvider construct callbackConstruct fallback selection) BodyCallProtocol.client ⟨()⟩
    (fun _ _ => 1) quantum (isReturn construct callbackConstruct fallback selection)
    (rearm construct callbackConstruct fallback selection) (consume construct callbackConstruct fallback selection accept)

def ownedOpen (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    OwnedState construct callbackConstruct fallback selection (Context := Context) :=
  ⟨(0, .paused (openPacket construct callbackConstruct fallback selection authored items parameter)), ([], context)⟩

theorem refusal_keeps_source (quantum : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (state : OwnedState construct callbackConstruct fallback selection)
    (item returned : SparseReturned construct callbackConstruct fallback selection)
    (ready : state.computation.2 = .done returned)
    (produced : isReturn construct callbackConstruct fallback selection returned = true)
    (refused : (accept state.context.2 returned).1 = false) :
    ((ownedProvider construct callbackConstruct fallback selection quantum accept).step
      (base := ()) (index := ()) state (.accept item)).2 =
      ⟨state.computation, (state.context.1, (accept state.context.2 returned).2)⟩ := by
  simp [ownedProvider, Retained.provider, ready, produced, consume, refused]

theorem acceptance_keeps_source (quantum : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (state : OwnedState construct callbackConstruct fallback selection)
    (item returned : SparseReturned construct callbackConstruct fallback selection)
    (ready : state.computation.2 = .done returned)
    (produced : isReturn construct callbackConstruct fallback selection returned = true)
    (accepted : (accept state.context.2 returned).1 = true) :
    ((ownedProvider construct callbackConstruct fallback selection quantum accept).step
      (base := ()) (index := ()) state (.accept item)).2 =
      ⟨(state.computation.1, .paused (rearm construct callbackConstruct fallback selection returned)),
        (state.context.1 ++ returned.2.1.rows, (accept state.context.2 returned).2)⟩ := by
  simp [ownedProvider, Retained.provider, ready, produced, consume, accepted]

#print axioms refusal_keeps_source
#print axioms acceptance_keeps_source

set_option backward.isDefEq.respectTransparency false in
def forgetHom : Cursor.Hom (SparseProvider construct callbackConstruct fallback selection)
    (BodyCallProtocol.provider construct callbackConstruct fallback) where
  map state := ⟨state.val.core, state.property⟩
  step state _request := by
    change (⟨(BodyCall.Graded.Compact.stepWith construct callbackConstruct fallback
      (BodyCall.Graded.Compact.Attachment.values selection) state.val).1,
      ⟨(BodyCall.Graded.Compact.stepWith construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.values selection) state.val).2.core, _⟩⟩ :
        Σ moved : BodyCall.Move Input Output, { core : BodyCall.State Input Output // core.phase = moved.next.phase }) =
      ⟨BodyCall.step construct callbackConstruct fallback state.val.core,
        ⟨(BodyCall.step construct callbackConstruct fallback state.val.core).next, rfl⟩⟩
    calc
      _ = ⟨(BodyCall.Graded.Compact.stepWith construct callbackConstruct fallback
          (BodyCall.Graded.Compact.Attachment.values selection) state.val).1,
          ⟨(BodyCall.Graded.Compact.stepWith construct callbackConstruct fallback
            (BodyCall.Graded.Compact.Attachment.values selection) state.val).1.next, rfl⟩⟩ := by
        apply congrArg (Sigma.mk _)
        exact Subtype.ext (BodyCall.Graded.Compact.stepWith_link construct callbackConstruct fallback _ _)
      _ = _ := congrArg (fun moved : BodyCall.Move Input Output =>
        (⟨moved, ⟨moved.next, rfl⟩⟩ : Σ moved : BodyCall.Move Input Output,
          { core : BodyCall.State Input Output // core.phase = moved.next.phase }))
          (BodyCall.Graded.Compact.stepWith_move construct callbackConstruct fallback _ _)

theorem resume_forget (quantum : Nat) (previous : Nat × SparseOutcome construct callbackConstruct fallback selection) :
    forget construct callbackConstruct fallback selection
      (Cursor.resume (SparseProvider construct callbackConstruct fallback selection) BodyCallProtocol.client
        (fun _ _ => 1) quantum previous).2 =
      (BodyCallProtocol.resume construct callbackConstruct fallback quantum
        (previous.1, forget construct callbackConstruct fallback selection previous.2)).2 :=
  congrArg Prod.snd ((forgetHom construct callbackConstruct fallback selection).resume_account
    BodyCallProtocol.client (fun _ _ => 1) (BodyCallProtocol.requestCharge construct callbackConstruct fallback)
    (fun _ _ => rfl) quantum previous)

def sound (state : OwnedState construct callbackConstruct fallback selection (Context := Context)) : Prop :=
  BodyCallProtocol.sourceSound construct callbackConstruct fallback
    (forget construct callbackConstruct fallback selection state.computation.2)

def quiet (state : OwnedState construct callbackConstruct fallback selection (Context := Context)) : Prop :=
  BodyCallProtocol.finishedQuiet construct callbackConstruct
    (BodyCallProtocol.stateView construct callbackConstruct fallback
      (forget construct callbackConstruct fallback selection state.computation.2))

def view (state : OwnedState construct callbackConstruct fallback selection (Context := Context)) : List (List Output) :=
  state.context.1 ++ BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
    (forget construct callbackConstruct fallback selection state.computation.2)

theorem owned_step_view (quantum : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (state : OwnedState construct callbackConstruct fallback selection)
    (request : Request (SparseReturned construct callbackConstruct fallback selection))
    (safe : sound construct callbackConstruct fallback selection state) :
    sound construct callbackConstruct fallback selection
        ((ownedProvider construct callbackConstruct fallback selection quantum accept).step
          (base := ()) (index := ()) state request).2 ∧
      view construct callbackConstruct fallback selection
        ((ownedProvider construct callbackConstruct fallback selection quantum accept).step
          (base := ()) (index := ()) state request).2 = view construct callbackConstruct fallback selection state := by
  cases request with
  | next =>
      dsimp only [ownedProvider]
      rw [Retained.next_retains_outcome]
      have kept := BodyCallProtocol.resume_source_view construct callbackConstruct fallback quantum
        (state.computation.1, forget construct callbackConstruct fallback selection state.computation.2) safe
      constructor
      · simpa only [sound, ← resume_forget] using kept.2
      · simpa only [view, ← resume_forget] using congrArg (state.context.1 ++ ·) kept.1
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet =>
          simp only [ownedProvider, Retained.provider, ready]
          exact ⟨safe, True.intro⟩
      | done returned =>
          cases produced : isReturn construct callbackConstruct fallback selection returned with
          | false =>
              simp only [ownedProvider, Retained.provider, ready, produced, Bool.false_eq_true, ↓reduceIte]
              exact ⟨safe, True.intro⟩
          | true =>
              cases decision : (accept state.context.2 returned).1 with
              | false =>
                  simp only [ownedProvider, Retained.provider, ready, produced, consume, decision, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨safe, rfl⟩
              | true =>
                  have readings := safe.2
                  simp only [ready, forget, Cursor.Outcome.mapState, BodyCallProtocol.stateView] at readings
                  simp only [ownedProvider, Retained.provider, ready, produced, consume, decision, ↓reduceIte]
                  constructor
                  · exact ⟨rfl, readings⟩
                  · simp [view, BodyCallProtocol.unacceptedRows, ready, rearm, forget, Cursor.Outcome.mapState,
                      BodyCallProtocol.moveView, BodyCallProtocol.stateView, BodyCall.Move.rows, BodyCall.Move.next,
                      List.append_assoc]

theorem owned_step_quiet (quantum : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (state : OwnedState construct callbackConstruct fallback selection)
    (request : Request (SparseReturned construct callbackConstruct fallback selection))
    (safe : quiet construct callbackConstruct fallback selection state) :
    quiet construct callbackConstruct fallback selection
      ((ownedProvider construct callbackConstruct fallback selection quantum accept).step
        (base := ()) (index := ()) state request).2 := by
  cases request with
  | next =>
      dsimp only [ownedProvider]
      rw [Retained.next_retains_outcome]
      have kept := BodyCallProtocol.resume_finishedQuiet construct callbackConstruct fallback quantum
        (state.computation.1, forget construct callbackConstruct fallback selection state.computation.2) safe
      simpa only [quiet, ← resume_forget] using kept
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet => simpa [ownedProvider, Retained.provider, ready] using safe
      | done returned =>
          cases produced : isReturn construct callbackConstruct fallback selection returned <;>
            cases accepted : (accept state.context.2 returned).1 <;>
            simpa [quiet, ownedProvider, Retained.provider, ready, produced, consume, accepted, rearm,
              forget, Cursor.Outcome.mapState, BodyCallProtocol.stateView, BodyCall.Move.next] using safe

abbrev Call := Nat × (Result (SparseReturned construct callbackConstruct fallback selection)
  (SparseReturned construct callbackConstruct fallback selection) ×
    OwnedState construct callbackConstruct fallback selection (Context := Context))

def openCall (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    Call construct callbackConstruct fallback selection (Context := Context) :=
  (0, ⟨none, none, 0⟩, ownedOpen construct callbackConstruct fallback selection authored items parameter context)

def resumeCallSource (quantum allowance : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (previous : Call construct callbackConstruct fallback selection (Context := Context)) :=
  resumeCall (ownedProvider construct callbackConstruct fallback selection quantum accept) (fun _ _ => 1)
    allowance previous (terminalAfter construct callbackConstruct fallback selection)

def Captured (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context)) : Prop :=
  sound construct callbackConstruct fallback selection call.2.2 ∧
    quiet construct callbackConstruct fallback selection call.2.2 ∧
    view construct callbackConstruct fallback selection call.2.2 = source construct callbackConstruct authored items parameter

theorem open_captured (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    Captured construct callbackConstruct fallback selection authored items parameter
      (openCall construct callbackConstruct fallback selection authored items parameter context) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rfl
    · change BodyCall.sourceReadings (BodyCall.openState authored items parameter (.observe .noAnswers)).work
      simp [BodyCall.openState, BodyCall.sourceReadings_cons, BodyCall.Cursor.sourceReading, openFrontier]
  · change BodyCall.Phase.running = .finished → _
    intro impossible
    cases impossible
  · exact BodyCall.openState_rows construct callbackConstruct authored items parameter

theorem resume_captured (quantum allowance : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (previous : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Captured construct callbackConstruct fallback selection authored items parameter previous) :
    Captured construct callbackConstruct fallback selection authored items parameter
      (resumeCallSource construct callbackConstruct fallback selection quantum allowance accept previous) := by
  unfold resumeCallSource resumeCall
  cases previous.2.1.terminal with
  | some reason => exact safe
  | none =>
      refine fromCallbacks_invariant (ownedProvider construct callbackConstruct fallback selection quantum accept) (fun _ _ => 1)
        (fun (state : OwnedState construct callbackConstruct fallback selection (Context := Context)) => sound construct callbackConstruct fallback selection state ∧
          quiet construct callbackConstruct fallback selection state ∧
          view construct callbackConstruct fallback selection state = source construct callbackConstruct authored items parameter)
        ?_ allowance previous.2.1.accepted previous.2.1.pending previous.2.2 safe _
      intro state request invariant
      have kept := owned_step_view construct callbackConstruct fallback selection quantum accept state request invariant.1
      exact ⟨kept.1, owned_step_quiet construct callbackConstruct fallback selection quantum accept state request invariant.2.1,
        kept.2.trans invariant.2.2⟩

abbrev Grant := Nat × Nat × (Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)

def schedule (grants : List (Grant construct callbackConstruct fallback selection (Context := Context)))
    (initial : Call construct callbackConstruct fallback selection (Context := Context)) :=
  grants.foldl (fun previous grant => resumeCallSource construct callbackConstruct fallback selection
    grant.1 grant.2.1 grant.2.2 previous) initial

theorem schedule_captured (grants : List (Grant construct callbackConstruct fallback selection (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (initial : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Captured construct callbackConstruct fallback selection authored items parameter initial) :
    Captured construct callbackConstruct fallback selection authored items parameter
      (schedule construct callbackConstruct fallback selection grants initial) := by
  induction grants generalizing initial with
  | nil => exact safe
  | cons grant rest ih =>
      exact ih _ (resume_captured construct callbackConstruct fallback selection grant.1 grant.2.1 grant.2.2
        authored items parameter initial safe)

def eraseCall (call : Call construct callbackConstruct fallback selection (Context := Context)) :
    BodyCallAdmission.Call construct callbackConstruct fallback (Context := Context) :=
  (call.1, ⟨⟨call.2.1.terminal.map ((forgetHom construct callbackConstruct fallback selection).finished
      (Return := fun _ _ => BodyCall.Move Input Output)),
    call.2.1.pending.map ((forgetHom construct callbackConstruct fallback selection).finished
      (Return := fun _ _ => BodyCall.Move Input Output)), call.2.1.accepted⟩,
    ⟨(call.2.2.computation.1, forget construct callbackConstruct fallback selection call.2.2.computation.2), call.2.2.context⟩⟩)

def complete (call : Call construct callbackConstruct fallback selection (Context := Context)) : Bool :=
  BodyCallAdmission.complete construct callbackConstruct fallback (eraseCall construct callbackConstruct fallback selection call)

theorem completed_source (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Captured construct callbackConstruct fallback selection authored items parameter call)
    (finished : complete construct callbackConstruct fallback selection call = true) :
    call.2.2.context.1 = source construct callbackConstruct authored items parameter := by
  have erased := BodyCallAdmission.completed_view construct callbackConstruct fallback
    (eraseCall construct callbackConstruct fallback selection call) safe.2.1 finished
  exact erased.symm.trans safe.2.2

def admit (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Captured construct callbackConstruct fallback selection authored items parameter call) :
    Option (List (List Output)) × Call construct callbackConstruct fallback selection (Context := Context) :=
  ((BodyCallAdmission.admit construct callbackConstruct fallback requested interface authored items parameter
    (eraseCall construct callbackConstruct fallback selection call) safe.2.1).1, call)

theorem mode_license (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Captured construct callbackConstruct fallback selection authored items parameter call)
    (answers : List (List Output))
    (admitted : (admit construct callbackConstruct fallback selection requested interface authored items parameter call safe).1 = some answers) :
    answers = source construct callbackConstruct authored items parameter ∧ ConventionAllows requested answers.length :=
  BodyCallAdmission.admit_license construct callbackConstruct fallback requested interface authored items parameter
    (eraseCall construct callbackConstruct fallback selection call) safe.2.1 safe.2.2 answers admitted

#print axioms resume_forget
#print axioms owned_step_view
#print axioms owned_step_quiet
#print axioms open_captured
#print axioms resume_captured
#print axioms schedule_captured
#print axioms completed_source
#print axioms mode_license

/-- A proof-only witness in the established all-attached source. The sparse
runtime state stores no witness, paid ledger or previous computation. -/
def Origin (outcome : SparseOutcome construct callbackConstruct fallback selection) : Prop :=
  ∃ reference : SourceOutcome construct callbackConstruct fallback selection,
    (fromSource construct callbackConstruct fallback selection).outcome BodyCallProtocol.client reference = outcome

def LoanOrigin (loan : SparseReturned construct callbackConstruct fallback selection) : Prop :=
  ∃ reference : Returned construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection),
    (fromSource construct callbackConstruct fallback selection).finished reference = loan

theorem open_origin (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    Origin construct callbackConstruct fallback selection
      (openCall construct callbackConstruct fallback selection authored items parameter context).2.2.computation.2 :=
  ⟨.paused (packet construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)
    (openChecked (BodyCall.Graded.Compact.Attachment.valuation selection) authored items parameter)), rfl⟩

theorem source_resume_origin (quantum : Nat) (previous : Nat × SparseOutcome construct callbackConstruct fallback selection)
    (origin : Origin construct callbackConstruct fallback selection previous.2) :
    Origin construct callbackConstruct fallback selection
      (Cursor.resume (SparseProvider construct callbackConstruct fallback selection) BodyCallProtocol.client
        (fun _ _ => 1) quantum previous).2 := by
  obtain ⟨reference, same⟩ := origin
  refine ⟨(BodyCallWeighted.resume construct callbackConstruct fallback
    (BodyCall.Graded.Compact.Attachment.valuation selection) quantum (previous.1, reference)).2, ?_⟩
  have projected := congrArg Prod.snd (resume_erases construct callbackConstruct fallback selection quantum (previous.1, reference))
  dsimp only at projected
  simpa only [same] using projected

theorem owned_step_origin (quantum : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (state : OwnedState construct callbackConstruct fallback selection)
    (request : Request (SparseReturned construct callbackConstruct fallback selection))
    (origin : Origin construct callbackConstruct fallback selection state.computation.2) :
    Origin construct callbackConstruct fallback selection
      ((ownedProvider construct callbackConstruct fallback selection quantum accept).step
        (base := ()) (index := ()) state request).2.computation.2 := by
  cases request with
  | next =>
      dsimp only [ownedProvider]
      rw [Retained.next_retains_outcome]
      exact source_resume_origin construct callbackConstruct fallback selection quantum state.computation origin
  | accept item =>
      cases ready : state.computation.2 with
      | paused held => simpa [ownedProvider, Retained.provider, ready] using origin
      | done returned =>
          cases produced : isReturn construct callbackConstruct fallback selection returned with
          | false => simpa [ownedProvider, Retained.provider, ready, produced] using origin
          | true =>
              cases accepted : (accept state.context.2 returned).1 with
              | false => simpa [ownedProvider, Retained.provider, ready, produced, consume, accepted] using origin
              | true =>
                  obtain ⟨reference, same⟩ := origin
                  rw [ready] at same
                  cases reference with
                  | paused held => cases same
                  | done reference =>
                      have found : (fromSource construct callbackConstruct fallback selection).finished reference = returned := by
                        simpa only [Cursor.Hom.outcome, Cursor.Hom.finished, Cursor.Outcome.mapState, Cursor.Outcome.done.injEq] using same
                      simp only [ownedProvider, Retained.provider, ready, produced, consume, accepted, ↓reduceIte]
                      refine ⟨.paused ⟨reference.1,
                        ⟨.advance reference.2.2.val.val.core, reference.2.2.property⟩, reference.2.2⟩, ?_⟩
                      rw [← found]
                      rfl

theorem resume_origin (quantum allowance : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (previous : Call construct callbackConstruct fallback selection (Context := Context))
    (origin : Origin construct callbackConstruct fallback selection previous.2.2.computation.2) :
    Origin construct callbackConstruct fallback selection
      (resumeCallSource construct callbackConstruct fallback selection quantum allowance accept previous).2.2.computation.2 := by
  unfold resumeCallSource resumeCall
  cases previous.2.1.terminal with
  | some reason => exact origin
  | none =>
      exact fromCallbacks_invariant (ownedProvider construct callbackConstruct fallback selection quantum accept)
        (fun _ _ => 1) (fun state => Origin construct callbackConstruct fallback selection state.computation.2)
        (owned_step_origin construct callbackConstruct fallback selection quantum accept)
        allowance previous.2.1.accepted previous.2.1.pending previous.2.2 origin _

theorem held_loan_origin (state : OwnedState construct callbackConstruct fallback selection (Context := Context))
    (loan : SparseReturned construct callbackConstruct fallback selection)
    (origin : Origin construct callbackConstruct fallback selection state.computation.2)
    (held : state.computation.2 = .done loan) : LoanOrigin construct callbackConstruct fallback selection loan := by
  obtain ⟨reference, same⟩ := origin
  rw [held] at same
  cases reference with
  | paused saved => cases same
  | done reference =>
      exact ⟨reference, by simpa only [Cursor.Hom.outcome, Cursor.Hom.finished, Cursor.Outcome.mapState,
        Cursor.Outcome.done.injEq] using same⟩

theorem origin_loan_valid (loan : SparseReturned construct callbackConstruct fallback selection)
    (origin : LoanOrigin construct callbackConstruct fallback selection loan) : Valid loan.2.2.val.loan := by
  obtain ⟨reference, same⟩ := origin
  rw [← same]
  exact (returned_source_weight construct callbackConstruct fallback selection reference).2

#print axioms open_origin
#print axioms source_resume_origin
#print axioms owned_step_origin
#print axioms resume_origin
#print axioms held_loan_origin
#print axioms origin_loan_valid

end Attachment

end Compact

namespace Owned

abbrev State := Retained.State (provider construct callbackConstruct fallback clause)
  (BodyCallProtocol.client (Item := Input) (Value := Output)) ⟨()⟩ (List (List Output) × Context)

def isReturn (returned : Returned construct callbackConstruct fallback clause) : Bool :=
  match returned.2.1 with
  | .yield _ _ => true
  | .finish rows _ => !rows.isEmpty
  | _ => false

def terminalAfter (returned : Returned construct callbackConstruct fallback clause) :
    Option (Returned construct callbackConstruct fallback clause) :=
  match returned.2.1 with | .yield _ _ => none | _ => some returned

def rearm (returned : Returned construct callbackConstruct fallback clause) :=
  packet construct callbackConstruct fallback clause returned.2.2.val

def consume (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (context : List (List Output) × Context) (returned : Returned construct callbackConstruct fallback clause) :=
  let decision := accept context.2 returned
  (decision.1, (if decision.1 then context.1 ++ returned.2.1.rows else context.1, decision.2))

def provider (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context) :=
  Retained.provider (BodyCallWeighted.provider construct callbackConstruct fallback clause)
    BodyCallProtocol.client ⟨()⟩ (requestCharge construct callbackConstruct fallback clause) quantum
    (isReturn construct callbackConstruct fallback clause) (rearm construct callbackConstruct fallback clause)
    (consume construct callbackConstruct fallback clause accept)

def sound (state : State construct callbackConstruct fallback clause (Context := Context)) :=
  BodyCallProtocol.sourceSound construct callbackConstruct fallback
    (eraseOutcome construct callbackConstruct fallback clause state.computation.2)

def view (state : State construct callbackConstruct fallback clause (Context := Context)) :=
  state.context.1 ++ BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
    (eraseOutcome construct callbackConstruct fallback clause state.computation.2)

private theorem resume_source (quantum : Nat)
    (state : State construct callbackConstruct fallback clause (Context := Context))
    (safe : sound construct callbackConstruct fallback clause state) :
    let next := BodyCallWeighted.resume construct callbackConstruct fallback clause quantum state.computation
    BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
        (eraseOutcome construct callbackConstruct fallback clause next.2) =
      BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
        (eraseOutcome construct callbackConstruct fallback clause state.computation.2) ∧
      BodyCallProtocol.sourceSound construct callbackConstruct fallback
        (eraseOutcome construct callbackConstruct fallback clause next.2) := by
  have same := congrArg Prod.snd (resume_projection construct callbackConstruct fallback clause quantum state.computation)
  dsimp only at same
  dsimp only
  rw [same]
  exact BodyCallProtocol.resume_source_view construct callbackConstruct fallback quantum _ safe

theorem step_preserves_view (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (state : State construct callbackConstruct fallback clause)
    (request : Request (Returned construct callbackConstruct fallback clause))
    (safe : sound construct callbackConstruct fallback clause state) :
    sound construct callbackConstruct fallback clause
        ((provider construct callbackConstruct fallback clause quantum accept).step
          (base := ()) (index := ()) state request).2 ∧
      view construct callbackConstruct fallback clause
        ((provider construct callbackConstruct fallback clause quantum accept).step
          (base := ()) (index := ()) state request).2 =
        view construct callbackConstruct fallback clause state := by
  cases request with
  | next =>
      dsimp only [provider]
      rw [Retained.next_retains_outcome]
      have kept := resume_source construct callbackConstruct fallback clause quantum state safe
      exact ⟨kept.2, congrArg (state.context.1 ++ ·) kept.1⟩
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet =>
          simp only [provider, Retained.provider, ready]
          exact ⟨safe, True.intro⟩
      | done returned =>
          cases produced : isReturn construct callbackConstruct fallback clause returned with
          | false =>
              simp only [provider, Retained.provider, ready, produced, Bool.false_eq_true, ↓reduceIte]
              exact ⟨safe, True.intro⟩
          | true =>
              cases decision : (accept state.context.2 returned).1 with
              | false =>
                  simp only [provider, Retained.provider, ready, produced, consume,
                    decision, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨safe, rfl⟩
              | true =>
                  have readings := safe.2
                  simp only [ready, eraseOutcome, erase, Cursor.Hom.outcome, Cursor.Outcome.mapState,
                    BodyCallProtocol.stateView] at readings
                  simp only [provider, Retained.provider, ready, produced, consume, decision, ↓reduceIte]
                  constructor
                  · exact ⟨rfl, readings⟩
                  · simp [view, BodyCallProtocol.unacceptedRows, ready, rearm, packet,
                      eraseOutcome, erase, Cursor.Hom.outcome, Cursor.Outcome.mapState,
                      BodyCallProtocol.moveView, BodyCallProtocol.stateView, BodyCall.Move.rows, BodyCall.Move.next,
                      List.append_assoc]

/-- Stateful consumer refusals preserve the real captured source view. The
callback owns the same typed, source-valued loan until acknowledgment. -/
theorem call_preserves_view (quantum allowance accepted : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (pending : Option (Returned construct callbackConstruct fallback clause))
    (state : State construct callbackConstruct fallback clause)
    (safe : sound construct callbackConstruct fallback clause state)
    (charge : Cursor.Charge (provider construct callbackConstruct fallback clause quantum accept)) :
    let actual := fromCallbacks (provider construct callbackConstruct fallback clause quantum accept) charge
      allowance pending accepted state (terminalAfter construct callbackConstruct fallback clause)
    sound construct callbackConstruct fallback clause actual.2.2 ∧
      view construct callbackConstruct fallback clause actual.2.2 =
        view construct callbackConstruct fallback clause state := by
  refine fromCallbacks_invariant (provider construct callbackConstruct fallback clause quantum accept) charge
    (fun next => sound construct callbackConstruct fallback clause next ∧
      view construct callbackConstruct fallback clause next = view construct callbackConstruct fallback clause state)
    ?_ allowance accepted pending state ⟨safe, rfl⟩ (terminalAfter construct callbackConstruct fallback clause)
  intro next request invariant
  have kept := step_preserves_view construct callbackConstruct fallback clause quantum accept next request invariant.1
  exact ⟨kept.1, kept.2.trans invariant.2⟩

def openState (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    State construct callbackConstruct fallback clause (Context := Context) :=
  ⟨(0, .paused (packet construct callbackConstruct fallback clause (openChecked clause authored items parameter))),
    ([], context)⟩

theorem call_open_source (quantum allowance accepted : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (charge : Cursor.Charge (provider construct callbackConstruct fallback clause quantum accept)) :
    view construct callbackConstruct fallback clause
      (fromCallbacks (provider construct callbackConstruct fallback clause quantum accept) charge
        allowance none accepted (openState construct callbackConstruct fallback clause authored items parameter context)
        (terminalAfter construct callbackConstruct fallback clause)).2.2 =
      source construct callbackConstruct authored items parameter := by
  have kept := call_preserves_view construct callbackConstruct fallback clause quantum allowance accepted accept none
    (openState construct callbackConstruct fallback clause authored items parameter context)
    (by
      constructor
      · rfl
      · simp [openState, eraseOutcome, erase, Cursor.Hom.outcome, Cursor.Outcome.mapState, packet, openChecked,
          BodyCallProtocol.stateView, BodyCall.Graded.openState, BodyCall.openState,
          BodyCall.sourceReadings_cons, BodyCall.Cursor.sourceReading, openFrontier]) charge
  exact kept.2.trans (BodyCall.openState_rows construct callbackConstruct authored items parameter)

def quiet (state : State construct callbackConstruct fallback clause (Context := Context)) :=
  BodyCallProtocol.finishedQuiet construct callbackConstruct
    (BodyCallProtocol.stateView construct callbackConstruct fallback
      (eraseOutcome construct callbackConstruct fallback clause state.computation.2))

private theorem step_quiet (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (state : State construct callbackConstruct fallback clause)
    (request : Request (Returned construct callbackConstruct fallback clause))
    (initial : quiet construct callbackConstruct fallback clause state) :
    quiet construct callbackConstruct fallback clause
      ((provider construct callbackConstruct fallback clause quantum accept).step
        (base := ()) (index := ()) state request).2 := by
  cases request with
  | next =>
      dsimp only [provider]
      rw [Retained.next_retains_outcome]
      have same := congrArg Prod.snd (resume_projection construct callbackConstruct fallback clause quantum state.computation)
      dsimp only at same
      unfold quiet
      change BodyCallProtocol.finishedQuiet construct callbackConstruct
        (BodyCallProtocol.stateView construct callbackConstruct fallback
          (eraseOutcome construct callbackConstruct fallback clause
            (BodyCallWeighted.resume construct callbackConstruct fallback clause quantum state.computation).2))
      rw [same]
      exact BodyCallProtocol.resume_finishedQuiet construct callbackConstruct fallback quantum _ initial
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet => simpa [provider, Retained.provider, ready] using initial
      | done returned =>
          cases produced : isReturn construct callbackConstruct fallback clause returned <;>
            cases accepted : (accept state.context.2 returned).1 <;>
            simpa [quiet, provider, Retained.provider, ready, produced, consume, accepted, rearm, packet,
              eraseOutcome, erase, Cursor.Hom.outcome, Cursor.Outcome.mapState,
              BodyCallProtocol.stateView, BodyCall.Move.next] using initial

theorem call_quiet (quantum allowance accepted : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (pending : Option (Returned construct callbackConstruct fallback clause))
    (state : State construct callbackConstruct fallback clause)
    (initial : quiet construct callbackConstruct fallback clause state)
    (charge : Cursor.Charge (provider construct callbackConstruct fallback clause quantum accept)) :
    quiet construct callbackConstruct fallback clause
      (fromCallbacks (provider construct callbackConstruct fallback clause quantum accept) charge
        allowance pending accepted state (terminalAfter construct callbackConstruct fallback clause)).2.2 :=
  fromCallbacks_invariant _ charge (quiet construct callbackConstruct fallback clause)
    (step_quiet construct callbackConstruct fallback clause quantum accept) allowance accepted pending state initial _

theorem open_quiet (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    quiet construct callbackConstruct fallback clause
      (openState construct callbackConstruct fallback clause authored items parameter context) := by
  simp [quiet, openState, packet, openChecked, BodyCall.Graded.openState, BodyCall.openState,
    eraseOutcome, erase, Cursor.Hom.outcome, Cursor.Outcome.mapState, BodyCallProtocol.stateView,
    BodyCallProtocol.finishedQuiet]

abbrev Call := Nat × (Result (Returned construct callbackConstruct fallback clause)
  (Returned construct callbackConstruct fallback clause) ×
    State construct callbackConstruct fallback clause (Context := Context))

def eraseCall (call : Call construct callbackConstruct fallback clause (Context := Context)) :
    BodyCallAdmission.Call construct callbackConstruct fallback (Context := Context) :=
  (call.1, ⟨⟨call.2.1.terminal.map ((erase construct callbackConstruct fallback clause).finished
      (Return := fun _ _ => BodyCall.Move Input Output)),
    call.2.1.pending.map ((erase construct callbackConstruct fallback clause).finished
      (Return := fun _ _ => BodyCall.Move Input Output)),
    call.2.1.accepted⟩,
    ⟨(call.2.2.computation.1, eraseOutcome construct callbackConstruct fallback clause call.2.2.computation.2),
      call.2.2.context⟩⟩)

def complete (call : Call construct callbackConstruct fallback clause (Context := Context)) : Bool :=
  BodyCallAdmission.complete construct callbackConstruct fallback
    (eraseCall construct callbackConstruct fallback clause call)

/-- A producer-finished, acknowledged cut has exactly the independent
source rows. The empty residual follows from the actual transition invariant. -/
theorem completed_source (quantum allowance accepted : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (charge : Cursor.Charge (provider construct callbackConstruct fallback clause quantum accept))
    (completed :
      complete construct callbackConstruct fallback clause
        (fromCallbacks (provider construct callbackConstruct fallback clause quantum accept) charge
          allowance none accepted (openState construct callbackConstruct fallback clause authored items parameter context)
          (terminalAfter construct callbackConstruct fallback clause)) = true) :
    (fromCallbacks (provider construct callbackConstruct fallback clause quantum accept) charge
      allowance none accepted (openState construct callbackConstruct fallback clause authored items parameter context)
      (terminalAfter construct callbackConstruct fallback clause)).2.2.context.1 =
        source construct callbackConstruct authored items parameter := by
  have kept := call_open_source construct callbackConstruct fallback clause quantum allowance accepted accept
    authored items parameter context charge
  have earned := call_quiet construct callbackConstruct fallback clause quantum allowance accepted accept none
    (openState construct callbackConstruct fallback clause authored items parameter context)
    (open_quiet construct callbackConstruct fallback clause authored items parameter context) charge
  have finished := BodyCallAdmission.completed_view construct callbackConstruct fallback
    (eraseCall construct callbackConstruct fallback clause _) earned completed
  exact finished.symm.trans kept

/-- Consumer refusal changes only its private context. The exact pending
source state, lineages, paid account and valued loan are retained. -/
theorem refused_retains_whole_computation (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (state : State construct callbackConstruct fallback clause) (item returned : Returned construct callbackConstruct fallback clause)
    (ready : state.computation.2 = .done returned)
    (produced : isReturn construct callbackConstruct fallback clause returned = true)
    (refused : (accept state.context.2 returned).1 = false) :
    ((provider construct callbackConstruct fallback clause quantum accept).step
      (base := ()) (index := ()) state (.accept item)).2 =
      ⟨state.computation, (state.context.1, (accept state.context.2 returned).2)⟩ := by
  simp [provider, Retained.provider, ready, produced, consume, refused]

/-- Acknowledgment rearms the same actual graded source state. It neither
creates a factor nor makes another provider request, for any source quantum. -/
theorem accepted_keeps_whole_source (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (state : State construct callbackConstruct fallback clause) (item returned : Returned construct callbackConstruct fallback clause)
    (ready : state.computation.2 = .done returned)
    (produced : isReturn construct callbackConstruct fallback clause returned = true)
    (accepted : (accept state.context.2 returned).1 = true) :
    ((provider construct callbackConstruct fallback clause quantum accept).step
      (base := ()) (index := ()) state (.accept item)).2 =
      ⟨(state.computation.1, .paused (rearm construct callbackConstruct fallback clause returned)),
        (state.context.1 ++ returned.2.1.rows, (accept state.context.2 returned).2)⟩ := by
  simp [provider, Retained.provider, ready, produced, consume, accepted]

#print axioms call_quiet
#print axioms open_quiet
#print axioms refused_retains_whole_computation
#print axioms accepted_keeps_whole_source

#print axioms step_preserves_view
#print axioms call_preserves_view
#print axioms call_open_source
#print axioms completed_source

end Owned



end BodyCallWeighted

/-! Shared weighted returns in one fixed pure captured source world. Numeric
factor identities are local to that producer instance. Cross-instance naming,
Need-world compatibility and effectful authority are separate contracts. -/
namespace BodyCallShared.Weighted

open Mettapedia.Algebra.SharedCoefficientLedger
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory

variable {Input Output Weight Context : Type} [Semiring Weight]
    (construct : Input → Output → Output) (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (selection : BodyCall.Graded.Activation Input Output → Option (WeighClause Weight (BodyCall.Graded.Activation Input Output)))

abbrev Call := BodyCallWeighted.Compact.Attachment.Call construct callbackConstruct fallback selection (Context := Context)
abbrev Loan := BodyCallWeighted.Compact.Attachment.SparseReturned construct callbackConstruct fallback selection
abbrev Borrowed := Nat × Loan construct callbackConstruct fallback selection
/-- The immutable return image stores no producer residual or IR continuation.
Its two numeric factor fields name the one-factor-per-activation source profile. -/
abbrev Stored := Nat × List (List Output) × Ledger Nat Nat Weight
abbrev Move := Cursor.ProducerOccurrenceLog.ProducerOutcome
  (Call construct callbackConstruct fallback selection (Context := Context))
  (Borrowed construct callbackConstruct fallback selection) Empty (Loan construct callbackConstruct fallback selection)

def projectLedger (ledger : Ledger Nat (BodyCall.Graded.Activation Input Output) Weight) : Ledger Nat Nat Weight :=
  ledger.map (fun produced => produced.rename id (fun _ => produced.identity))

omit [Semiring Weight] in
theorem project_identities (ledger : Ledger Nat (BodyCall.Graded.Activation Input Output) Weight) :
    identities (projectLedger ledger) = identities ledger := by
  simp [projectLedger, identities, Factor.rename, List.map_map]

theorem project_denote (ledger : Ledger Nat (BodyCall.Graded.Activation Input Output) Weight) :
    denote (projectLedger ledger) = denote ledger := by
  simp only [projectLedger, Mettapedia.Algebra.SharedCoefficientLedger.denote, List.map_map, Function.comp_def, Factor.rename]

def image (borrowed : Borrowed construct callbackConstruct fallback selection) : Stored (Output := Output) (Weight := Weight) :=
  (borrowed.1, borrowed.2.2.1.rows, projectLedger borrowed.2.2.2.val.loan)

def capture (borrowed : Borrowed construct callbackConstruct fallback selection) :
    Option (Stored (Output := Output) (Weight := Weight)) := some (image construct callbackConstruct fallback selection borrowed)

def Authentic (stored : Stored (Output := Output) (Weight := Weight)) : Prop :=
  ∃ borrowed : Borrowed construct callbackConstruct fallback selection,
    BodyCallWeighted.Compact.Attachment.LoanOrigin construct callbackConstruct fallback selection borrowed.2 ∧
      image construct callbackConstruct fallback selection borrowed = stored

theorem image_valid (borrowed : Borrowed construct callbackConstruct fallback selection)
    (origin : BodyCallWeighted.Compact.Attachment.LoanOrigin construct callbackConstruct fallback selection borrowed.2) :
    Valid (image construct callbackConstruct fallback selection borrowed).2.2 := by
  change (identities (projectLedger borrowed.2.2.2.val.loan)).Nodup
  rw [project_identities]
  exact BodyCallWeighted.Compact.Attachment.origin_loan_valid construct callbackConstruct fallback selection borrowed.2 origin

def refuse (context : Context) (_ : Loan construct callbackConstruct fallback selection) : Bool × Context := (false, context)
def accept (context : Context) (_ : Loan construct callbackConstruct fallback selection) : Bool × Context := (true, context)

def inspect (call : Call construct callbackConstruct fallback selection (Context := Context)) :
    Move construct callbackConstruct fallback selection (Context := Context) :=
  if BodyCallWeighted.Compact.Attachment.complete construct callbackConstruct fallback selection call then .completed call
  else match call.2.1.terminal with
    | some returned => match returned.2.1 with
      | .decline _ => .interrupted call
      | .handoff _ => .handoff returned call
      | _ => .yielded call
    | none => match call.2.1.pending with
      | some returned => .returned (call.2.1.accepted, returned) call
      | none => .yielded call

def Coherent (call : Call construct callbackConstruct fallback selection (Context := Context)) : Prop :=
  ∀ loan, call.2.1.pending = some loan → call.2.1.terminal = none ∧
    call.2.2.computation.2 = .done loan ∧ BodyCallWeighted.Compact.Attachment.isReturn construct callbackConstruct fallback selection loan = true

theorem inspect_next (call : Call construct callbackConstruct fallback selection (Context := Context)) :
    (inspect construct callbackConstruct fallback selection call).next = call := by
  unfold inspect
  split
  · rfl
  · cases call.2.1.terminal with
    | some returned => cases moved : returned.2.1 <;> simp [moved, Cursor.ProducerOccurrenceLog.ProducerOutcome.next]
    | none => cases call.2.1.pending <;> rfl

theorem inspect_returns (call : Call construct callbackConstruct fallback selection (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback selection call) :
    (inspect construct callbackConstruct fallback selection call).returns =
      call.2.1.pending.toList.map (fun loan => (call.2.1.accepted, loan)) := by
  cases pending : call.2.1.pending with
  | some loan =>
      have held := coherent loan pending
      simp [inspect, BodyCallWeighted.Compact.Attachment.complete, BodyCallAdmission.complete, BodyCallWeighted.Compact.Attachment.eraseCall, pending, held.1,
        Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]
  | none =>
      unfold inspect
      split
      · rfl
      · cases terminal : call.2.1.terminal with
        | none => simp [pending, Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]
        | some returned => cases moved : returned.2.1 <;> simp [moved, Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]

theorem poll_shape (quantum : Nat) (call : Call construct callbackConstruct fallback selection (Context := Context))
    (running : call.2.1.terminal = none) (empty : call.2.1.pending = none) :
    let later := BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selection quantum 1
      (refuse construct callbackConstruct fallback selection) call
    later.2.2.context = call.2.2.context ∧ later.2.1.accepted = call.2.1.accepted ∧
      Coherent construct callbackConstruct fallback selection later := by
  cases outcome : (Cursor.resume (BodyCallWeighted.Compact.Attachment.SparseProvider construct callbackConstruct fallback selection)
      BodyCallProtocol.client (fun _ _ => 1) quantum call.2.2.computation).2 with
  | paused saved =>
      simp [BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall, running, empty, fromCallbacks,
        BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider, outcome, Coherent]
  | done returned =>
      cases produced : BodyCallWeighted.Compact.Attachment.isReturn construct callbackConstruct fallback selection returned <;>
        simp [BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall, running, empty, fromCallbacks,
          BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider, outcome, produced, BodyCallWeighted.Compact.Attachment.consume, refuse, Coherent]

theorem acknowledge_shape (call : Call construct callbackConstruct fallback selection (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback selection call)
    (loan : Loan construct callbackConstruct fallback selection) (pending : call.2.1.pending = some loan) :
    let later := BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selection 0 1
      (accept construct callbackConstruct fallback selection) call
    later.2.1.pending = none ∧ later.2.2.context.1 = call.2.2.context.1 ++ loan.2.1.rows ∧
      later.2.1.accepted = call.2.1.accepted + 1 ∧ Coherent construct callbackConstruct fallback selection later := by
  have held := coherent loan pending
  cases final : BodyCallWeighted.Compact.Attachment.terminalAfter construct callbackConstruct fallback selection loan <;>
    simp [BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall, held.1, pending, fromCallbacks,
      BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider, held.2.1, held.2.2, BodyCallWeighted.Compact.Attachment.consume, accept, final, Coherent]

variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    {size : Nat} (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]

def poll (quantum : Nat) (call : Call construct callbackConstruct fallback selection (Context := Context)) :=
  if OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) then
    if FrameUpdate point.authority required then
      BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selection quantum 1
        (refuse construct callbackConstruct fallback selection) call
    else call
  else call

def step (quantum : Nat) (call : Call construct callbackConstruct fallback selection (Context := Context)) :
    Move construct callbackConstruct fallback selection (Context := Context) :=
  BodyCallShared.retainedStep (inspect construct callbackConstruct fallback selection)
    (BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selection 0 1
      (accept construct callbackConstruct fallback selection))
    (poll construct callbackConstruct fallback selection authority before current reader point required quantum) call

def Safe (items : List Input) (parameter : Nat) (call : Call construct callbackConstruct fallback selection (Context := Context)) : Prop :=
  BodyCallWeighted.Compact.Attachment.Captured construct callbackConstruct fallback selection (OrderedDependencyStore.query before reader) items parameter call ∧
    BodyCallWeighted.Compact.Attachment.Origin construct callbackConstruct fallback selection call.2.2.computation.2 ∧
    Coherent construct callbackConstruct fallback selection call

theorem open_safe (items : List Input) (parameter : Nat) (context : Context) :
    Safe construct callbackConstruct fallback selection before reader items parameter
      (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selection (OrderedDependencyStore.query before reader) items parameter context) := by
  refine ⟨BodyCallWeighted.Compact.Attachment.open_captured construct callbackConstruct fallback selection _ items parameter context,
    BodyCallWeighted.Compact.Attachment.open_origin construct callbackConstruct fallback selection _ items parameter context, ?_⟩
  intro loan pending
  cases pending

set_option backward.isDefEq.respectTransparency false in
theorem poll_safe (quantum : Nat) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Safe construct callbackConstruct fallback selection before reader items parameter call)
    (running : call.2.1.terminal = none) (empty : call.2.1.pending = none) :
    Safe construct callbackConstruct fallback selection before reader items parameter
      (poll construct callbackConstruct fallback selection authority before current reader point required quantum call) := by
  by_cases fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true
  · by_cases allowed : FrameUpdate point.authority required
    · simpa [poll, fresh, allowed] using
        (show Safe construct callbackConstruct fallback selection before reader items parameter
          (BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selection quantum 1
            (refuse construct callbackConstruct fallback selection) call) from
          ⟨BodyCallWeighted.Compact.Attachment.resume_captured construct callbackConstruct fallback selection quantum 1
            (refuse construct callbackConstruct fallback selection) _ items parameter call safe.1,
            BodyCallWeighted.Compact.Attachment.resume_origin construct callbackConstruct fallback selection quantum 1
              (refuse construct callbackConstruct fallback selection) call safe.2.1,
            (poll_shape construct callbackConstruct fallback selection quantum call running empty).2.2⟩)
    · simpa [poll, fresh, allowed] using safe
  · simpa [poll, fresh] using safe

set_option backward.isDefEq.respectTransparency false in
theorem step_safe (quantum : Nat) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Safe construct callbackConstruct fallback selection before reader items parameter call) :
    Safe construct callbackConstruct fallback selection before reader items parameter
      (step construct callbackConstruct fallback selection authority before current reader point required quantum call).next := by
  unfold step BodyCallShared.retainedStep
  split
  · simpa only [inspect_next] using safe
  · cases pending : call.2.1.pending with
    | some loan =>
        exact ⟨BodyCallWeighted.Compact.Attachment.resume_captured construct callbackConstruct fallback selection 0 1
          (accept construct callbackConstruct fallback selection) _ items parameter call safe.1,
          BodyCallWeighted.Compact.Attachment.resume_origin construct callbackConstruct fallback selection 0 1
            (accept construct callbackConstruct fallback selection) call safe.2.1,
          (acknowledge_shape construct callbackConstruct fallback selection call safe.2.2 loan pending).2.2.2⟩
    | none =>
        simpa only [inspect_next] using poll_safe construct callbackConstruct fallback selection authority before current reader point required
          quantum items parameter call safe (by simpa using ‹¬call.2.1.terminal.isSome = true›) pending

theorem inspect_origin (call : Call construct callbackConstruct fallback selection (Context := Context))
    (origin : BodyCallWeighted.Compact.Attachment.Origin construct callbackConstruct fallback selection call.2.2.computation.2)
    (coherent : Coherent construct callbackConstruct fallback selection call) :
    ∀ borrowed ∈ (inspect construct callbackConstruct fallback selection call).returns,
      Authentic construct callbackConstruct fallback selection (image construct callbackConstruct fallback selection borrowed) := by
  rw [inspect_returns construct callbackConstruct fallback selection call coherent]
  intro borrowed present
  obtain ⟨loan, loanMember, equal⟩ := List.mem_map.mp present
  subst borrowed
  have pending : call.2.1.pending = some loan := Option.mem_toList.mp loanMember
  exact ⟨(call.2.1.accepted, loan), BodyCallWeighted.Compact.Attachment.held_loan_origin construct callbackConstruct fallback selection
    call.2.2 loan origin (coherent loan pending).2.1, rfl⟩

theorem step_origins (quantum : Nat) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Safe construct callbackConstruct fallback selection before reader items parameter call) :
    ∀ borrowed ∈ (step construct callbackConstruct fallback selection authority before current reader point required quantum call).returns,
      Authentic construct callbackConstruct fallback selection (image construct callbackConstruct fallback selection borrowed) := by
  unfold step BodyCallShared.retainedStep
  split
  · exact inspect_origin construct callbackConstruct fallback selection call safe.2.1 safe.2.2
  · cases pending : call.2.1.pending with
    | some loan => simp [Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]
    | none =>
        have kept := poll_safe construct callbackConstruct fallback selection authority before current reader point required
          quantum items parameter call safe (by simpa using ‹¬call.2.1.terminal.isSome = true›) pending
        exact inspect_origin construct callbackConstruct fallback selection _ kept.2.1 kept.2.2

#print axioms project_identities
#print axioms project_denote
#print axioms image_valid
#print axioms open_safe
#print axioms step_safe
#print axioms step_origins



def publishedRows (call : Call construct callbackConstruct fallback selection (Context := Context)) : List (List Output) :=
  call.2.2.context.1 ++ call.2.1.pending.toList.flatMap (fun loan => loan.2.1.rows)

def residualRows (call : Call construct callbackConstruct fallback selection (Context := Context)) : List (List Output) :=
  match call.2.1.pending with
  | some _ => BodyCall.workRows construct callbackConstruct (BodyCallProtocol.stateView construct callbackConstruct fallback
      (BodyCallWeighted.Compact.Attachment.forget construct callbackConstruct fallback selection call.2.2.computation.2)).work
  | none => BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
      (BodyCallWeighted.Compact.Attachment.forget construct callbackConstruct fallback selection call.2.2.computation.2)

theorem published_residual_eq_view (call : Call construct callbackConstruct fallback selection (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback selection call) :
    publishedRows construct callbackConstruct fallback selection call ++ residualRows construct callbackConstruct fallback selection call =
      BodyCallWeighted.Compact.Attachment.view construct callbackConstruct fallback selection call.2.2 := by
  cases pending : call.2.1.pending with
  | none => simp [publishedRows, residualRows, pending, BodyCallWeighted.Compact.Attachment.view]
  | some loan =>
      have held := coherent loan pending
      simp [publishedRows, residualRows, pending, BodyCallWeighted.Compact.Attachment.view, held.2.1,
        BodyCallWeighted.Compact.Attachment.forget, Cursor.Outcome.mapState,
        BodyCallProtocol.unacceptedRows, BodyCallProtocol.moveView, List.append_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem step_rows (quantum : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback selection call) :
    publishedRows construct callbackConstruct fallback selection
        (step construct callbackConstruct fallback selection authority before current reader point required quantum call).next =
      publishedRows construct callbackConstruct fallback selection call ++
        (step construct callbackConstruct fallback selection authority before current reader point required quantum call).returns.flatMap
          (fun borrowed => borrowed.2.2.1.rows) := by
  unfold step BodyCallShared.retainedStep
  split
  · rw [inspect_next, inspect_returns construct callbackConstruct fallback selection call coherent]
    have empty : call.2.1.pending = none := by
      cases pending : call.2.1.pending with
      | none => rfl
      | some loan =>
          have held := coherent loan pending
          simp [held.1] at ‹call.2.1.terminal.isSome = true›
    simp [empty]
  · cases pending : call.2.1.pending with
    | some loan =>
        have shape := acknowledge_shape construct callbackConstruct fallback selection call coherent loan pending
        simp [Cursor.ProducerOccurrenceLog.ProducerOutcome.next,
          Cursor.ProducerOccurrenceLog.ProducerOutcome.returns, publishedRows, shape.1, shape.2.1, pending]
    | none =>
        by_cases fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true
        · by_cases permitted : FrameUpdate point.authority required
          · simp only [poll, fresh, permitted, ↓reduceIte]
            have shape := poll_shape construct callbackConstruct fallback selection quantum call
              (by simpa using ‹¬call.2.1.terminal.isSome = true›) pending
            rw [inspect_next, inspect_returns construct callbackConstruct fallback selection _ shape.2.2]
            simp [publishedRows, shape.1, shape.2.1, pending, List.flatMap_map]
          · simp only [poll, fresh, permitted, ↓reduceIte]
            rw [inspect_next, inspect_returns construct callbackConstruct fallback selection call coherent]
            simp [pending]
        · simp only [poll, fresh, Bool.false_eq_true, ↓reduceIte]
          rw [inspect_next, inspect_returns construct callbackConstruct fallback selection call coherent]
          simp [pending]

theorem path_rows (quantum : Nat) (items : List Input) (parameter : Nat)
    {first last : Call construct callbackConstruct fallback selection (Context := Context)}
    {returns : List (Borrowed construct callbackConstruct fallback selection)}
    (path : Cursor.ProducerOccurrenceLog.ProducerPath
      (step construct callbackConstruct fallback selection authority before current reader point required quantum) first returns last)
    (safe : Safe construct callbackConstruct fallback selection before reader items parameter first) :
    publishedRows construct callbackConstruct fallback selection last =
      publishedRows construct callbackConstruct fallback selection first ++ returns.flatMap (fun loan => loan.2.2.1.rows) := by
  induction path with
  | refl => simp
  | @next first move later returns transition tail ih =>
      have kept := step_safe construct callbackConstruct fallback selection authority before current reader
        point required quantum items parameter first safe
      have row := step_rows construct callbackConstruct fallback selection authority before current reader point required
        quantum first safe.2.2
      rw [transition] at kept row
      rw [ih kept, row, List.flatMap_append, List.append_assoc]

abbrev Configuration (Owner : Type) (clients : Nat) :=
  Cursor.ProducerOccurrenceLog.Configuration
    (Call construct callbackConstruct fallback selection (Context := Context))
    (Borrowed construct callbackConstruct fallback selection)
    (Stored (Output := Output) (Weight := Weight))
    (OrderedDependencyStore.Store (Equation Output) size) Owner Empty
    (Loan construct callbackConstruct fallback selection) clients

def initial (items : List Input) (parameter : Nat) (context : Context) (Owner : Type) (clients limit : Nat) :
    Configuration construct callbackConstruct fallback selection (Context := Context) (size := size) Owner clients :=
  Cursor.ProducerOccurrenceLog.initial
    (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selection
      (OrderedDependencyStore.query before reader) items parameter context) before limit

variable {Owner : Type} {clients : Nat} (quantum : Nat)
local notation "sourceStep" => step construct callbackConstruct fallback selection authority before current reader point required quantum
local notation "sourceCapture" => capture construct callbackConstruct fallback selection
local notation "Cfg" => Configuration construct callbackConstruct fallback selection (Context := Context) (size := size) Owner clients

/-- The whole saved source remains reachable. Authentication of immutable row
images is a proposition, never an extra field of a stored return. -/
def Accounted (items : List Input) (parameter : Nat) (state : Cfg) : Prop :=
  (∃ execution, state.execution = some execution ∧
    Safe construct callbackConstruct fallback selection before reader items parameter execution.producer) ∧
  (∀ stored ∈ state.delivery.log.rows, Authentic construct callbackConstruct fallback selection stored) ∧
  (∀ borrowed ∈ (Cursor.ProducerOccurrenceLog.pending state).toList,
    Authentic construct callbackConstruct fallback selection (image construct callbackConstruct fallback selection borrowed))

theorem initial_accounted (items : List Input) (parameter : Nat) (context : Context) (limit : Nat) :
    Accounted construct callbackConstruct fallback selection before reader items parameter
      (initial construct callbackConstruct fallback selection before reader items parameter context Owner clients limit) := by
  refine ⟨⟨_, rfl, open_safe construct callbackConstruct fallback selection before reader items parameter context⟩, ?_, ?_⟩
  · simp [initial, Cursor.ProducerOccurrenceLog.initial, Cursor.SharedOccurrenceLog.initial]
  · simp [initial, Cursor.ProducerOccurrenceLog.initial, Cursor.ProducerOccurrenceLog.pending]

theorem path_safe (items : List Input) (parameter : Nat)
    {first last : Call construct callbackConstruct fallback selection (Context := Context)}
    {returned : List (Borrowed construct callbackConstruct fallback selection)}
    (path : Cursor.ProducerOccurrenceLog.ProducerPath sourceStep first returned last)
    (safe : Safe construct callbackConstruct fallback selection before reader items parameter first) :
    Safe construct callbackConstruct fallback selection before reader items parameter last ∧
      ∀ borrowed ∈ returned,
        Authentic construct callbackConstruct fallback selection (image construct callbackConstruct fallback selection borrowed) := by
  induction path with
  | refl => exact ⟨safe, by simp⟩
  | @next source outcome rest target transition tail ih =>
      have nextSafe := step_safe construct callbackConstruct fallback selection authority before current reader point required
        quantum items parameter source safe
      have nextOrigins := step_origins construct callbackConstruct fallback selection authority before current reader point required
        quantum items parameter source safe
      rw [transition] at nextSafe nextOrigins
      obtain ⟨finalSafe, origins⟩ := ih nextSafe
      refine ⟨finalSafe, ?_⟩
      intro borrowed member
      rcases List.mem_append.mp member with earlier | later
      · exact nextOrigins borrowed earlier
      · exact origins borrowed later

set_option backward.isDefEq.respectTransparency false in
theorem pump_accounted (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
    (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Accounted construct callbackConstruct fallback selection before reader items parameter state) :
    Accounted construct callbackConstruct fallback selection before reader items parameter
      (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2 := by
  obtain ⟨⟨execution, attached, safe⟩, rows, pending⟩ := accounted
  obtain ⟨next, retained, path⟩ := Cursor.ProducerOccurrenceLog.pump_producer_path
    sourceStep sourceCapture capacity (fun _ => true) state execution attached
  obtain ⟨nextSafe, returned⟩ := path_safe construct callbackConstruct fallback selection authority before current reader point required
    quantum items parameter path safe
  have conserved := Cursor.ProducerOccurrenceLog.pump_conservation
    (image construct callbackConstruct fallback selection) id sourceStep sourceCapture capacity (fun _ => true)
    (fun borrowed stored captured => by cases captured; rfl) state
  have authentic : ∀ stored ∈
      (Cursor.ProducerOccurrenceLog.admitted (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1) ++
        (Cursor.ProducerOccurrenceLog.pending (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2).toList.map
          (image construct callbackConstruct fallback selection),
      Authentic construct callbackConstruct fallback selection stored := by
    simpa only [List.map_id] using (show ∀ stored ∈
      (Cursor.ProducerOccurrenceLog.pending state).toList.map (image construct callbackConstruct fallback selection) ++
        (Cursor.ProducerOccurrenceLog.returned (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1).map
          (image construct callbackConstruct fallback selection),
      Authentic construct callbackConstruct fallback selection stored from by
        intro stored member
        rcases List.mem_append.mp member with old | new
        · obtain ⟨borrowed, present, same⟩ := List.mem_map.mp old
          subst stored
          exact pending borrowed present
        · obtain ⟨borrowed, present, same⟩ := List.mem_map.mp new
          subst stored
          exact returned borrowed present) |> fun proof => by
            rw [conserved] at proof
            simpa only [List.map_id] using proof
  refine ⟨⟨next, retained, nextSafe⟩, ?_, ?_⟩
  · rw [Cursor.ProducerOccurrenceLog.pump_rows]
    intro stored member
    rcases List.mem_append.mp member with old | new
    · exact rows stored old
    · exact authentic stored (List.mem_append_left _ new)
  · intro borrowed member
    exact authentic _ (List.mem_append_right _ (List.mem_map.mpr ⟨borrowed, member, rfl⟩))

variable [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]

set_option backward.isDefEq.respectTransparency false in
theorem delivery_accounted (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Accounted construct callbackConstruct fallback selection before reader items parameter state)
    (client : Fin clients) (owner : Owner) :
    Accounted construct callbackConstruct fallback selection before reader items parameter
      (Cursor.ProducerOccurrenceLog.deliver (fun _ => true) state client owner).2 := by
  obtain ⟨⟨execution, attached, safe⟩, rows, pending⟩ := accounted
  refine ⟨⟨execution, ?_, safe⟩, ?_, ?_⟩
  · simpa only [Cursor.ProducerOccurrenceLog.delivery_preserves_complete_execution] using attached
  · cases reply : Cursor.SharedOccurrenceLog.peek state.delivery.log client <;>
      simpa [Cursor.ProducerOccurrenceLog.deliver, Cursor.SharedOccurrenceOwnership.advance, Cursor.SharedOccurrenceOwnership.acknowledge,
        Cursor.SharedOccurrenceOwnership.prepare, Cursor.SharedOccurrenceLog.pull, Cursor.SharedOccurrenceLog.setPosition, reply] using rows
  · simpa only [Cursor.ProducerOccurrenceLog.pending,
      Cursor.ProducerOccurrenceLog.delivery_preserves_complete_execution] using pending

theorem actions_accounted (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Accounted construct callbackConstruct fallback selection before reader items parameter state) :
    Accounted construct callbackConstruct fallback selection before reader items parameter
      (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions state) := by
  induction actions generalizing state with
  | nil => exact accounted
  | cons action rest ih =>
      cases action with
      | pump => exact ih _ (pump_accounted construct callbackConstruct fallback selection authority before current reader point required
          quantum capacity items parameter state accounted)
      | deliver client owner => exact ih _ (delivery_accounted construct callbackConstruct fallback selection before reader
          items parameter state accounted client owner)

#print axioms path_safe
#print axioms pump_accounted
#print axioms actions_accounted


/-- Publication alignment is proved from the actual log operations. It is
not an assumption that consumer acceptance equals an authored answer list. -/
def Aligned (state : Cfg) : Prop :=
  ∀ execution, state.execution = some execution →
    state.delivery.log.rows.flatMap (·.2.1) ++
      (Cursor.ProducerOccurrenceLog.pending state).toList.flatMap (fun loan => loan.2.2.1.rows) =
      publishedRows construct callbackConstruct fallback selection execution.producer

omit [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner] in
theorem initial_aligned (items : List Input) (parameter : Nat) (context : Context) (limit : Nat) :
    Aligned construct callbackConstruct fallback selection
      (initial construct callbackConstruct fallback selection before reader items parameter context Owner clients limit) := by
  intro execution attached
  cases attached
  rfl

omit [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner] in
set_option backward.isDefEq.respectTransparency false in
theorem pump_aligned (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
    (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Accounted construct callbackConstruct fallback selection before reader items parameter state)
    (aligned : Aligned construct callbackConstruct fallback selection state) :
    Aligned construct callbackConstruct fallback selection
      (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2 := by
  intro next attachedNext
  obtain ⟨⟨execution, attached, safe⟩, _, _⟩ := accounted
  obtain ⟨target, attachedTarget, path⟩ := Cursor.ProducerOccurrenceLog.pump_producer_path
    sourceStep sourceCapture capacity (fun _ => true) state execution attached
  have same : target = next := Option.some.inj (attachedTarget.symm.trans attachedNext)
  subst next
  have row := path_rows construct callbackConstruct fallback selection authority before current reader point required
    quantum items parameter path safe
  have conserved := Cursor.ProducerOccurrenceLog.pump_conservation
    (fun (loan : Borrowed construct callbackConstruct fallback selection) => loan.2.2.1.rows)
    (fun (stored : Stored (Output := Output) (Weight := Weight)) => stored.2.1)
    sourceStep sourceCapture capacity (fun _ => true)
    (by intro loan stored captured; cases captured; rfl) state
  have flat := congrArg (List.flatMap id) conserved
  simp only [List.flatMap_append, List.flatMap_map, id_eq] at flat
  calc
    _ = (state.delivery.log.rows.flatMap (·.2.1) ++
          (Cursor.ProducerOccurrenceLog.admitted (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1).flatMap (·.2.1)) ++
          (Cursor.ProducerOccurrenceLog.pending (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2).toList.flatMap
            (fun loan => loan.2.2.1.rows) := by rw [Cursor.ProducerOccurrenceLog.pump_rows, List.flatMap_append]
    _ = state.delivery.log.rows.flatMap (·.2.1) ++
          ((Cursor.ProducerOccurrenceLog.pending state).toList.flatMap (fun loan => loan.2.2.1.rows) ++
            (Cursor.ProducerOccurrenceLog.returned (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1).flatMap
              (fun loan => loan.2.2.1.rows)) := by rw [List.append_assoc, ← flat]
    _ = publishedRows construct callbackConstruct fallback selection execution.producer ++
          (Cursor.ProducerOccurrenceLog.returned (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1).flatMap
            (fun loan => loan.2.2.1.rows) := by rw [← List.append_assoc, aligned execution attached]
    _ = _ := row.symm

private theorem delivery_rows (state : Cfg) (client : Fin clients) (owner : Owner) :
    (Cursor.ProducerOccurrenceLog.deliver (fun _ => true) state client owner).2.delivery.log.rows = state.delivery.log.rows := by
  cases reply : Cursor.SharedOccurrenceLog.peek state.delivery.log client <;>
    simp [Cursor.ProducerOccurrenceLog.deliver, Cursor.SharedOccurrenceOwnership.advance,
      Cursor.SharedOccurrenceOwnership.acknowledge, Cursor.SharedOccurrenceOwnership.prepare,
      Cursor.SharedOccurrenceLog.pull, Cursor.SharedOccurrenceLog.setPosition, reply]

theorem delivery_aligned (state : Cfg) (aligned : Aligned construct callbackConstruct fallback selection state)
    (client : Fin clients) (owner : Owner) :
    Aligned construct callbackConstruct fallback selection
      (Cursor.ProducerOccurrenceLog.deliver (fun _ => true) state client owner).2 := by
  intro execution attached
  simpa only [delivery_rows, Cursor.ProducerOccurrenceLog.pending,
    Cursor.ProducerOccurrenceLog.delivery_preserves_complete_execution] using
    aligned execution (by simpa only [Cursor.ProducerOccurrenceLog.delivery_preserves_complete_execution] using attached)

theorem actions_aligned (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Accounted construct callbackConstruct fallback selection before reader items parameter state)
    (aligned : Aligned construct callbackConstruct fallback selection state) :
    Aligned construct callbackConstruct fallback selection
      (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions state) := by
  induction actions generalizing state with
  | nil => exact aligned
  | cons action rest ih =>
      cases action with
      | pump =>
          apply ih _
          · exact pump_accounted construct callbackConstruct fallback selection authority before current reader point required quantum capacity items parameter state accounted
          · exact pump_aligned construct callbackConstruct fallback selection authority before current reader point required quantum capacity items parameter state accounted aligned
      | deliver client owner =>
          apply ih _
          · exact delivery_accounted construct callbackConstruct fallback selection before reader items parameter state accounted client owner
          · exact delivery_aligned construct callbackConstruct fallback selection state aligned client owner

/-- Every arbitrary action word keeps the actual source Call and each
compact branch image, and partitions source answers into the admitted prefix,
the held return, and the full saved residual in occurrence order. -/
theorem actions_open_source (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (items : List Input) (parameter : Nat) (context : Context) (limit : Nat) :
    let start := initial construct callbackConstruct fallback selection before reader items parameter context Owner clients limit
    let final := Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions start
    Accounted construct callbackConstruct fallback selection before reader items parameter final ∧
      ∃ execution, final.execution = some execution ∧
        final.delivery.log.rows.flatMap (·.2.1) ++
          (Cursor.ProducerOccurrenceLog.pending final).toList.flatMap (fun loan => loan.2.2.1.rows) ++
          residualRows construct callbackConstruct fallback selection execution.producer =
          source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  dsimp only
  have startAccounted := initial_accounted construct callbackConstruct fallback selection before reader items parameter context limit (Owner := Owner) (clients := clients)
  have startAligned := initial_aligned construct callbackConstruct fallback selection before reader items parameter context limit (Owner := Owner) (clients := clients)
  have finalAccounted := actions_accounted construct callbackConstruct fallback selection authority before current reader point required quantum capacity actions
    items parameter _ startAccounted
  have finalAligned := actions_aligned construct callbackConstruct fallback selection authority before current reader point required quantum capacity actions
    items parameter _ startAccounted startAligned
  obtain ⟨execution, attached, safe⟩ := finalAccounted.1
  refine ⟨finalAccounted, execution, attached, ?_⟩
  rw [finalAligned execution attached, published_residual_eq_view construct callbackConstruct fallback selection execution.producer safe.2.2]
  exact safe.1.2.2

#print axioms actions_open_source


omit [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner] in
set_option backward.isDefEq.respectTransparency false in
/-- A stored row denotes the selected branch of its authentic source loan.
The failed physical ledger is not folded into this per-row interpretation. -/
theorem authentic_factors (stored : Stored (Output := Output) (Weight := Weight))
    (authentic : Authentic construct callbackConstruct fallback selection stored) :
    ∃ reference : BodyCallWeighted.Returned construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection),
      stored.2.1 = reference.2.1.rows ∧
      stored.2.2 = projectLedger (BodyCall.Graded.Compact.Attachment.selected selection reference.2.2.val.val.loan) ∧
      Mettapedia.Algebra.SharedCoefficientLedger.denote stored.2.2 = BodyCall.Graded.loanWeight reference.2.2.val.val ∧
      Valid stored.2.2 := by
  obtain ⟨borrowed, origin, same⟩ := authentic
  subst stored
  obtain ⟨reference, projected⟩ := origin
  refine ⟨reference, ?_, ?_, ?_, image_valid construct callbackConstruct fallback selection borrowed ⟨reference, projected⟩⟩
  · dsimp only [image]
    rw [← projected]
    rfl
  · dsimp only [image]
    rw [← projected]
    rfl
  · change Mettapedia.Algebra.SharedCoefficientLedger.denote (projectLedger borrowed.2.2.2.val.loan) = _
    rw [project_denote, ← projected]
    exact (BodyCallWeighted.Compact.Attachment.returned_source_weight construct callbackConstruct fallback selection reference).1

omit [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner] in
/-- Completion readout is earned in the captured source world. No current
permission check can turn this completed pure value into unfinished code. -/
theorem completed_log_source (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Accounted construct callbackConstruct fallback selection before reader items parameter state)
    (aligned : Aligned construct callbackConstruct fallback selection state)
    (execution : Cursor.ProducerOccurrenceLog.Execution
      (Call construct callbackConstruct fallback selection (Context := Context))
      (Borrowed construct callbackConstruct fallback selection) Empty (Loan construct callbackConstruct fallback selection))
    (attached : state.execution = some execution)
    (noLoan : Cursor.ProducerOccurrenceLog.pending state = none)
    (finished : BodyCallWeighted.Compact.Attachment.complete construct callbackConstruct fallback selection execution.producer = true) :
    state.delivery.log.rows.flatMap (·.2.1) = source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  obtain ⟨⟨actual, retained, safe⟩, _, _⟩ := accounted
  have same : actual = execution := Option.some.inj (retained.symm.trans attached)
  subst actual
  have noPending : execution.producer.2.1.pending = none := by
    cases pending : execution.producer.2.1.pending with
    | none => rfl
    | some loan => simp [BodyCallWeighted.Compact.Attachment.complete, BodyCallWeighted.Compact.Attachment.eraseCall,
        BodyCallAdmission.complete, pending] at finished
  have row := aligned execution attached
  simp only [noLoan, Option.toList_none, List.flatMap_nil, List.append_nil, publishedRows,
    noPending] at row
  exact row.trans (BodyCallWeighted.Compact.Attachment.completed_source construct callbackConstruct fallback selection
    _ items parameter execution.producer safe.1 finished)

section BranchScopes

omit [Semiring Weight] [DecidableEq Output] [DecidableEq Owner]
variable {Observer : Type} [DecidableEq Observer]
local notation "Account" => Scoped Nat Nat Weight Observer

/-- A scope checks the actual immutable branch image and its captured factors.
This claims contributions for readout; it neither issues execution authority
nor combines the ledgers of different alternatives. -/
def observeBranch (stored : Stored (Output := Output) (Weight := Weight))
    (entry current : Account) (observer : Observer) : Option (Account × Ledger Nat Nat Weight) :=
  if current.productions = stored.2.2 then Scoped.handleSince? entry current observer else none

theorem observeBranch_spec (stored : Stored (Output := Output) (Weight := Weight))
    (entry current result : Account) (observer : Observer) (observed : Ledger Nat Nat Weight)
    (accepted : observeBranch stored entry current observer = some (result, observed)) :
    current.productions = stored.2.2 ∧ entry.productions.Sublist stored.2.2 ∧
      result.productions = stored.2.2 ∧ observed = Scoped.selectedSince entry.productions current ∧
      Scoped.selectedSince entry.productions result = [] := by
  unfold observeBranch at accepted
  split at accepted
  · next same =>
      have spec := Scoped.handleSince_spec accepted
      have checked : Scoped.extendsOccurrenceCapture entry current = true := by
        unfold Scoped.handleSince? at accepted
        split at accepted
        · assumption
        · cases accepted
      exact ⟨same, same ▸ (Scoped.extendsOccurrenceCapture_valid checked).2, spec.1.trans same, spec.2⟩
  · cases accepted

theorem observeBranch_claims (stored : Stored (Output := Output) (Weight := Weight))
    (entry current result : Account) (observer : Observer) (observed : Ledger Nat Nat Weight)
    (supported : current.Supported)
    (accepted : observeBranch stored entry current observer = some (result, observed)) :
    result.Supported ∧ (∀ identity prior, current.claims identity = some prior → result.claims identity = some prior) ∧
      (∀ produced ∈ observed, result.claims produced.identity = some observer ∧
        produced ∈ stored.2.2 ∧ produced.identity ∉ identities entry.productions) := by
  unfold observeBranch at accepted
  split at accepted
  · next same =>
      unfold Scoped.handleSince? at accepted
      split at accepted
      · cases accepted
        refine ⟨Scoped.handleSince_supported _ _ _ supported, ?_, ?_⟩
        · intro identity prior claimed
          exact Scoped.handleSince_prior_claim_preserved _ _ _ claimed
        · intro produced member
          have present := (Scoped.mem_selectedSince entry.productions current produced).mp member
          exact ⟨Scoped.selectedSince_claimed _ _ _ member, same ▸ present.1, present.2.2⟩
      · cases accepted
  · cases accepted

end BranchScopes

#print axioms authentic_factors
#print axioms completed_log_source
#print axioms observeBranch_spec
#print axioms observeBranch_claims


/-- Retiring one independently held consumer preserves the whole actual
source, its captured context, protocol account, and the other's ordered view.
The schedule must not subsequently deliver to the retired consumer. -/
theorem independent_retirement (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (account : Cursor.ProducerOccurrenceLog.Accounting.ProtocolAccount) (state : Cfg)
    (retired other : Fin clients) (position : Nat) (distinct : other ≠ retired)
    (live : state.delivery.log.positions other = some position)
    (spares : Cursor.ProducerOccurrenceLog.Accounting.sparesRetired retired actions) :
    let original := Cursor.ProducerOccurrenceLog.Accounting.count sourceStep sourceCapture capacity (fun _ => true) actions account state
    let cancelled := Cursor.ProducerOccurrenceLog.Accounting.count sourceStep sourceCapture capacity (fun _ => true) actions account
      (Cursor.ProducerOccurrenceLog.retireConsumer state retired)
    cancelled.1.execution = original.1.execution ∧ cancelled.1.context = original.1.context ∧
      cancelled.2 = original.2 ∧
      Cursor.SharedOccurrenceLog.peek cancelled.1.delivery.log other = Cursor.SharedOccurrenceLog.peek original.1.delivery.log other ∧
      Cursor.SharedOccurrenceLog.unread cancelled.1.delivery.log other = Cursor.SharedOccurrenceLog.unread original.1.delivery.log other := by
  dsimp only
  rw [Cursor.ProducerOccurrenceLog.Accounting.count_after_retained_demand sourceStep sourceCapture capacity (fun _ => true)
    actions account state retired other position distinct live spares]
  exact ⟨rfl, rfl, rfl, (Cursor.ProducerOccurrenceLog.retireConsumer_releases_only_its_retention _ retired).2.2 other distinct⟩

namespace History

open Cursor.ProducerOccurrenceLog
open Cursor.ProducerOccurrenceLog.Accounting
open Mettapedia.GSLT.Core.InferenceControl.Recording

variable (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
local notation "Action" => Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients
local notation "Occurrence" => CausalEvent (HistoryOccurrence clients)

abbrev observe (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (state : Cfg) :=
  enterActionObservers sourceStep sourceCapture capacity (fun _ => true) history account actions state

/-- Optional history and protocol accounting erase to this same operational
source instance, including the complete Call and immutable branch images. -/
theorem source_erasure (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (items : List Input) (parameter : Nat) (context : Context) (limit : Nat) :
    let start := initial construct callbackConstruct fallback selection before reader items parameter context Owner clients limit
    let observed := observe construct callbackConstruct fallback selection authority before current reader point required quantum capacity history account actions start
    observed.2.2 = runActions sourceStep sourceCapture capacity (fun _ => true) actions start ∧
      Accounted construct callbackConstruct fallback selection before reader items parameter observed.2.2 ∧
      Aligned construct callbackConstruct fallback selection observed.2.2 := by
  dsimp only
  rw [enterActionObservers_erases]
  exact ⟨rfl,
    actions_accounted construct callbackConstruct fallback selection authority before current reader point required quantum capacity actions items parameter _
      (initial_accounted construct callbackConstruct fallback selection before reader items parameter context limit),
    actions_aligned construct callbackConstruct fallback selection authority before current reader point required quantum capacity actions items parameter _
      (initial_accounted construct callbackConstruct fallback selection before reader items parameter context limit)
      (initial_aligned construct callbackConstruct fallback selection before reader items parameter context limit)⟩

theorem forget_keeps_source_and_account (record : Prefix Occurrence) (account : ProtocolAccount)
    (first second : List Action) (state : Cfg) :
    observe construct callbackConstruct fallback selection authority before current reader point required quantum capacity none
      (observe construct callbackConstruct fallback selection authority before current reader point required quantum capacity (some record) (some account) first state).2.1 second
      (observe construct callbackConstruct fallback selection authority before current reader point required quantum capacity (some record) (some account) first state).2.2 =
      (none, some (count sourceStep sourceCapture capacity (fun _ => true) (first ++ second) account state).2,
        runActions sourceStep sourceCapture capacity (fun _ => true) (first ++ second) state) := by
  unfold observe
  rw [forget_action_history_preserves_account, count_erases]

/-- Each observed admission/delivery occurrence belongs to an actual operation
at an actual prefix of this saved source. It grants no execution authority. -/
theorem occurrence_origin (actions : List Action) (state : Cfg) {event : Occurrence}
    (present : event ∈ pathOccurrences sourceStep sourceCapture capacity (fun _ => true)
      (actionPath sourceStep sourceCapture capacity (fun _ => true) actions state)) :
    ∃ done action later, actions = done ++ action :: later ∧
      (actionResult sourceStep sourceCapture capacity (fun _ => true) action
        (runActions sourceStep sourceCapture capacity (fun _ => true) done state)).occurrence = some event :=
  projected_occurrence_is_a_source_reply sourceStep sourceCapture capacity (fun _ => true) actions state present

#print axioms source_erasure
#print axioms forget_keeps_source_and_account
#print axioms occurrence_origin

end History

#print axioms independent_retirement



end BodyCallShared.Weighted

/-! Authored weighted correspondence uses the maintained sparse provider and
client. The independent meaning is recursive on source Code/equations; these
views inspect only the actual current reply, branch factors and saved work. -/
namespace BodyCallWeighted.Authored

open Mettapedia.Algebra.SharedCoefficientLedger
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Cursor.Fold.OwnedSequence.CallbackBoundary

variable {Input Output Weight Context : Type} [Semiring Weight]
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (attachment : BodyCall.WeightedSource.Attachment Input Output Weight)

def selection (activation : BodyCall.Graded.Activation Input Output) :
    Option (WeighClause Weight (BodyCall.Graded.Activation Input Output)) :=
  (BodyCall.WeightedSource.activationValue attachment activation).map WeighClause.scalar

@[simp] theorem selection_values :
    BodyCall.Graded.Compact.Attachment.values (selection attachment) =
      BodyCall.WeightedSource.activationValue attachment := by
  funext activation
  cases attached : BodyCall.WeightedSource.activationValue attachment activation <;>
    simp [BodyCall.Graded.Compact.Attachment.values, selection, attached, WeighClause.eval]

local notation "M" => Compact.Attachment.SparseProvider construct callbackConstruct fallback (selection attachment)
local notation "C" => (BodyCallProtocol.client (Item := Input) (Value := Output))
local notation "Packet" => Cursor.Packet M C (⟨()⟩ : ULift Unit)
local notation "Outcome" => Cursor.Outcome M C (⟨()⟩ : ULift Unit)
local notation "Returned" => Cursor.Finished M (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit)

def stateView : Outcome → BodyCall.Graded.Compact.State Input Output Weight
  | .paused packet => packet.2.2.val
  | .done returned => returned.2.2.val

def moveView : Outcome → BodyCall.Move Input Output
  | .paused packet => packet.2.1.val
  | .done returned => returned.2.1

private theorem forget_state (outcome : Outcome) :
    BodyCallProtocol.stateView construct callbackConstruct fallback
        (Compact.Attachment.forget construct callbackConstruct fallback (selection attachment) outcome) =
      (stateView construct callbackConstruct fallback attachment outcome).core := by
  cases outcome <;> rfl

private theorem forget_move (outcome : Outcome) :
    BodyCallProtocol.moveView construct callbackConstruct fallback
        (Compact.Attachment.forget construct callbackConstruct fallback (selection attachment) outcome) =
      moveView construct callbackConstruct fallback attachment outcome := by
  cases outcome <;> rfl

def safe (outcome : Outcome) : Prop :=
  BodyCall.sourceReadings (stateView construct callbackConstruct fallback attachment outcome).core.work ∧
    (stateView construct callbackConstruct fallback attachment outcome).branches.length =
      (stateView construct callbackConstruct fallback attachment outcome).core.work.length

def residual (state : BodyCall.Graded.Compact.State Input Output Weight) :=
  BodyCall.WeightedSource.workRows construct callbackConstruct attachment state.core.work state.branches

def unaccepted (outcome : Outcome) :=
  BodyCall.WeightedSource.emitted (moveView construct callbackConstruct fallback attachment outcome)
      (stateView construct callbackConstruct fallback attachment outcome).loan ++
    residual construct callbackConstruct attachment (stateView construct callbackConstruct fallback attachment outcome)

private def replyPacket (actual : BodyCall.Move Input Output × BodyCall.Graded.Compact.State Input Output Weight)
    (linked : actual.2.core = actual.1.next) : Packet :=
  ⟨⟨actual.1.next.phase⟩, ⟨actual.1, rfl⟩, ⟨actual.2, congrArg BodyCall.State.phase linked⟩⟩

/-- One bounded client inspection sequence conserves the independent weighted
residual. A pending reply is counted once without another source operation. -/
theorem advance_view (fuel : Nat) (packet : Packet)
    (readings : BodyCall.sourceReadings packet.2.2.val.core.work)
    (aligned : packet.2.2.val.branches.length = packet.2.2.val.core.work.length) :
    let outcome := (Cursor.advance M C (fun _ _ => 1) fuel packet).2
    unaccepted construct callbackConstruct fallback attachment outcome =
        BodyCall.WeightedSource.emitted packet.2.1.val packet.2.2.val.loan ++
          residual construct callbackConstruct attachment packet.2.2.val ∧
      safe construct callbackConstruct fallback attachment outcome := by
  induction fuel generalizing packet with
  | zero => exact ⟨rfl, readings, aligned⟩
  | succ fuel ih =>
      rcases packet with ⟨phase, ⟨control, controlPhase⟩, ⟨state, statePhase⟩⟩
      cases control with
      | advance saved =>
          let actual := BodyCall.Graded.Compact.stepWith construct callbackConstruct fallback
            (BodyCall.Graded.Compact.Attachment.values (selection attachment)) state
          have one : BodyCall.WeightedSource.emitted actual.1 actual.2.loan ++
              residual construct callbackConstruct attachment actual.2 =
                residual construct callbackConstruct attachment state := by
            simpa only [actual, selection_values, residual] using
              BodyCall.WeightedSource.step_preserves_rows construct callbackConstruct fallback attachment state aligned readings
          have kept : BodyCall.sourceReadings actual.2.core.work := by
            simpa only [actual, BodyCall.Graded.Compact.stepWith_link, BodyCall.Graded.Compact.stepWith_move] using
              BodyCall.step_preserves_sourceReadings construct callbackConstruct fallback state.core readings
          have nextAligned : actual.2.branches.length = actual.2.core.work.length := by
            simpa only [actual, selection_values] using
              BodyCall.WeightedSource.step_aligned construct callbackConstruct fallback attachment state aligned
          have later := ih (replyPacket construct callbackConstruct fallback attachment actual
            (BodyCall.Graded.Compact.stepWith_link construct callbackConstruct fallback _ state)) kept nextAligned
          exact ⟨later.1.trans one, later.2⟩
      | yield row next => exact ⟨rfl, readings, aligned⟩
      | finish rows next => exact ⟨rfl, readings, aligned⟩
      | decline next => exact ⟨rfl, readings, aligned⟩
      | handoff next => exact ⟨rfl, readings, aligned⟩

/-- Arbitrary bounded resumption preserves the complete earned reply and
weighted future view. This uses scheduler inspections, not native work ticks. -/
theorem resume_view (fuel : Nat) (previous : Nat × Outcome)
    (valid : safe construct callbackConstruct fallback attachment previous.2) :
    unaccepted construct callbackConstruct fallback attachment
        (Cursor.resume M C (fun _ _ => 1) fuel previous).2 =
      unaccepted construct callbackConstruct fallback attachment previous.2 ∧
    safe construct callbackConstruct fallback attachment
      (Cursor.resume M C (fun _ _ => 1) fuel previous).2 := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | done returned => exact ⟨rfl, valid⟩
  | paused packet => exact advance_view construct callbackConstruct fallback attachment fuel packet valid.1 valid.2

theorem run_open_source (fuel : Nat) (authored : List (Equation Output))
    (items : List Input) (parameter : Nat) :
    let actual := Compact.Attachment.run construct callbackConstruct fallback (selection attachment) fuel authored items parameter
    unaccepted construct callbackConstruct fallback attachment actual.2 =
        BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter ∧
      safe construct callbackConstruct fallback attachment actual.2 := by
  have viewed := advance_view construct callbackConstruct fallback attachment fuel
    (Compact.Attachment.openPacket construct callbackConstruct fallback (selection attachment) authored items parameter)
    (by
      change BodyCall.sourceReadings (BodyCall.openState authored items parameter (.observe .noAnswers)).work
      simp [BodyCall.openState, BodyCall.sourceReadings_cons, BodyCall.Cursor.sourceReading, openFrontier]) (by rfl)
  exact ⟨viewed.1.trans (BodyCall.WeightedSource.open_rows construct callbackConstruct attachment authored items parameter), viewed.2⟩

/-- An ordinary result-collecting consumer folds actual weighted loans. The
user callback retains arbitrary context updates, including stateful refusal;
no factor is generated by this consumer and no future source answer is read. -/
def reader (accept : Context → Returned → Bool × Context)
    (context : List (BodyCall.WeightedSource.Row Output Weight) × Context) (returned : Returned) :=
  let decision := accept context.2 returned
  (decision.1,
    (if decision.1 then context.1 ++ BodyCall.WeightedSource.emitted returned.2.1 returned.2.2.val.loan else context.1,
      decision.2))

local notation "Owned" => Compact.Attachment.OwnedState construct callbackConstruct fallback (selection attachment)
  (Context := List (BodyCall.WeightedSource.Row Output Weight) × Context)
local notation "Call" => Compact.Attachment.Call construct callbackConstruct fallback (selection attachment)
  (Context := List (BodyCall.WeightedSource.Row Output Weight) × Context)

def view (state : Owned) :=
  state.context.2.1 ++ unaccepted construct callbackConstruct fallback attachment state.computation.2

/-- The existing retained callback engine preserves weighted output plus
residual under acceptance, refusal, source pause and terminal re-entry. -/
theorem owned_step_view (quantum : Nat) (accept : Context → Returned → Bool × Context)
    (state : Owned) (request : Request Returned)
    (valid : safe construct callbackConstruct fallback attachment state.computation.2) :
    let later := ((Compact.Attachment.ownedProvider construct callbackConstruct fallback (selection attachment)
      quantum (reader construct callbackConstruct fallback attachment accept)).step
        (base := ()) (index := ()) state request).2
    safe construct callbackConstruct fallback attachment later.computation.2 ∧
      view construct callbackConstruct fallback attachment later = view construct callbackConstruct fallback attachment state := by
  cases request with
  | next =>
      dsimp only [Compact.Attachment.ownedProvider]
      rw [Retained.next_retains_outcome]
      have kept := resume_view construct callbackConstruct fallback attachment quantum state.computation valid
      exact ⟨kept.2, congrArg (state.context.2.1 ++ ·) kept.1⟩
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet =>
          simp only [Compact.Attachment.ownedProvider, Retained.provider, ready]
          exact ⟨by simpa only [ready] using valid, True.intro⟩
      | done returned =>
          cases produced : Compact.Attachment.isReturn construct callbackConstruct fallback (selection attachment) returned with
          | false =>
              simp only [Compact.Attachment.ownedProvider, Retained.provider, ready, produced, Bool.false_eq_true, ↓reduceIte]
              exact ⟨by simpa only [ready] using valid, True.intro⟩
          | true =>
              cases decision : (accept state.context.2.2 returned).1 with
              | false =>
                  simp only [Compact.Attachment.ownedProvider, Retained.provider, ready, produced,
                    Compact.Attachment.consume, reader, decision, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨by simpa only [ready] using valid, rfl⟩
              | true =>
                  simp only [Compact.Attachment.ownedProvider, Retained.provider, ready, produced,
                    Compact.Attachment.consume, reader, decision, ↓reduceIte]
                  constructor
                  · simpa only [safe, stateView, ready, Compact.Attachment.rearm] using valid
                  · simp [view, unaccepted, ready, stateView, moveView, Compact.Attachment.rearm,
                      BodyCall.WeightedSource.emitted, BodyCall.Move.rows, List.append_assoc]

/-- Reachability retains both independent source views and the actual quiet
finished invariant. No equation equating accepted grades to source is assumed. -/
def Captured (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call) : Prop :=
  Compact.Attachment.Captured construct callbackConstruct fallback (selection attachment) authored items parameter call ∧
    safe construct callbackConstruct fallback attachment call.2.2.computation.2 ∧
    view construct callbackConstruct fallback attachment call.2.2 =
      BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter

theorem open_captured (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    Captured construct callbackConstruct fallback attachment authored items parameter
      (Compact.Attachment.openCall construct callbackConstruct fallback (selection attachment) authored items parameter ([], context)) := by
  refine ⟨Compact.Attachment.open_captured construct callbackConstruct fallback (selection attachment) authored items parameter ([], context), ?_, ?_⟩
  · constructor
    · change BodyCall.sourceReadings (BodyCall.openState authored items parameter (.observe .noAnswers)).work
      simp [BodyCall.openState, BodyCall.sourceReadings_cons, BodyCall.Cursor.sourceReading, openFrontier]
    · rfl
  · exact BodyCall.WeightedSource.open_rows construct callbackConstruct attachment authored items parameter

theorem resume_captured (quantum allowance : Nat) (accept : Context → Returned → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (previous : Call)
    (valid : Captured construct callbackConstruct fallback attachment authored items parameter previous) :
    Captured construct callbackConstruct fallback attachment authored items parameter
      (Compact.Attachment.resumeCallSource construct callbackConstruct fallback (selection attachment)
        quantum allowance (reader construct callbackConstruct fallback attachment accept) previous) := by
  refine ⟨Compact.Attachment.resume_captured construct callbackConstruct fallback (selection attachment)
    quantum allowance (reader construct callbackConstruct fallback attachment accept) authored items parameter previous valid.1, ?_⟩
  unfold Compact.Attachment.resumeCallSource resumeCall
  cases previous.2.1.terminal with
  | some reason => exact valid.2
  | none =>
      refine fromCallbacks_invariant (Compact.Attachment.ownedProvider construct callbackConstruct fallback (selection attachment)
        quantum (reader construct callbackConstruct fallback attachment accept)) (fun _ _ => 1)
        (fun (state : Owned) => safe construct callbackConstruct fallback attachment state.computation.2 ∧
          view construct callbackConstruct fallback attachment state =
            BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter)
        ?_ allowance previous.2.1.accepted previous.2.1.pending previous.2.2 valid.2 _
      intro state request invariant
      have kept := owned_step_view construct callbackConstruct fallback attachment quantum accept state request invariant.1
      exact ⟨kept.1, kept.2.trans invariant.2⟩

abbrev Grant := Nat × Nat × (Context → Returned → Bool × Context)

def readGrants (grants : List (Grant construct callbackConstruct fallback attachment (Context := Context))) :=
  grants.map (fun grant => (grant.1, grant.2.1, reader construct callbackConstruct fallback attachment grant.2.2))

theorem schedule_captured (grants : List (Grant construct callbackConstruct fallback attachment (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (previous : Call)
    (valid : Captured construct callbackConstruct fallback attachment authored items parameter previous) :
    Captured construct callbackConstruct fallback attachment authored items parameter
      (Compact.Attachment.schedule construct callbackConstruct fallback (selection attachment)
        (readGrants construct callbackConstruct fallback attachment grants) previous) := by
  induction grants generalizing previous with
  | nil => exact valid
  | cons grant rest ih => exact ih _ (resume_captured construct callbackConstruct fallback attachment grant.1 grant.2.1
      grant.2.2 authored items parameter previous valid)

/-- Only an actual acknowledged finished cut exposes the completed weighted
answers. It preserves the whole retained call and its captured source world. -/
def readout (call : Call) : Option (List (BodyCall.WeightedSource.Row Output Weight)) × Call :=
  ((if Compact.Attachment.complete construct callbackConstruct fallback (selection attachment) call then
    some call.2.2.context.2.1 else none), call)

theorem completed_source (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call)
    (valid : Captured construct callbackConstruct fallback attachment authored items parameter call)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback (selection attachment) call = true) :
    call.2.2.context.2.1 = BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter := by
  have cut := BodyCallAdmission.complete_cut construct callbackConstruct fallback
    (Compact.Attachment.eraseCall construct callbackConstruct fallback (selection attachment) call) finished
  simp only [Compact.Attachment.eraseCall, forget_state, forget_move] at cut
  have quiet := valid.1.2.1
  change BodyCallProtocol.finishedQuiet construct callbackConstruct
    (BodyCallProtocol.stateView construct callbackConstruct fallback
      (Compact.Attachment.forget construct callbackConstruct fallback (selection attachment) call.2.2.computation.2)) at quiet
  rw [forget_state] at quiet
  have erased := BodyCall.WeightedSource.workRows_erase construct callbackConstruct attachment
    (stateView construct callbackConstruct fallback attachment call.2.2.computation.2).core.work
    (stateView construct callbackConstruct fallback attachment call.2.2.computation.2).branches valid.2.1.2
  have empty : residual construct callbackConstruct attachment
      (stateView construct callbackConstruct fallback attachment call.2.2.computation.2) = [] :=
    List.map_eq_nil_iff.mp (erased.trans (quiet cut.1))
  simpa only [view, unaccepted, BodyCall.WeightedSource.emitted, cut.2, List.map_nil, List.nil_append,
    empty, List.append_nil] using valid.2.2

theorem schedule_open_completed (grants : List (Grant construct callbackConstruct fallback attachment (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback (selection attachment)
      (Compact.Attachment.schedule construct callbackConstruct fallback (selection attachment)
        (readGrants construct callbackConstruct fallback attachment grants)
        (Compact.Attachment.openCall construct callbackConstruct fallback (selection attachment) authored items parameter ([], context))) = true) :
    (Compact.Attachment.schedule construct callbackConstruct fallback (selection attachment)
      (readGrants construct callbackConstruct fallback attachment grants)
      (Compact.Attachment.openCall construct callbackConstruct fallback (selection attachment) authored items parameter ([], context))).2.2.context.2.1 =
        BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter :=
  completed_source construct callbackConstruct fallback attachment authored items parameter _
    (schedule_captured construct callbackConstruct fallback attachment grants authored items parameter _
      (open_captured construct callbackConstruct fallback attachment authored items parameter context)) finished

/-- Existing source-inferred conventions license weighted result readout.
The gate examines completion and the existing selected-worker convention. -/
def admit (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call) :
    Option (List (BodyCall.WeightedSource.Row Output Weight)) × Call :=
  ((if Compact.Attachment.complete construct callbackConstruct fallback (selection attachment) call &&
    BodyCallAdmission.modeEligible requested (BodyCallAdmission.workerMode (selectWorker authored items parameter interface)) interface then
      some call.2.2.context.2.1 else none), call)

theorem admit_license (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call)
    (valid : Captured construct callbackConstruct fallback attachment authored items parameter call)
    (answers : List (BodyCall.WeightedSource.Row Output Weight))
    (admitted : (admit construct callbackConstruct fallback attachment requested interface authored items parameter call).1 = some answers) :
    answers = BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter ∧
      ConventionAllows requested answers.length := by
  unfold admit at admitted
  split at admitted
  next allowed =>
    have gates := Bool.and_eq_true_iff.mp allowed
    have actual := completed_source construct callbackConstruct fallback attachment authored items parameter call valid gates.1
    have same := Option.some.inj admitted
    refine ⟨same.symm.trans actual, ?_⟩
    have mode := BodyCallAdmission.modeEligible_sound requested _ interface
      (source construct callbackConstruct authored items parameter).length gates.2
      (BodyCallAdmission.selected_mode_sound construct callbackConstruct authored items parameter interface)
    have counts := congrArg List.length (BodyCall.WeightedSource.source_erase construct callbackConstruct attachment authored items parameter)
    simp only [List.length_map] at counts
    rw [← actual, same] at counts
    simpa only [← counts] using mode
  next refused => cases admitted

/-- Ordered coefficient-word equality yields the semiring readout without
commutativity. Zero-valued rows remain in this list. -/
theorem completed_denote (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call)
    (valid : Captured construct callbackConstruct fallback attachment authored items parameter call)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback (selection attachment) call = true) :
    call.2.2.context.2.1.map (fun row => (row.1, row.2.prod)) =
      (BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter).map
        (fun row => (row.1, row.2.prod)) :=
  congrArg (List.map (fun row : BodyCall.WeightedSource.Row Output Weight => (row.1, row.2.prod)))
    (completed_source construct callbackConstruct fallback attachment authored items parameter call valid finished)

theorem origin_aligned (outcome : Outcome)
    (origin : Compact.Attachment.Origin construct callbackConstruct fallback (selection attachment) outcome) :
    (stateView construct callbackConstruct fallback attachment outcome).branches.length =
      (stateView construct callbackConstruct fallback attachment outcome).core.work.length := by
  obtain ⟨reference, same⟩ := origin
  rw [← same]
  cases reference with
  | paused packet =>
      change (packet.2.2.val.val.branches.map
        (BodyCall.Graded.Compact.Attachment.selected (selection attachment))).length = packet.2.2.val.val.core.work.length
      simpa only [List.length_map, BodyCall.Graded.Aligned] using packet.2.2.val.property.2.2
  | done returned =>
      change (returned.2.2.val.val.branches.map
        (BodyCall.Graded.Compact.Attachment.selected (selection attachment))).length = returned.2.2.val.val.core.work.length
      simpa only [List.length_map, BodyCall.Graded.Aligned] using returned.2.2.val.property.2.2

theorem completed_unaccepted
    (call : Compact.Attachment.Call construct callbackConstruct fallback (selection attachment) (Context := Context))
    (quiet : Compact.Attachment.quiet construct callbackConstruct fallback (selection attachment) call.2.2)
    (aligned : (stateView construct callbackConstruct fallback attachment call.2.2.computation.2).branches.length =
      (stateView construct callbackConstruct fallback attachment call.2.2.computation.2).core.work.length)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback (selection attachment) call = true) :
    unaccepted construct callbackConstruct fallback attachment call.2.2.computation.2 = [] := by
  have cut := BodyCallAdmission.complete_cut construct callbackConstruct fallback
    (Compact.Attachment.eraseCall construct callbackConstruct fallback (selection attachment) call) finished
  simp only [Compact.Attachment.eraseCall, forget_state, forget_move] at cut
  change BodyCallProtocol.finishedQuiet construct callbackConstruct
    (BodyCallProtocol.stateView construct callbackConstruct fallback
      (Compact.Attachment.forget construct callbackConstruct fallback (selection attachment) call.2.2.computation.2)) at quiet
  rw [forget_state] at quiet
  have erased := BodyCall.WeightedSource.workRows_erase construct callbackConstruct attachment
    (stateView construct callbackConstruct fallback attachment call.2.2.computation.2).core.work
    (stateView construct callbackConstruct fallback attachment call.2.2.computation.2).branches aligned
  have empty : residual construct callbackConstruct attachment
      (stateView construct callbackConstruct fallback attachment call.2.2.computation.2) = [] :=
    List.map_eq_nil_iff.mp (erased.trans (quiet cut.1))
  simp only [unaccepted, BodyCall.WeightedSource.emitted, cut.2, List.map_nil, List.nil_append, empty]

#print axioms origin_aligned
#print axioms completed_unaccepted

#print axioms owned_step_view
#print axioms open_captured
#print axioms resume_captured
#print axioms schedule_captured
#print axioms completed_source
#print axioms schedule_open_completed
#print axioms admit_license
#print axioms completed_denote

#print axioms selection_values
#print axioms advance_view
#print axioms resume_view
#print axioms run_open_source


end BodyCallWeighted.Authored

/-! The shared weighted instance observes existing immutable branch images.
Its residual excludes a pending loan already exposed to the occurrence log;
acknowledgment therefore cannot mint another semantic occurrence. -/
namespace BodyCallShared.Weighted.Authored

open Mettapedia.Algebra.SharedCoefficientLedger
open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory

variable {Input Output Weight Context : Type} [Semiring Weight]
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (attachment : BodyCall.WeightedSource.Attachment Input Output Weight)

local notation "selected" => BodyCallWeighted.Authored.selection attachment
local notation "Call" => Weighted.Call construct callbackConstruct fallback selected (Context := Context)
local notation "Borrowed" => Weighted.Borrowed construct callbackConstruct fallback selected
local notation "Source" => BodyCallWeighted.Authored.stateView construct callbackConstruct fallback attachment
local notation "View" => BodyCallWeighted.Authored.unaccepted construct callbackConstruct fallback attachment

def loanRows (borrowed : Borrowed) :=
  BodyCall.WeightedSource.emitted borrowed.2.2.1 borrowed.2.2.2.val.loan

def storedRows (stored : Weighted.Stored (Output := Output) (Weight := Weight)) :=
  stored.2.1.map (fun row => (row, stored.2.2.map (·.coefficient)))

theorem capture_rows (borrowed : Borrowed) :
    storedRows (Weighted.image construct callbackConstruct fallback selected borrowed) =
      loanRows construct callbackConstruct fallback attachment borrowed := by
  simp [storedRows, Weighted.image, Weighted.projectLedger, BodyCall.WeightedSource.emitted,
    loanRows, List.map_map, Function.comp_def, Factor.rename]

def residual (call : Call) :=
  match call.2.1.pending with
  | some _ => BodyCallWeighted.Authored.residual construct callbackConstruct attachment (Source call.2.2.computation.2)
  | none => View call.2.2.computation.2

theorem inspect_rows (call : Call) (coherent : Weighted.Coherent construct callbackConstruct fallback selected call) :
    (Weighted.inspect construct callbackConstruct fallback selected call).returns.flatMap
        (loanRows construct callbackConstruct fallback attachment) ++ residual construct callbackConstruct fallback attachment call =
      View call.2.2.computation.2 := by
  rw [Weighted.inspect_returns construct callbackConstruct fallback selected call coherent]
  cases pending : call.2.1.pending with
  | none => simp [pending, residual]
  | some loan =>
      have held := coherent loan pending
      simp [pending, residual, loanRows, BodyCallWeighted.Authored.unaccepted,
        held.2.1, BodyCallWeighted.Authored.moveView, BodyCallWeighted.Authored.stateView]

theorem acknowledge_rows (call : Call) (coherent : Weighted.Coherent construct callbackConstruct fallback selected call)
    (loan : Weighted.Loan construct callbackConstruct fallback selected) (pending : call.2.1.pending = some loan) :
    residual construct callbackConstruct fallback attachment
        (BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selected 0 1
          (Weighted.accept construct callbackConstruct fallback selected) call) =
      residual construct callbackConstruct fallback attachment call := by
  have held := coherent loan pending
  cases final : BodyCallWeighted.Compact.Attachment.terminalAfter construct callbackConstruct fallback selected loan <;>
    simp [BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall, held.1, pending, fromCallbacks,
      BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider, held.2.1, held.2.2,
      BodyCallWeighted.Compact.Attachment.consume, Weighted.accept, final, residual,
      BodyCallWeighted.Authored.unaccepted, BodyCallWeighted.Authored.stateView,
      BodyCallWeighted.Authored.moveView, BodyCallWeighted.Compact.Attachment.rearm,
      BodyCall.WeightedSource.emitted, BodyCall.Move.rows]

private theorem poll_view (quantum : Nat) (call : Call)
    (running : call.2.1.terminal = none) (empty : call.2.1.pending = none)
    (safe : BodyCallWeighted.Authored.safe construct callbackConstruct fallback attachment call.2.2.computation.2) :
    View (BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selected quantum 1
      (Weighted.refuse construct callbackConstruct fallback selected) call).2.2.computation.2 =
        View call.2.2.computation.2 := by
  have preserved := (BodyCallWeighted.Authored.resume_view construct callbackConstruct fallback attachment quantum call.2.2.computation safe).1
  cases outcome : (Cursor.resume (BodyCallWeighted.Compact.Attachment.SparseProvider construct callbackConstruct fallback selected)
    BodyCallProtocol.client (fun _ _ => 1) quantum call.2.2.computation).2 with
  | paused saved =>
      simpa [BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall, running, empty,
        fromCallbacks, BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider, outcome] using preserved
  | done returned =>
      cases produced : BodyCallWeighted.Compact.Attachment.isReturn construct callbackConstruct fallback selected returned <;>
        simpa [BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall, running, empty,
          fromCallbacks, BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider, outcome,
          produced, BodyCallWeighted.Compact.Attachment.consume, Weighted.refuse] using preserved

variable {size : Nat} (before : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)

theorem safe_view (items : List Input) (parameter : Nat) (call : Call)
    (safe : Weighted.Safe construct callbackConstruct fallback selected before reader items parameter call) :
    BodyCallWeighted.Authored.safe construct callbackConstruct fallback attachment call.2.2.computation.2 := by
  refine ⟨?_, BodyCallWeighted.Authored.origin_aligned construct callbackConstruct fallback attachment _ safe.2.1⟩
  have readings := safe.1.1.2
  change BodyCall.sourceReadings
    (BodyCallProtocol.stateView construct callbackConstruct fallback
      (BodyCallWeighted.Compact.Attachment.forget construct callbackConstruct fallback selected call.2.2.computation.2)).work at readings
  rw [BodyCallWeighted.Authored.forget_state] at readings
  exact readings

variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    (current : OrderedDependencyStore.Store (Equation Output) size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)] (quantum : Nat)
local notation "sourceStep" => Weighted.step construct callbackConstruct fallback selected authority before current reader point required quantum

set_option backward.isDefEq.respectTransparency false in
theorem step_rows (items : List Input) (parameter : Nat) (call : Call)
    (safe : Weighted.Safe construct callbackConstruct fallback selected before reader items parameter call) :
    (sourceStep call).returns.flatMap (loanRows construct callbackConstruct fallback attachment) ++
        residual construct callbackConstruct fallback attachment (sourceStep call).next =
      residual construct callbackConstruct fallback attachment call := by
  unfold Weighted.step BodyCallShared.retainedStep
  split
  · have noLoan : call.2.1.pending = none := by
      cases pending : call.2.1.pending with
      | none => rfl
      | some loan => simp [(safe.2.2 loan pending).1] at ‹call.2.1.terminal.isSome = true›
    rw [Weighted.inspect_next, Weighted.inspect_returns construct callbackConstruct fallback selected call safe.2.2]
    simp [noLoan]
  · cases pending : call.2.1.pending with
    | some loan =>
        exact acknowledge_rows construct callbackConstruct fallback attachment call safe.2.2 loan pending
    | none =>
        dsimp only
        have running : call.2.1.terminal = none := by simpa using ‹¬call.2.1.terminal.isSome = true›
        have kept := Weighted.poll_safe construct callbackConstruct fallback selected authority before current reader point required quantum
          items parameter call safe running pending
        rw [Weighted.inspect_next]
        have observed := inspect_rows construct callbackConstruct fallback attachment
          (Weighted.poll construct callbackConstruct fallback selected authority before current reader point required quantum call) kept.2.2
        rw [observed]
        by_cases fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true
        · by_cases permitted : FrameUpdate point.authority required
          · simpa only [Weighted.poll, fresh, permitted, ↓reduceIte, residual, pending] using
              poll_view construct callbackConstruct fallback attachment quantum call running pending
                (safe_view construct callbackConstruct fallback attachment before reader items parameter call safe)
          · simp [Weighted.poll, fresh, permitted, residual, pending]
        · simp [Weighted.poll, fresh, residual, pending]

/-- Existing actual producer paths telescope the ordered loan/residual law;
no schedule-independent trace or factor identity is invented. -/
theorem path_rows (items : List Input) (parameter : Nat)
    {first last : Call} {returns : List Borrowed}
    (path : Cursor.ProducerOccurrenceLog.ProducerPath sourceStep first returns last)
    (safe : Weighted.Safe construct callbackConstruct fallback selected before reader items parameter first) :
    returns.flatMap (loanRows construct callbackConstruct fallback attachment) ++
        residual construct callbackConstruct fallback attachment last =
      residual construct callbackConstruct fallback attachment first := by
  induction path with
  | refl => rfl
  | @next first move later returns transition tail ih =>
      have kept := Weighted.step_safe construct callbackConstruct fallback selected authority before current reader point required quantum
        items parameter first safe
      have one := step_rows construct callbackConstruct fallback attachment before reader authority current point required quantum items parameter first safe
      rw [transition] at kept one
      rw [List.flatMap_append, List.append_assoc, ih kept, one]

variable {Owner : Type} {clients : Nat}
local notation "Cfg" => Weighted.Configuration construct callbackConstruct fallback selected
  (Context := Context) (size := size) Owner clients
local notation "sourceCapture" => Weighted.capture construct callbackConstruct fallback selected
local notation "Execution" => Cursor.ProducerOccurrenceLog.Execution Call Borrowed Empty
  (Weighted.Loan construct callbackConstruct fallback selected)

def view (state : Cfg) (call : Call) :=
  state.delivery.log.rows.flatMap (storedRows (Output := Output) (Weight := Weight)) ++
    (Cursor.ProducerOccurrenceLog.pending state).toList.flatMap (loanRows construct callbackConstruct fallback attachment) ++
      residual construct callbackConstruct fallback attachment call

set_option backward.isDefEq.respectTransparency false in
theorem pump_view (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (items : List Input) (parameter : Nat) (state : Cfg) (execution target : Execution)
    (attached : state.execution = some execution)
    (nextAttached : (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2.execution = some target)
    (safe : Weighted.Safe construct callbackConstruct fallback selected before reader items parameter execution.producer) :
    view construct callbackConstruct fallback attachment
        (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2 target.producer =
      view construct callbackConstruct fallback attachment state execution.producer := by
  obtain ⟨actual, retained, path⟩ := Cursor.ProducerOccurrenceLog.pump_producer_path sourceStep sourceCapture capacity (fun _ => true) state execution attached
  have same : actual = target := Option.some.inj (retained.symm.trans nextAttached)
  subst actual
  have row := path_rows construct callbackConstruct fallback attachment before reader authority current point required quantum
    items parameter path safe
  have conserved := Cursor.ProducerOccurrenceLog.pump_conservation
    (loanRows construct callbackConstruct fallback attachment) (storedRows (Output := Output) (Weight := Weight))
    sourceStep sourceCapture capacity (fun _ => true)
    (by intro loan stored captured; cases captured; exact capture_rows construct callbackConstruct fallback attachment loan) state
  have flat := congrArg (List.flatMap id) conserved
  simp only [List.flatMap_append, List.flatMap_map, id_eq] at flat
  unfold view
  rw [Cursor.ProducerOccurrenceLog.pump_rows, List.flatMap_append]
  calc
    _ = state.delivery.log.rows.flatMap storedRows ++
        ((Cursor.ProducerOccurrenceLog.admitted (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1).flatMap storedRows ++
          (Cursor.ProducerOccurrenceLog.pending (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2).toList.flatMap
            (loanRows construct callbackConstruct fallback attachment)) ++
          residual construct callbackConstruct fallback attachment target.producer := by simp only [List.append_assoc]
    _ = state.delivery.log.rows.flatMap storedRows ++
        ((Cursor.ProducerOccurrenceLog.pending state).toList.flatMap (loanRows construct callbackConstruct fallback attachment) ++
          (Cursor.ProducerOccurrenceLog.returned (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1).flatMap
            (loanRows construct callbackConstruct fallback attachment)) ++
          residual construct callbackConstruct fallback attachment target.producer := by rw [← flat]
    _ = _ := by simp only [List.append_assoc]; rw [row]

private theorem delivery_view [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (state : Cfg) (execution : Execution) (client : Fin clients) (owner : Owner) :
    view construct callbackConstruct fallback attachment (Cursor.ProducerOccurrenceLog.deliver (fun _ => true) state client owner).2 execution.producer =
      view construct callbackConstruct fallback attachment state execution.producer := by
  simp only [view, Weighted.delivery_rows, Cursor.ProducerOccurrenceLog.pending,
    Cursor.ProducerOccurrenceLog.delivery_preserves_complete_execution]

private theorem actions_view [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Weighted.Accounted construct callbackConstruct fallback selected before reader items parameter state)
    (conserved : ∀ execution, state.execution = some execution →
      view construct callbackConstruct fallback attachment state execution.producer =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter) :
    ∀ execution, (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions state).execution = some execution →
      view construct callbackConstruct fallback attachment
        (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions state) execution.producer =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
  induction actions generalizing state with
  | nil => exact conserved
  | cons action rest ih =>
      cases action with
      | pump =>
          apply ih _ (Weighted.pump_accounted construct callbackConstruct fallback selected authority before current reader point required quantum capacity
            items parameter state accounted)
          intro target attachedTarget
          obtain ⟨⟨execution, attached, safe⟩, _, _⟩ := accounted
          exact (pump_view construct callbackConstruct fallback attachment before reader authority current point required quantum capacity
            items parameter state execution target attached attachedTarget safe).trans (conserved execution attached)
      | deliver client owner =>
          apply ih _ (Weighted.delivery_accounted construct callbackConstruct fallback selected before reader items parameter state accounted client owner)
          intro execution attached
          exact (delivery_view construct callbackConstruct fallback attachment state execution client owner).trans
            (conserved execution (by simpa only [Cursor.ProducerOccurrenceLog.delivery_preserves_complete_execution] using attached))

/-- Arbitrary actual shared pump/delivery actions preserve the independent
weighted source partition in existing stored rows, pending loan and residual. -/
theorem actions_open_source [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (items : List Input) (parameter : Nat) (context : Context) (limit : Nat) :
    let start := Weighted.initial construct callbackConstruct fallback selected before reader items parameter context Owner clients limit
    let final := Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions start
    Weighted.Accounted construct callbackConstruct fallback selected before reader items parameter final ∧
      ∃ execution, final.execution = some execution ∧
        view construct callbackConstruct fallback attachment final execution.producer =
          BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
  dsimp only
  have startAccounted := Weighted.initial_accounted construct callbackConstruct fallback selected before reader items parameter context limit (Owner := Owner) (clients := clients)
  have finalAccounted := Weighted.actions_accounted construct callbackConstruct fallback selected authority before current reader point required quantum capacity actions
    items parameter _ startAccounted
  have initialView : ∀ execution, (Weighted.initial construct callbackConstruct fallback selected before reader items parameter context Owner clients limit).execution = some execution →
      view construct callbackConstruct fallback attachment
        (Weighted.initial construct callbackConstruct fallback selected before reader items parameter context Owner clients limit) execution.producer =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
    intro execution attached
    cases attached
    exact BodyCall.WeightedSource.open_rows construct callbackConstruct attachment _ items parameter
  have finalView := actions_view construct callbackConstruct fallback attachment before reader authority current point required quantum capacity actions
    items parameter _ startAccounted initialView
  obtain ⟨execution, attached, _⟩ := finalAccounted.1
  exact ⟨finalAccounted, execution, attached, finalView execution attached⟩

/-- On an actually finished, acknowledged shared cut, stored branch images
alone equal the recursively weighted authored source. Delivery adds no factor. -/
theorem completed_log_source [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (items : List Input) (parameter : Nat) (context : Context) (limit : Nat)
    (execution : Execution)
    (attached : (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions
      (Weighted.initial construct callbackConstruct fallback selected before reader items parameter context Owner clients limit)).execution = some execution)
    (noLoan : Cursor.ProducerOccurrenceLog.pending
      (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions
        (Weighted.initial construct callbackConstruct fallback selected before reader items parameter context Owner clients limit)) = none)
    (finished : BodyCallWeighted.Compact.Attachment.complete construct callbackConstruct fallback selected execution.producer = true) :
    (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions
      (Weighted.initial construct callbackConstruct fallback selected before reader items parameter context Owner clients limit)).delivery.log.rows.flatMap storedRows =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
  obtain ⟨accounted, actual, retained, conserved⟩ := actions_open_source construct callbackConstruct fallback attachment before reader authority current point required quantum
    capacity actions items parameter context limit (Owner := Owner) (clients := clients)
  have same : actual = execution := Option.some.inj (retained.symm.trans attached)
  subst actual
  obtain ⟨⟨actual, retained, safe⟩, _, _⟩ := accounted
  have same : actual = execution := Option.some.inj (retained.symm.trans attached)
  subst actual
  have noPending : execution.producer.2.1.pending = none := by
    cases pending : execution.producer.2.1.pending with
    | none => rfl
    | some loan => simp [BodyCallWeighted.Compact.Attachment.complete, BodyCallWeighted.Compact.Attachment.eraseCall,
        BodyCallAdmission.complete, pending] at finished
  have empty := BodyCallWeighted.Authored.completed_unaccepted construct callbackConstruct fallback attachment
    execution.producer safe.1.2.1 (safe_view construct callbackConstruct fallback attachment before reader items parameter execution.producer safe).2 finished
  simpa only [view, noLoan, Option.toList_none, List.flatMap_nil, List.append_nil, residual, noPending, empty] using conserved

#print axioms pump_view
#print axioms actions_open_source
#print axioms completed_log_source

#print axioms capture_rows
#print axioms inspect_rows
#print axioms acknowledge_rows
#print axioms safe_view
#print axioms step_rows
#print axioms path_rows


end BodyCallShared.Weighted.Authored

namespace BodyCallShared.Handoff

open Cursor.ProducerOccurrenceLog
open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory

variable {Input Output Context Owner : Type} {clients size : Nat}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)

local notation "Call" => BodyCallShared.Call construct callbackConstruct fallback (Context := Context)
local notation "Loan" => BodyCallShared.Loan construct callbackConstruct fallback
local notation "Borrowed" => BodyCallShared.Borrowed construct callbackConstruct fallback
local notation "Cfg" => BodyCallShared.Configuration construct callbackConstruct fallback
  (Context := Context) (size := size) Owner clients

private theorem callbacks_coherent (quantum : Nat)
    (consumer : Context → Loan → Bool × Context)
    (charges : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer))
    (allowance accepted : Nat) (held : Option Loan)
    (state : BodyCallOwned.State construct callbackConstruct fallback (Context := Context))
    (aligned : ∀ loan, held = some loan → state.computation.2 = .done loan ∧
      BodyCallOwned.isReturn construct callbackConstruct fallback loan = true) :
    BodyCallShared.Coherent construct callbackConstruct fallback
      (fromCallbacks (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer)
        charges allowance held accepted state (BodyCallOwned.terminalAfter construct callbackConstruct fallback)) := by
  simpa only [BodyCallShared.Coherent, BodyCallOwned.provider] using
    BodyCallShared.retainedCallbacks_coherent
      (BodyCallProtocol.provider construct callbackConstruct fallback)
      (BodyCallProtocol.requestCharge construct callbackConstruct fallback) quantum
      (BodyCallOwned.isReturn construct callbackConstruct fallback)
      (BodyCallOwned.rearm construct callbackConstruct fallback)
      (BodyCallOwned.consume construct callbackConstruct fallback consumer)
      (BodyCallOwned.terminalAfter construct callbackConstruct fallback)
      charges allowance accepted held state aligned

/-- Actual ordinary callback resumption constructs the loan-shape invariant;
it is not supplied as an equality with an expected answer stream. -/
theorem resume_coherent (quantum allowance : Nat)
    (consumer : Context → Loan → Bool × Context)
    (charges : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer))
    (call : Call) (coherent : BodyCallShared.Coherent construct callbackConstruct fallback call) :
    BodyCallShared.Coherent construct callbackConstruct fallback
      (BodyCallAdmission.resume construct callbackConstruct fallback quantum allowance consumer charges call) := by
  unfold BodyCallAdmission.resume resumeCall
  cases stopped : call.2.1.terminal with
  | some reason => exact coherent
  | none =>
      simpa [BodyCallShared.Coherent] using
        callbacks_coherent construct callbackConstruct fallback quantum consumer charges allowance
          call.2.1.accepted call.2.1.pending call.2.2 (fun loan pending => (coherent loan pending).2)

theorem schedule_coherent
    (charges : ∀ quantum (consumer : Context → Loan → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer))
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    BodyCallShared.Coherent construct callbackConstruct fallback
      (BodyCallAdmission.schedule construct callbackConstruct fallback charges grants
        (BodyCallAdmission.openCall construct callbackConstruct fallback authored items parameter context)) := by
  have preserved : ∀ call : Call, BodyCallShared.Coherent construct callbackConstruct fallback call →
      BodyCallShared.Coherent construct callbackConstruct fallback
        (BodyCallAdmission.schedule construct callbackConstruct fallback charges grants call) := by
    induction grants with
    | nil => exact fun _ safe => safe
    | cons grant rest ih =>
        exact fun call safe => ih _ (resume_coherent construct callbackConstruct fallback grant.1 grant.2.1 grant.2.2
          (charges grant.1 grant.2.2) call safe)
  exact preserved _ (BodyCallShared.open_coherent construct callbackConstruct fallback authored items parameter context)

/-- Transfer the actual owned cut. Its held return is already issued, so it
enters the log's pending slot without invoking the source or its consumer.
Prior ordinary acknowledgments stay in the Call, outside the new reader log. -/
def adopt (world : OrderedDependencyStore.Store (Equation Output) size)
    (limit : Nat) (call : Call) : Cfg :=
  BodyCallShared.retainedAdopt world limit call

/-- Handback distinguishes a loan still awaiting capture from one already
captured by the shared log. The latter needs only its existing acknowledgment;
no source request is made. Buffered images retain their independent owners. -/
def release (state : Cfg) : Option Call × Cfg :=
  BodyCallShared.retainedRelease
    (BodyCallAdmission.resume construct callbackConstruct fallback 0 1
      (BodyCallShared.accept construct callbackConstruct fallback)
      (BodyCallShared.charge construct callbackConstruct fallback _ _)) state

theorem adopt_keeps_cut (world : OrderedDependencyStore.Store (Equation Output) size)
    (limit : Nat) (call : Call) :
    (adopt construct callbackConstruct fallback world limit call (Owner := Owner) (clients := clients)).execution =
      some ⟨call, call.2.1.pending.map (fun loan => (call.2.1.accepted, loan)), 0, .active⟩ ∧
      pending (adopt construct callbackConstruct fallback world limit call (Owner := Owner) (clients := clients)) =
        call.2.1.pending.map (fun loan => (call.2.1.accepted, loan)) := ⟨rfl, rfl⟩

theorem release_adopt (world : OrderedDependencyStore.Store (Equation Output) size)
    (limit : Nat) (call : Call) :
    (release construct callbackConstruct fallback
      (adopt construct callbackConstruct fallback world limit call (Owner := Owner) (clients := clients))).1 =
      some call := by
  cases held : call.2.1.pending <;> simp [release, adopt, BodyCallShared.retainedRelease, BodyCallShared.retainedAdopt, held]

theorem release_keeps_delivery (state : Cfg) :
    (release construct callbackConstruct fallback state).2.execution = none ∧
      (release construct callbackConstruct fallback state).2.context = state.context ∧
      (release construct callbackConstruct fallback state).2.delivery = state.delivery := ⟨rfl, rfl, rfl⟩

/-- Even after capture, handback keeps the exact source frontier and source
operation account. Only acknowledgment/context accounting may advance. -/
theorem release_keeps_source (state : Cfg)
    (execution : Execution Call Borrowed Empty Loan) (attached : state.execution = some execution)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback execution.producer) :
    ∃ call, (release construct callbackConstruct fallback state).1 = some call ∧
      call.2.2.computation.1 = execution.producer.2.2.computation.1 ∧
      BodyCallProtocol.stateView construct callbackConstruct fallback call.2.2.computation.2 =
        BodyCallProtocol.stateView construct callbackConstruct fallback execution.producer.2.2.computation.2 := by
  unfold release BodyCallShared.retainedRelease
  rw [attached]
  simp only [Option.map_some]
  split
  next ready =>
    obtain ⟨loan, held⟩ := Option.isSome_iff_exists.mp (Bool.and_eq_true_iff.mp ready).2
    have shape := coherent loan held
    exact ⟨_, rfl, BodyCallAdmission.pending_resume_keeps_source construct callbackConstruct fallback 0
      (BodyCallShared.accept construct callbackConstruct fallback)
      (BodyCallShared.charge construct callbackConstruct fallback _ _) execution.producer loan shape.1 held⟩
  next waiting => exact ⟨_, rfl, rfl, rfl⟩

theorem release_captured (state : Cfg)
    (execution : Execution Call Borrowed Empty Loan) (attached : state.execution = some execution)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback authored items parameter execution.producer) :
    ∃ call, (release construct callbackConstruct fallback state).1 = some call ∧
      BodyCallAdmission.captured construct callbackConstruct fallback authored items parameter call := by
  unfold release BodyCallShared.retainedRelease
  rw [attached]
  simp only [Option.map_some]
  split
  · exact ⟨_, rfl, BodyCallAdmission.resume_captured construct callbackConstruct fallback 0 1
      (BodyCallShared.accept construct callbackConstruct fallback)
      (BodyCallShared.charge construct callbackConstruct fallback _ _) authored items parameter execution.producer safe⟩
  · exact ⟨_, rfl, safe⟩

variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]

/-- Current permission and the captured dependency stamp gate both new source
progress and publication from a buffer. This does not discharge authority. -/
def compatible (captured : OrderedDependencyStore.Store (Equation Output) size) : Bool :=
  OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp captured reader) &&
    decide (FrameUpdate point.authority required)

local notation "sourceStep" => BodyCallShared.step construct callbackConstruct fallback authority before current reader point required
local notation "sourceCapture" => BodyCallShared.capture construct callbackConstruct fallback
local notation "gate" => compatible authority current reader point required

/-- The same existing log engine performs all shared requests. Source quantum
and admission/delivery operations remain separate units. -/
def advance [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (state : Cfg) : Cfg :=
  Accounting.runActions (sourceStep quantum) sourceCapture capacity gate actions state

def view (state : Cfg) (call : Call) : List (List Output) :=
  state.delivery.log.rows.flatMap (·.2) ++
    (pending state).toList.flatMap (fun loan => loan.2.2.1.rows) ++
      BodyCallShared.residualRows construct callbackConstruct fallback call

theorem adopt_view (limit : Nat) (call : Call)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback call) :
    call.2.2.context.1 ++ view construct callbackConstruct fallback
        (adopt construct callbackConstruct fallback before limit call (Owner := Owner) (clients := clients)) call =
      BodyCallOwned.view construct callbackConstruct fallback call.2.2 := by
  have partition := BodyCallShared.published_residual_eq_view construct callbackConstruct fallback call coherent
  cases held : call.2.1.pending <;>
    simpa [view, adopt, BodyCallShared.retainedAdopt, pending, Cursor.SharedOccurrenceLog.initial, BodyCallShared.publishedRows,
      held, List.append_assoc] using partition

private theorem path_residual (quantum : Nat) (items : List Input) (parameter : Nat)
    {first last : Call} {returns : List Borrowed}
    (path : ProducerPath (sourceStep quantum) first returns last)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter first)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback first) :
    returns.flatMap (fun loan => loan.2.2.1.rows) ++
        BodyCallShared.residualRows construct callbackConstruct fallback last =
      BodyCallShared.residualRows construct callbackConstruct fallback first := by
  obtain ⟨nextCoherent, rows⟩ := BodyCallShared.path_rows construct callbackConstruct fallback
    authority before current reader point required quantum path coherent
  have nextSafe := BodyCallShared.path_preserves_captured construct callbackConstruct fallback
    authority before current reader point required quantum items parameter path safe
  have initialView := BodyCallShared.published_residual_eq_view construct callbackConstruct fallback first coherent
  have finalView := BodyCallShared.published_residual_eq_view construct callbackConstruct fallback last nextCoherent
  rw [rows, List.append_assoc] at finalView
  apply List.append_cancel_left (as := BodyCallShared.publishedRows construct callbackConstruct fallback first)
  exact (finalView.trans nextSafe.2.2).trans (initialView.trans safe.2.2).symm

set_option backward.isDefEq.respectTransparency false in
theorem pump_view (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (items : List Input) (parameter : Nat) (state : Cfg)
    (execution target : Execution Call Borrowed Empty Loan)
    (attached : state.execution = some execution)
    (nextAttached : (pump (sourceStep quantum) sourceCapture capacity gate state).2.execution = some target)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback execution.producer) :
    view construct callbackConstruct fallback
        (pump (sourceStep quantum) sourceCapture capacity gate state).2 target.producer =
      view construct callbackConstruct fallback state execution.producer := by
  obtain ⟨actual, retained, path⟩ := pump_producer_path (sourceStep quantum) sourceCapture capacity gate state execution attached
  have same : actual = target := Option.some.inj (retained.symm.trans nextAttached)
  subst actual
  have row := path_residual construct callbackConstruct fallback authority before current reader point required quantum
    items parameter path safe coherent
  have conserved := pump_conservation (fun (loan : Borrowed) => loan.2.2.1.rows)
    (fun (stored : BodyCallShared.Stored (Output := Output)) => stored.2)
    (sourceStep quantum) sourceCapture capacity gate
    (by intro loan stored captured; cases captured; rfl) state
  have flat := congrArg (List.flatMap id) conserved
  simp only [List.flatMap_append, List.flatMap_map, id_eq] at flat
  unfold view
  rw [pump_rows, List.flatMap_append]
  calc
    _ = state.delivery.log.rows.flatMap (·.2) ++
        ((admitted (pump (sourceStep quantum) sourceCapture capacity gate state).1).flatMap (·.2) ++
          (pending (pump (sourceStep quantum) sourceCapture capacity gate state).2).toList.flatMap
            (fun loan => loan.2.2.1.rows)) ++ BodyCallShared.residualRows construct callbackConstruct fallback target.producer := by
          simp only [List.append_assoc]
    _ = state.delivery.log.rows.flatMap (·.2) ++
        ((pending state).toList.flatMap (fun loan => loan.2.2.1.rows) ++
          (returned (pump (sourceStep quantum) sourceCapture capacity gate state).1).flatMap
            (fun loan => loan.2.2.1.rows)) ++ BodyCallShared.residualRows construct callbackConstruct fallback target.producer := by rw [← flat]
    _ = _ := by simp only [List.append_assoc]; rw [row]

private theorem delivery_view [DecidableEq Output] [DecidableEq Owner]
    (state : Cfg) (call : Call) (client : Fin clients) (owner : Owner) :
    view construct callbackConstruct fallback (deliver gate state client owner).2 call =
      view construct callbackConstruct fallback state call := by
  have rows : (deliver gate state client owner).2.delivery.log.rows = state.delivery.log.rows := by
    unfold deliver
    split
    · cases reply : Cursor.SharedOccurrenceLog.peek state.delivery.log client <;>
        simp [Cursor.SharedOccurrenceOwnership.advance, Cursor.SharedOccurrenceOwnership.acknowledge,
          Cursor.SharedOccurrenceOwnership.prepare, Cursor.SharedOccurrenceLog.pull,
          Cursor.SharedOccurrenceLog.setPosition, reply]
    · rfl
  simp only [view, rows, pending, delivery_preserves_complete_execution]

/-- Arbitrary finite shared requests preserve the actual source, loan shape
and exact ordered suffix partition, including refusals and delivery retries. -/
theorem advance_source [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (state : Cfg)
    (execution : Execution Call Borrowed Empty Loan) (attached : state.execution = some execution)
    (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback execution.producer) :
    ∃ target, (advance construct callbackConstruct fallback authority before current reader point required
        quantum capacity actions state).execution = some target ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter target.producer ∧
      BodyCallShared.Coherent construct callbackConstruct fallback target.producer ∧
      view construct callbackConstruct fallback
          (advance construct callbackConstruct fallback authority before current reader point required
            quantum capacity actions state) target.producer =
        view construct callbackConstruct fallback state execution.producer := by
  induction actions generalizing state execution with
  | nil => exact ⟨execution, attached, safe, coherent, rfl⟩
  | cons action rest ih =>
      cases action with
      | pump =>
          obtain ⟨next, retained, path⟩ := pump_producer_path (sourceStep quantum) sourceCapture capacity gate state execution attached
          have safeNext := BodyCallShared.path_preserves_captured construct callbackConstruct fallback authority
            before current reader point required quantum items parameter path safe
          have coherentNext := (BodyCallShared.path_rows construct callbackConstruct fallback authority
            before current reader point required quantum path coherent).1
          obtain ⟨target, final, safeFinal, coherentFinal, same⟩ := ih _ next retained safeNext coherentNext
          exact ⟨target, final, safeFinal, coherentFinal, same.trans
            (pump_view construct callbackConstruct fallback authority before current reader point required quantum capacity
              items parameter state execution next attached retained safe coherent)⟩
      | deliver client owner =>
          have retained := (delivery_preserves_complete_execution gate state client owner).trans attached
          obtain ⟨target, final, safeFinal, coherentFinal, same⟩ := ih _ execution retained safe coherent
          exact ⟨target, final, safeFinal, coherentFinal, same.trans
            (delivery_view construct callbackConstruct fallback authority current reader point required state execution.producer client owner)⟩

/-- An ordinary owned prefix is kept outside the new multicast log. The actual
pending loan and future residual enter exactly once at this nonfresh cut. -/
theorem adopt_advance_source [DecidableEq Output] [DecidableEq Owner]
    (quantum limit : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (call : Call)
    (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter call)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback call) :
    let final := advance construct callbackConstruct fallback authority before current reader point required
      quantum capacity actions (adopt construct callbackConstruct fallback before limit call (Owner := Owner) (clients := clients))
    ∃ target, final.execution = some target ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter target.producer ∧
      BodyCallShared.Coherent construct callbackConstruct fallback target.producer ∧
      call.2.2.context.1 ++ view construct callbackConstruct fallback final target.producer =
        source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  obtain ⟨target, attached, safeFinal, coherentFinal, same⟩ := advance_source construct callbackConstruct fallback
    authority before current reader point required quantum capacity actions
    (adopt construct callbackConstruct fallback before limit call (Owner := Owner) (clients := clients)) _ rfl
    items parameter safe coherent
  refine ⟨target, attached, safeFinal, coherentFinal, ?_⟩
  rw [same, adopt_view construct callbackConstruct fallback before limit call coherent]
  exact safe.2.2

/-- The handback readout uses the independently proved source invariant. It
retains the full Call, and all four modes use their existing grade licenses. -/
theorem advance_release_license [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (state : Cfg)
    (execution : Execution Call Borrowed Empty Loan) (attached : state.execution = some execution)
    (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback execution.producer) :
    ∃ call, (release construct callbackConstruct fallback
        (advance construct callbackConstruct fallback authority before current reader point required
          quantum capacity actions state)).1 = some call ∧
      ∃ earned : BodyCallAdmission.quiet construct callbackConstruct fallback call.2.2,
        ∀ requested interface answers,
          (BodyCallAdmission.admit construct callbackConstruct fallback requested interface
            (OrderedDependencyStore.query before reader) items parameter call earned).1 = some answers →
          answers = source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter ∧
            ConventionAllows requested answers.length := by
  obtain ⟨target, final, safeFinal, _, _⟩ := advance_source construct callbackConstruct fallback
    authority before current reader point required quantum capacity actions state execution attached items parameter safe coherent
  obtain ⟨call, handedBack, safeBack⟩ := release_captured construct callbackConstruct fallback _ target final
    (OrderedDependencyStore.query before reader) items parameter safeFinal
  exact ⟨call, handedBack, safeBack.2.1, fun requested interface answers admitted =>
    BodyCallAdmission.admit_license construct callbackConstruct fallback requested interface _ items parameter call
      safeBack.2.1 safeBack.2.2 answers admitted⟩

/-- Splitting keeps the same source quantum, captured/current context and
permission. It does not combine grants across external context changes. -/
theorem advance_split [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (first second : List (Accounting.Action Owner clients)) (state : Cfg) :
    advance construct callbackConstruct fallback authority before current reader point required quantum capacity (first ++ second) state =
      advance construct callbackConstruct fallback authority before current reader point required quantum capacity second
        (advance construct callbackConstruct fallback authority before current reader point required quantum capacity first state) :=
  Accounting.runActions_append _ _ _ _ _ _ _

theorem denied_keeps_cut [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (state : Cfg) (client : Fin clients) (owner : Owner)
    (denied : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp state.context reader) = false ∨
      ¬ FrameUpdate point.authority required) :
    pump (sourceStep quantum) sourceCapture capacity gate state =
        (if state.execution.isNone then .detached else .contextRefused, state) ∧
      deliver gate state client owner = (.contextRefused, state) := by
  have no : gate state.context = false := by
    rcases denied with stale | revoked <;> simp [compatible, *]
  constructor
  · cases attached : state.execution <;> simp [pump, attached, no]
  · simp [deliver, no]

/-- The entry invariant is constructed from actual ordinary resumptions,
then transported through the shared engine from their exact retained cut. -/
theorem scheduled_handoff_source [DecidableEq Output] [DecidableEq Owner]
    (charges : ∀ quantum (consumer : Context → Loan → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer))
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (quantum limit : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallAdmission.schedule construct callbackConstruct fallback charges grants
      (BodyCallAdmission.openCall construct callbackConstruct fallback (OrderedDependencyStore.query before reader) items parameter context)
    let final := advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback before limit owned (Owner := Owner) (clients := clients))
    ∃ target, final.execution = some target ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter target.producer ∧
      BodyCallShared.Coherent construct callbackConstruct fallback target.producer ∧
      owned.2.2.context.1 ++ view construct callbackConstruct fallback final target.producer =
        source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  exact adopt_advance_source construct callbackConstruct fallback authority before current reader point required quantum limit capacity
    actions _ items parameter
    (BodyCallAdmission.schedule_open_captured construct callbackConstruct fallback charges grants _ items parameter context)
    (schedule_coherent construct callbackConstruct fallback charges grants _ items parameter context)

theorem completed_residual (call : Call)
    (earned : BodyCallAdmission.quiet construct callbackConstruct fallback call.2.2)
    (completed : BodyCallAdmission.complete construct callbackConstruct fallback call = true) :
    BodyCallShared.residualRows construct callbackConstruct fallback call = [] := by
  obtain ⟨finished, empty⟩ := BodyCallAdmission.complete_cut construct callbackConstruct fallback call completed
  have noLoan : call.2.1.pending = none := by
    cases held : call.2.1.pending with
    | none => rfl
    | some loan => simp [BodyCallAdmission.complete, held] at completed
  simp [BodyCallShared.residualRows, noLoan, BodyCallProtocol.unacceptedRows, empty, earned finished]

/-- A completed acknowledged shared suffix combines with the earlier ordinary
prefix, preserving multiplicity. The multicast log alone need not be the whole
source when adoption happened after earlier ordinary acknowledgments. -/
theorem completed_handoff_source [DecidableEq Output] [DecidableEq Owner]
    (quantum limit : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (call : Call) (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter call)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback call)
    (target : Execution Call Borrowed Empty Loan)
    (attached : (advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback before limit call (Owner := Owner) (clients := clients))).execution = some target)
    (noLoan : pending (advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback before limit call (Owner := Owner) (clients := clients))) = none)
    (completed : BodyCallAdmission.complete construct callbackConstruct fallback target.producer = true) :
    call.2.2.context.1 ++ (advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback before limit call (Owner := Owner) (clients := clients))).delivery.log.rows.flatMap (·.2) =
      source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  obtain ⟨actual, retained, safeFinal, _, partition⟩ := adopt_advance_source construct callbackConstruct fallback
    authority before current reader point required quantum limit capacity actions call items parameter safe coherent
  have same : actual = target := Option.some.inj (retained.symm.trans attached)
  subst actual
  simpa [view, noLoan, completed_residual construct callbackConstruct fallback target.producer safeFinal.2.1 completed] using partition

theorem retirement_commutes [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (state : Cfg)
    (retired other : Fin clients) (position : Nat) (distinct : other ≠ retired)
    (live : state.delivery.log.positions other = some position)
    (spares : Accounting.sparesRetired retired actions) :
    advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions (retireConsumer state retired) =
      retireConsumer (advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions state) retired :=
  Accounting.runActions_after_retained_demand (sourceStep quantum) sourceCapture capacity gate actions state
    retired other position distinct live spares

/-- This license starts from authored entry, includes arbitrary ordinary
callback grants, shared requests, and the actual acknowledgment-only handback. -/
theorem scheduled_release_license [DecidableEq Output] [DecidableEq Owner]
    (charges : ∀ quantum (consumer : Context → Loan → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer))
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (quantum limit : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallAdmission.schedule construct callbackConstruct fallback charges grants
      (BodyCallAdmission.openCall construct callbackConstruct fallback (OrderedDependencyStore.query before reader) items parameter context)
    let final := advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback before limit owned (Owner := Owner) (clients := clients))
    ∃ call, (release construct callbackConstruct fallback final).1 = some call ∧
      ∃ earned : BodyCallAdmission.quiet construct callbackConstruct fallback call.2.2,
        ∀ requested interface answers,
          (BodyCallAdmission.admit construct callbackConstruct fallback requested interface
            (OrderedDependencyStore.query before reader) items parameter call earned).1 = some answers →
          answers = source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter ∧
            ConventionAllows requested answers.length := by
  exact advance_release_license construct callbackConstruct fallback authority before current reader point required quantum capacity actions
    _ _ rfl items parameter
    (BodyCallAdmission.schedule_open_captured construct callbackConstruct fallback charges grants _ items parameter context)
    (schedule_coherent construct callbackConstruct fallback charges grants _ items parameter context)

#print axioms scheduled_release_license
#print axioms resume_coherent
#print axioms schedule_coherent
#print axioms scheduled_handoff_source
#print axioms completed_residual
#print axioms completed_handoff_source
#print axioms retirement_commutes
#print axioms adopt_keeps_cut
#print axioms release_adopt
#print axioms release_keeps_delivery
#print axioms release_keeps_source
#print axioms release_captured
#print axioms adopt_view
#print axioms pump_view
#print axioms advance_source
#print axioms adopt_advance_source
#print axioms advance_release_license
#print axioms advance_split
#print axioms denied_keeps_cut


end BodyCallShared.Handoff

namespace BodyCallShared.Weighted.Authored.Handoff

open Mettapedia.Algebra.SharedCoefficientLedger
open Cursor.ProducerOccurrenceLog
open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory

variable {Input Output Weight Context Owner : Type} [Semiring Weight] {clients size : Nat}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (attachment : BodyCall.WeightedSource.Attachment Input Output Weight)

local notation "selected" => BodyCallWeighted.Authored.selection attachment
local notation "Row" => BodyCall.WeightedSource.Row Output Weight
local notation "Call" => Weighted.Call construct callbackConstruct fallback selected (Context := List Row × Context)
local notation "Loan" => Weighted.Loan construct callbackConstruct fallback selected
local notation "Borrowed" => Weighted.Borrowed construct callbackConstruct fallback selected
local notation "Cfg" => Weighted.Configuration construct callbackConstruct fallback selected
  (Context := List Row × Context) (size := size) Owner clients
local notation "Source" => BodyCallWeighted.Authored.stateView construct callbackConstruct fallback attachment
local notation "Residual" => Authored.residual construct callbackConstruct fallback attachment
local notation "loanRows" => Authored.loanRows construct callbackConstruct fallback attachment
local notation "storedRows" => Authored.storedRows (Output := Output) (Weight := Weight)

def resume (quantum allowance : Nat) (consumer : Context → Loan → Bool × Context) (call : Call) : Call :=
  BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selected quantum allowance
    (BodyCallWeighted.Authored.reader construct callbackConstruct fallback attachment consumer) call

def accept (context : Context) (_ : Loan) := (true, context)

def refuse (context : Context) (_ : Loan) := (false, context)


/-- The same cold handoff used by plain source calls, now retaining the full
sparse loan and its prior authored weighted prefix. -/
def adopt (world : OrderedDependencyStore.Store (Equation Output) size) (limit : Nat) (call : Call) : Cfg :=
  BodyCallShared.retainedAdopt world limit call

def acknowledge := resume construct callbackConstruct fallback attachment 0 1
  (accept construct callbackConstruct fallback attachment (Context := Context))

def release (state : Cfg) : Option Call × Cfg :=
  BodyCallShared.retainedRelease (acknowledge construct callbackConstruct fallback attachment) state

def Safe (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call) : Prop :=
  BodyCallWeighted.Authored.Captured construct callbackConstruct fallback attachment authored items parameter call ∧
    BodyCallWeighted.Compact.Attachment.Origin construct callbackConstruct fallback selected call.2.2.computation.2 ∧
    Weighted.Coherent construct callbackConstruct fallback selected call

theorem resume_safe (quantum allowance : Nat) (consumer : Context → Loan → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call)
    (safe : Safe construct callbackConstruct fallback attachment authored items parameter call) :
    Safe construct callbackConstruct fallback attachment authored items parameter
      (resume construct callbackConstruct fallback attachment quantum allowance consumer call) := by
  refine ⟨BodyCallWeighted.Authored.resume_captured construct callbackConstruct fallback attachment quantum allowance consumer
      authored items parameter call safe.1,
    BodyCallWeighted.Compact.Attachment.resume_origin construct callbackConstruct fallback selected quantum allowance
      (BodyCallWeighted.Authored.reader construct callbackConstruct fallback attachment consumer) call safe.2.1, ?_⟩
  unfold resume BodyCallWeighted.Compact.Attachment.resumeCallSource resumeCall
  cases stopped : call.2.1.terminal with
  | some reason => exact safe.2.2
  | none =>
      simpa [Weighted.Coherent, BodyCallWeighted.Compact.Attachment.ownedProvider] using
        BodyCallShared.retainedCallbacks_coherent
          (BodyCallWeighted.Compact.Attachment.SparseProvider construct callbackConstruct fallback selected)
          (fun _ _ => 1) quantum
          (BodyCallWeighted.Compact.Attachment.isReturn construct callbackConstruct fallback selected)
          (BodyCallWeighted.Compact.Attachment.rearm construct callbackConstruct fallback selected)
          (BodyCallWeighted.Compact.Attachment.consume construct callbackConstruct fallback selected
            (BodyCallWeighted.Authored.reader construct callbackConstruct fallback attachment consumer))
          (BodyCallWeighted.Compact.Attachment.terminalAfter construct callbackConstruct fallback selected)
          (fun _ _ => 1) allowance call.2.1.accepted call.2.1.pending call.2.2
          (fun loan held => (safe.2.2 loan held).2)

/-- Construct the source/loan invariant from entry and arbitrary actual
callback grants; no weighted-answer equality is an input. -/
theorem schedule_safe
    (grants : List (BodyCallWeighted.Authored.Grant construct callbackConstruct fallback attachment (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    Safe construct callbackConstruct fallback attachment authored items parameter
      (BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
        (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
        (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected authored items parameter ([], context))) := by
  have keeps : ∀ call, Safe construct callbackConstruct fallback attachment authored items parameter call →
      Safe construct callbackConstruct fallback attachment authored items parameter
        (BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
          (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants) call) := by
    induction grants with
    | nil => exact fun _ safe => safe
    | cons grant rest ih =>
        exact fun call safe => ih _ (resume_safe construct callbackConstruct fallback attachment grant.1 grant.2.1 grant.2.2 authored items parameter call safe)
  exact keeps _ ⟨BodyCallWeighted.Authored.open_captured construct callbackConstruct fallback attachment authored items parameter context,
    BodyCallWeighted.Compact.Attachment.open_origin construct callbackConstruct fallback selected authored items parameter ([], context),
    by intro loan held; cases held⟩

theorem release_adopt (world : OrderedDependencyStore.Store (Equation Output) size) (limit : Nat) (call : Call) :
    (release construct callbackConstruct fallback attachment
      (adopt construct callbackConstruct fallback attachment world limit call (Owner := Owner) (clients := clients))).1 = some call := by
  cases held : call.2.1.pending <;>
    simp [release, adopt, BodyCallShared.retainedRelease, BodyCallShared.retainedAdopt, held]

/-- Acknowledgment uses the existing authored collector. It adds exactly this
loan's coefficient word and keeps every source frame, factor and firing ordinal. -/
theorem acknowledge_cut (call : Call) (coherent : Weighted.Coherent construct callbackConstruct fallback selected call)
    (loan : Loan) (held : call.2.1.pending = some loan) :
    let next := acknowledge construct callbackConstruct fallback attachment call
    next.2.1.pending = none ∧ next.2.1.accepted = call.2.1.accepted + 1 ∧
      next.2.2.context.2.1 = call.2.2.context.2.1 ++ loanRows (call.2.1.accepted, loan) ∧
      next.2.2.computation.1 = call.2.2.computation.1 ∧
      Source next.2.2.computation.2 = Source call.2.2.computation.2 ∧ Residual next = Residual call := by
  have shape := coherent loan held
  cases final : BodyCallWeighted.Compact.Attachment.terminalAfter construct callbackConstruct fallback selected loan <;>
    simp [acknowledge, resume, BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall,
      shape.1, held, fromCallbacks, BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider,
      shape.2.1, shape.2.2, BodyCallWeighted.Compact.Attachment.consume, BodyCallWeighted.Authored.reader,
      accept, final, Authored.residual, BodyCallWeighted.Authored.unaccepted, BodyCallWeighted.Authored.stateView,
      BodyCallWeighted.Authored.moveView, BodyCallWeighted.Compact.Attachment.rearm, Authored.loanRows,
      BodyCall.WeightedSource.emitted, BodyCall.Move.rows]

theorem release_safe (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (state : Cfg)
    (execution : Execution Call Borrowed Empty Loan) (attached : state.execution = some execution)
    (safe : Safe construct callbackConstruct fallback attachment authored items parameter execution.producer) :
    ∃ call, (release construct callbackConstruct fallback attachment state).1 = some call ∧
      Safe construct callbackConstruct fallback attachment authored items parameter call := by
  unfold release BodyCallShared.retainedRelease
  rw [attached]
  simp only [Option.map_some]
  split
  · exact ⟨_, rfl, resume_safe construct callbackConstruct fallback attachment 0 1
      (accept construct callbackConstruct fallback attachment) authored items parameter execution.producer safe⟩
  · exact ⟨_, rfl, safe⟩

theorem release_keeps_source (state : Cfg) (execution : Execution Call Borrowed Empty Loan)
    (attached : state.execution = some execution)
    (coherent : Weighted.Coherent construct callbackConstruct fallback selected execution.producer) :
    ∃ call, (release construct callbackConstruct fallback attachment state).1 = some call ∧
      call.2.2.computation.1 = execution.producer.2.2.computation.1 ∧
      Source call.2.2.computation.2 = Source execution.producer.2.2.computation.2 ∧
      (release construct callbackConstruct fallback attachment state).2.delivery = state.delivery := by
  unfold release BodyCallShared.retainedRelease
  rw [attached]
  simp only [Option.map_some]
  split
  next ready =>
    obtain ⟨loan, held⟩ := Option.isSome_iff_exists.mp (Bool.and_eq_true_iff.mp ready).2
    have kept := acknowledge_cut construct callbackConstruct fallback attachment execution.producer coherent loan held
    exact ⟨_, rfl, kept.2.2.2.1, kept.2.2.2.2.1, rfl⟩
  next waiting => exact ⟨_, rfl, rfl, rfl, rfl⟩

variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]

local notation "gate" => BodyCallShared.Handoff.compatible authority current reader point required

/-- New source progress and buffered publication use the same current gate.
The actual weighted reader is retained across acknowledgments and handback. -/
def poll (quantum : Nat) (call : Call) : Call :=
  if gate before then resume construct callbackConstruct fallback attachment quantum 1
    (refuse construct callbackConstruct fallback attachment) call else call

def step (quantum : Nat) : Call → Weighted.Move construct callbackConstruct fallback selected (Context := List Row × Context) :=
  BodyCallShared.retainedStep (Weighted.inspect construct callbackConstruct fallback selected)
    (acknowledge construct callbackConstruct fallback attachment)
    (poll construct callbackConstruct fallback attachment authority before current reader point required quantum)

private theorem poll_safe (quantum : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call) (safe : Safe construct callbackConstruct fallback attachment authored items parameter call) :
    Safe construct callbackConstruct fallback attachment authored items parameter
      (poll construct callbackConstruct fallback attachment authority before current reader point required quantum call) := by
  unfold poll
  split
  · exact resume_safe construct callbackConstruct fallback attachment quantum 1
      (refuse construct callbackConstruct fallback attachment) authored items parameter call safe
  · exact safe

theorem step_safe (quantum : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call) (safe : Safe construct callbackConstruct fallback attachment authored items parameter call) :
    Safe construct callbackConstruct fallback attachment authored items parameter
      (step construct callbackConstruct fallback attachment authority before current reader point required quantum call).next := by
  unfold step BodyCallShared.retainedStep
  split
  · simpa only [Weighted.inspect_next] using safe
  · cases held : call.2.1.pending with
    | some loan =>
        exact resume_safe construct callbackConstruct fallback attachment 0 1
          (accept construct callbackConstruct fallback attachment) authored items parameter call safe
    | none =>
        rw [Weighted.inspect_next]
        unfold poll
        split
        · exact resume_safe construct callbackConstruct fallback attachment quantum 1
            (refuse construct callbackConstruct fallback attachment) authored items parameter call safe
        · exact safe

theorem step_rows (quantum : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call) (safe : Safe construct callbackConstruct fallback attachment authored items parameter call) :
    (step construct callbackConstruct fallback attachment authority before current reader point required quantum call).returns.flatMap loanRows ++
        Residual (step construct callbackConstruct fallback attachment authority before current reader point required quantum call).next = Residual call := by
  unfold step BodyCallShared.retainedStep
  split
  · rw [Weighted.inspect_next]
    have empty : call.2.1.pending = none := by
      cases held : call.2.1.pending with
      | none => rfl
      | some loan => simp [(safe.2.2 loan held).1] at ‹call.2.1.terminal.isSome = true›
    simpa [Authored.residual, empty] using
      Authored.inspect_rows construct callbackConstruct fallback attachment call safe.2.2
  · cases held : call.2.1.pending with
    | some loan =>
        simpa only [ProducerOutcome.returns, ProducerOutcome.next, List.flatMap_nil, List.nil_append] using
          (acknowledge_cut construct callbackConstruct fallback attachment call safe.2.2 loan held).2.2.2.2.2
    | none =>
        rw [Weighted.inspect_next]
        have coherent := (poll_safe construct callbackConstruct fallback attachment authority before current reader point required
          quantum authored items parameter call safe).2.2
        rw [Authored.inspect_rows construct callbackConstruct fallback attachment _ coherent]
        unfold poll
        split
        · have identical : BodyCallWeighted.Authored.reader construct callbackConstruct fallback attachment
              (refuse construct callbackConstruct fallback attachment (Context := Context)) =
              Weighted.refuse construct callbackConstruct fallback selected := by
            funext context loan
            cases context
            rfl
          unfold resume
          rw [identical]
          simpa only [Authored.residual, held] using
            Authored.poll_view construct callbackConstruct fallback attachment quantum call
              (by simpa using ‹¬call.2.1.terminal.isSome = true›) held safe.1.2.1
        · simp [Authored.residual, held]

/-- Every newly exposed factor image is licensed by the actual source loan;
failed and sibling activations cannot be relabelled as return contributions. -/
theorem step_factor_origin (quantum : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call) (safe : Safe construct callbackConstruct fallback attachment authored items parameter call) :
    ∀ borrowed ∈ (step construct callbackConstruct fallback attachment authority before current reader point required quantum call).returns,
      Weighted.Authentic construct callbackConstruct fallback selected (Weighted.image construct callbackConstruct fallback selected borrowed) := by
  unfold step BodyCallShared.retainedStep
  split
  · exact Weighted.inspect_origin construct callbackConstruct fallback selected call safe.2.1 safe.2.2
  · cases held : call.2.1.pending with
    | some loan => simp [ProducerOutcome.returns]
    | none =>
        have nextSafe := poll_safe construct callbackConstruct fallback attachment authority before current reader point required quantum
          authored items parameter call safe
        exact Weighted.inspect_origin construct callbackConstruct fallback selected _ nextSafe.2.1 nextSafe.2.2

theorem adopt_pending_origin (world : OrderedDependencyStore.Store (Equation Output) size) (limit : Nat)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call)
    (safe : Safe construct callbackConstruct fallback attachment authored items parameter call) :
    ∀ borrowed ∈ (pending (adopt construct callbackConstruct fallback attachment world limit call (Owner := Owner) (clients := clients))).toList,
      Weighted.Authentic construct callbackConstruct fallback selected (Weighted.image construct callbackConstruct fallback selected borrowed) := by
  intro borrowed present
  have origin := Weighted.inspect_origin construct callbackConstruct fallback selected call safe.2.1 safe.2.2
  rw [Weighted.inspect_returns construct callbackConstruct fallback selected call safe.2.2] at origin
  exact origin borrowed (by simpa [pending, adopt, BodyCallShared.retainedAdopt] using present)

local notation "sourceStep" => step construct callbackConstruct fallback attachment authority before current reader point required
local notation "sourceCapture" => Weighted.capture construct callbackConstruct fallback selected

private theorem path_rows (quantum : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    {first last : Call} {returns : List Borrowed} (path : ProducerPath (sourceStep quantum) first returns last)
    (safe : Safe construct callbackConstruct fallback attachment authored items parameter first) :
    Safe construct callbackConstruct fallback attachment authored items parameter last ∧
      returns.flatMap loanRows ++ Residual last = Residual first := by
  induction path with
  | refl => exact ⟨safe, by simp⟩
  | @next first moved later returns transition tail ih =>
      have nextSafe := step_safe construct callbackConstruct fallback attachment authority before current reader point required quantum
        authored items parameter first safe
      have rows := step_rows construct callbackConstruct fallback attachment authority before current reader point required quantum
        authored items parameter first safe
      rw [transition] at nextSafe rows
      obtain ⟨finalSafe, remaining⟩ := ih nextSafe
      exact ⟨finalSafe, by simp only [List.flatMap_append, List.append_assoc]; rw [remaining, rows]⟩

def advance [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (quantum : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Accounting.Action Owner clients)) (state : Cfg) :=
  Accounting.runActions (sourceStep quantum) sourceCapture capacity gate actions state

local notation "View" => Authored.view construct callbackConstruct fallback attachment

private theorem pump_view (quantum : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (items : List Input) (parameter : Nat) (state : Cfg) (execution target : Execution Call Borrowed Empty Loan)
    (attached : state.execution = some execution)
    (nextAttached : (pump (sourceStep quantum) sourceCapture capacity gate state).2.execution = some target)
    (safe : Safe construct callbackConstruct fallback attachment (OrderedDependencyStore.query before reader) items parameter execution.producer) :
    View (pump (sourceStep quantum) sourceCapture capacity gate state).2 target.producer = View state execution.producer := by
  obtain ⟨actual, retained, path⟩ := pump_producer_path (sourceStep quantum) sourceCapture capacity gate state execution attached
  have same : actual = target := Option.some.inj (retained.symm.trans nextAttached)
  subst actual
  have rows := (path_rows construct callbackConstruct fallback attachment authority before current reader point required quantum
    (OrderedDependencyStore.query before reader) items parameter path safe).2
  have conserved := pump_conservation loanRows storedRows (sourceStep quantum) sourceCapture capacity gate
    (by intro loan stored captured; cases captured; exact Authored.capture_rows construct callbackConstruct fallback attachment loan) state
  have flat := congrArg (List.flatMap id) conserved
  simp only [List.flatMap_append, List.flatMap_map, id_eq] at flat
  unfold Authored.view
  rw [pump_rows, List.flatMap_append]
  calc
    _ = state.delivery.log.rows.flatMap storedRows ++
        ((admitted (pump (sourceStep quantum) sourceCapture capacity gate state).1).flatMap storedRows ++
          (pending (pump (sourceStep quantum) sourceCapture capacity gate state).2).toList.flatMap loanRows) ++ Residual target.producer := by
          simp only [List.append_assoc]
    _ = state.delivery.log.rows.flatMap storedRows ++
        ((pending state).toList.flatMap loanRows ++
          (returned (pump (sourceStep quantum) sourceCapture capacity gate state).1).flatMap loanRows) ++ Residual target.producer := by rw [← flat]
    _ = _ := by simp only [List.append_assoc]; rw [rows]

private theorem delivery_view [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (state : Cfg) (call : Call) (client : Fin clients) (owner : Owner) :
    View (deliver gate state client owner).2 call = View state call := by
  have rows : (deliver gate state client owner).2.delivery.log.rows = state.delivery.log.rows := by
    unfold deliver
    split
    · cases reply : Cursor.SharedOccurrenceLog.peek state.delivery.log client <;>
        simp [Cursor.SharedOccurrenceOwnership.advance, Cursor.SharedOccurrenceOwnership.acknowledge,
          Cursor.SharedOccurrenceOwnership.prepare, Cursor.SharedOccurrenceLog.pull, Cursor.SharedOccurrenceLog.setPosition, reply]
    · rfl
  simp only [Authored.view, rows, pending, delivery_preserves_complete_execution]

theorem advance_source [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (quantum : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Accounting.Action Owner clients)) (state : Cfg)
    (execution : Execution Call Borrowed Empty Loan) (attached : state.execution = some execution)
    (items : List Input) (parameter : Nat)
    (safe : Safe construct callbackConstruct fallback attachment (OrderedDependencyStore.query before reader) items parameter execution.producer) :
    ∃ target, (advance construct callbackConstruct fallback attachment authority before current reader point required
        quantum capacity actions state).execution = some target ∧
      Safe construct callbackConstruct fallback attachment (OrderedDependencyStore.query before reader) items parameter target.producer ∧
      View (advance construct callbackConstruct fallback attachment authority before current reader point required
        quantum capacity actions state) target.producer = View state execution.producer := by
  induction actions generalizing state execution with
  | nil => exact ⟨execution, attached, safe, rfl⟩
  | cons action rest ih =>
      cases action with
      | pump =>
          obtain ⟨next, retained, path⟩ := pump_producer_path (sourceStep quantum) sourceCapture capacity gate state execution attached
          obtain ⟨nextSafe, _⟩ := path_rows construct callbackConstruct fallback attachment authority before current reader point required quantum
            (OrderedDependencyStore.query before reader) items parameter path safe
          obtain ⟨target, final, safeFinal, same⟩ := ih _ next retained nextSafe
          exact ⟨target, final, safeFinal, same.trans
            (pump_view construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
              items parameter state execution next attached retained safe)⟩
      | deliver client owner =>
          obtain ⟨target, final, safeFinal, same⟩ := ih _ execution
            ((delivery_preserves_complete_execution gate state client owner).trans attached) safe
          exact ⟨target, final, safeFinal, same.trans
            (delivery_view construct callbackConstruct fallback attachment authority current reader point required state execution.producer client owner)⟩

/-- The actual nonfresh authored collector supplies the weighted prefix. The
shared log captures its same sparse factors once; delivery creates none. -/
theorem scheduled_handoff_source [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (grants : List (BodyCallWeighted.Authored.Grant construct callbackConstruct fallback attachment (Context := Context)))
    (quantum limit : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Accounting.Action Owner clients)) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
      (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
      (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected
        (OrderedDependencyStore.query before reader) items parameter ([], context))
    let final := advance construct callbackConstruct fallback attachment authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients))
    ∃ target, final.execution = some target ∧
      Safe construct callbackConstruct fallback attachment (OrderedDependencyStore.query before reader) items parameter target.producer ∧
      owned.2.2.context.2.1 ++ View final target.producer =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
  dsimp only
  let owned := BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
    (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
    (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected
      (OrderedDependencyStore.query before reader) items parameter ([], context))
  have safe := schedule_safe construct callbackConstruct fallback attachment grants (OrderedDependencyStore.query before reader) items parameter context
  obtain ⟨target, final, nextSafe, same⟩ := advance_source construct callbackConstruct fallback attachment authority before current reader point required
    quantum capacity actions (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients)) _ rfl items parameter safe
  refine ⟨target, final, nextSafe, ?_⟩
  rw [same]
  have inspected := Authored.inspect_rows construct callbackConstruct fallback attachment owned safe.2.2
  rw [Weighted.inspect_returns construct callbackConstruct fallback selected owned safe.2.2] at inspected
  have balance : View (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients)) owned =
      BodyCallWeighted.Authored.unaccepted construct callbackConstruct fallback attachment owned.2.2.computation.2 := by
    simpa [Authored.view, adopt, BodyCallShared.retainedAdopt, pending, Cursor.SharedOccurrenceLog.initial,
      Option.toList_map, List.flatMap_map] using inspected
  rw [balance]
  exact safe.1.2.2

/-- All four completed calling modes are earned after this actual weighted
handoff and handback; a pending final loan is not treated as completion. -/
theorem scheduled_release_license [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (grants : List (BodyCallWeighted.Authored.Grant construct callbackConstruct fallback attachment (Context := Context)))
    (quantum limit : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Accounting.Action Owner clients)) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
      (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
      (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected
        (OrderedDependencyStore.query before reader) items parameter ([], context))
    let final := advance construct callbackConstruct fallback attachment authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients))
    ∃ call, (release construct callbackConstruct fallback attachment final).1 = some call ∧
      ∀ requested interface answers,
        (BodyCallWeighted.Authored.admit construct callbackConstruct fallback attachment requested interface
          (OrderedDependencyStore.query before reader) items parameter call).1 = some answers →
        answers = BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter ∧
          ConventionAllows requested answers.length := by
  dsimp only
  obtain ⟨target, attached, safe, _⟩ := scheduled_handoff_source construct callbackConstruct fallback attachment authority before current reader point required
    grants quantum limit capacity actions items parameter context (Owner := Owner) (clients := clients)
  obtain ⟨call, handback, safeBack⟩ := release_safe construct callbackConstruct fallback attachment
    (OrderedDependencyStore.query before reader) items parameter _ target attached safe
  exact ⟨call, handback, fun requested interface answers admitted =>
    BodyCallWeighted.Authored.admit_license construct callbackConstruct fallback attachment requested interface
      (OrderedDependencyStore.query before reader) items parameter call safeBack.1 answers admitted⟩

theorem denied_keeps_cut [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (quantum : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (state : Cfg) (client : Fin clients) (owner : Owner)
    (denied : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp state.context reader) = false ∨
      ¬ FrameUpdate point.authority required) :
    pump (sourceStep quantum) sourceCapture capacity gate state =
        (if state.execution.isNone then .detached else .contextRefused, state) ∧
      deliver gate state client owner = (.contextRefused, state) := by
  have no : gate state.context = false := by
    rcases denied with stale | revoked <;> simp [BodyCallShared.Handoff.compatible, *]
  constructor
  · cases attached : state.execution <;> simp [pump, attached, no]
  · simp [deliver, no]

/-- At an acknowledged finished cut, the stored suffix and the prior ordinary
weighted prefix are exactly the authored weighted meaning. -/
theorem completed_suffix_source [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (grants : List (BodyCallWeighted.Authored.Grant construct callbackConstruct fallback attachment (Context := Context)))
    (quantum limit : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Accounting.Action Owner clients)) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
      (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
      (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected
        (OrderedDependencyStore.query before reader) items parameter ([], context))
    let final := advance construct callbackConstruct fallback attachment authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients))
    ∀ target : Execution Call Borrowed Empty Loan, final.execution = some target → pending final = none →
      BodyCallWeighted.Compact.Attachment.complete construct callbackConstruct fallback selected target.producer = true →
      owned.2.2.context.2.1 ++ final.delivery.log.rows.flatMap storedRows =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
  intro owned final target attached noLoan finished
  obtain ⟨actual, retained, safe, partition⟩ := scheduled_handoff_source construct callbackConstruct fallback attachment authority
    before current reader point required grants quantum limit capacity actions items parameter context (Owner := Owner) (clients := clients)
  have same : actual = target := Option.some.inj (retained.symm.trans attached)
  subst actual
  have noPending : target.producer.2.1.pending = none := by
    cases held : target.producer.2.1.pending with
    | none => rfl
    | some loan => simp [BodyCallWeighted.Compact.Attachment.complete,
        BodyCallWeighted.Compact.Attachment.eraseCall, BodyCallAdmission.complete, held] at finished
  have empty := BodyCallWeighted.Authored.completed_unaccepted construct callbackConstruct fallback attachment target.producer
    safe.1.1.2.1 safe.1.2.1.2 finished
  dsimp only [owned, final] at noLoan ⊢
  simpa [Authored.view, noLoan, Authored.residual, noPending, empty] using partition

namespace History

open Mettapedia.GSLT.Core.InferenceControl.Recording
open Cursor.ProducerOccurrenceLog.Accounting

variable [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (quantum : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
local notation "Action" => Accounting.Action Owner clients
local notation "Occurrence" => CausalEvent (HistoryOccurrence clients)
local notation "actualStep" => sourceStep quantum

/-- Entry selection uses the existing streaming observers. The disabled
branch is the original uncounted action runner on this same retained Call. -/
def observe (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (state : Cfg) :=
  enterActionObservers actualStep sourceCapture capacity gate history account actions state

theorem erasure (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (state : Cfg) :
    (observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
      history account actions state).2.2 =
      advance construct callbackConstruct fallback attachment authority before current reader point required quantum capacity actions state :=
  enterActionObservers_erases _ _ _ _ _ _ _ _

/-- The recorded endpoint retains the independently weighted source partition,
actual source loan, frames and work. Nothing is reconstructed from the diary. -/
theorem scheduled_source (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (grants : List (BodyCallWeighted.Authored.Grant construct callbackConstruct fallback attachment (Context := Context)))
    (limit : Nat) (actions : List Action) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
      (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
      (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected
        (OrderedDependencyStore.query before reader) items parameter ([], context))
    let observed := observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
      history account actions (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients))
    ∃ target, observed.2.2.execution = some target ∧
      Safe construct callbackConstruct fallback attachment (OrderedDependencyStore.query before reader) items parameter target.producer ∧
      owned.2.2.context.2.1 ++ View observed.2.2 target.producer =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
  dsimp only
  rw [erasure]
  exact scheduled_handoff_source construct callbackConstruct fallback attachment authority before current reader point required
    grants quantum limit capacity actions items parameter context

theorem scheduled_license (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (grants : List (BodyCallWeighted.Authored.Grant construct callbackConstruct fallback attachment (Context := Context)))
    (limit : Nat) (actions : List Action) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
      (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
      (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected
        (OrderedDependencyStore.query before reader) items parameter ([], context))
    let observed := observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
      history account actions (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients))
    ∃ call, (release construct callbackConstruct fallback attachment observed.2.2).1 = some call ∧
      ∀ requested interface answers,
        (BodyCallWeighted.Authored.admit construct callbackConstruct fallback attachment requested interface
          (OrderedDependencyStore.query before reader) items parameter call).1 = some answers →
        answers = BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter ∧
          ConventionAllows requested answers.length := by
  dsimp only
  rw [erasure]
  exact scheduled_release_license construct callbackConstruct fallback attachment authority before current reader point required
    grants quantum limit capacity actions items parameter context

set_option backward.isDefEq.respectTransparency false in
/-- History and numeric accounts are the existing RunAccount projections of
actual operations. These are admission/delivery events and protocol units;
acknowledgment may count a driver operation without a new source request. -/
theorem source_path (record : Prefix Occurrence) (account : ProtocolAccount) (actions : List Action) (state : Cfg) :
    letI : Quiver.{0} Cfg := actionQuiver (Output := Owner) (clients := clients) actualStep sourceCapture capacity gate
    observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
        (some record) (some account) actions state =
      (some (Prefix.append record (pathOccurrences actualStep sourceCapture capacity gate
        (actionPath actualStep sourceCapture capacity gate actions state))),
        some (account * (splitAccount (Output := Owner) (clients := clients) actualStep sourceCapture capacity gate).of
          (actionPath actualStep sourceCapture capacity gate actions state)),
        advance construct callbackConstruct fallback attachment authority before current reader point required quantum capacity actions state) := by
  simpa only [observe, enterActionObservers, advance] using
    congrArg (fun result => (some result.1, some result.2.2, result.2.1))
      (observeActions_eq_source_accounts actualStep sourceCapture capacity gate actions record account state)

theorem split (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (first second : List Action) (state : Cfg) :
    observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
      history account (first ++ second) state =
      observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
        (observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity history account first state).1
        (observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity history account first state).2.1 second
        (observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity history account first state).2.2 :=
  enterActionObservers_append _ _ _ _ _ _ _ _ _

theorem forget (record : Prefix Occurrence) (account : ProtocolAccount)
    (first second : List Action) (state : Cfg) :
    observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity none
      (observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity (some record) (some account) first state).2.1
      second (observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
        (some record) (some account) first state).2.2 =
      (none, some (count actualStep sourceCapture capacity gate (first ++ second) account state).2,
        advance construct callbackConstruct fallback attachment authority before current reader point required quantum capacity (first ++ second) state) := by
  unfold observe
  rw [forget_action_history_preserves_account, count_erases]
  rfl

theorem late_bounded (first gap last : List Action) (earlier : Prefix Occurrence) (bound : Nat) (state : Cfg) :
    let resumed := runActions actualStep sourceCapture capacity gate gap
      (recordActions actualStep sourceCapture capacity gate first earlier state).2
    let events := pathOccurrences actualStep sourceCapture capacity gate (actionPath actualStep sourceCapture capacity gate last resumed)
    let result := recordActions actualStep sourceCapture capacity gate last (Prefix.initial bound) resumed
    result.1.items = events.take bound ∧ result.1.remaining = bound - events.length ∧ result.1.omitted = events.length - bound :=
  fresh_record_after_unrecorded_gap_bounds _ _ _ _ _ _ _ _ _ _

#print axioms erasure
#print axioms scheduled_source
#print axioms scheduled_license
#print axioms source_path
#print axioms split
#print axioms forget
#print axioms late_bounded

end History

#print axioms completed_suffix_source
#print axioms release_keeps_source
#print axioms denied_keeps_cut
#print axioms step_factor_origin
#print axioms adopt_pending_origin
#print axioms resume_safe
#print axioms schedule_safe
#print axioms release_adopt
#print axioms acknowledge_cut
#print axioms release_safe
#print axioms step_safe
#print axioms step_rows
#print axioms advance_source
#print axioms scheduled_handoff_source
#print axioms scheduled_release_license


end BodyCallShared.Weighted.Authored.Handoff

/-! ## Checked publication of closed and open weighted returns

The source is the existing authored weighted Call. Ordinary completion
publishes its complete records separately; a genuine handoff publishes one
observation with the captured prefix and the same retained Call. A source
pause supplies no publication packet. The finite publication provider neither
re-enters source syntax nor interprets the returned records' conditions.
-/
namespace BodyCallWeighted.Authored.Publication

open Cursor.Fold.OwnedSequence.CallbackBoundary

variable {Input Output Weight Context Term Environment Consumer : Type} [Semiring Weight]
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (attachment : BodyCall.WeightedSource.Attachment Input Output Weight)

local notation "selected" => selection attachment
local notation "Row" => BodyCall.WeightedSource.Row Output Weight
local notation "Record" => Cursor.Fold.OwnedSequence.Returned Term Environment
local notation "SourceCall" => Compact.Attachment.Call construct callbackConstruct fallback selected
  (Context := List Row × Context)
local notation "Loan" => Compact.Attachment.SparseReturned construct callbackConstruct fallback selected
local notation "OpenReturn" => Record × (List Record × SourceCall)
local notation "Item" => Record ⊕ OpenReturn


/-- Only an acknowledged producer-finished cut supplies a closed batch.
A genuine handoff retains both the observed prefix and the original Call.
Pending loans, intermediate yields and source pauses remain unpublished here. -/
def reply (record : Row → Record) (observe : SourceCall → Record)
    (call : SourceCall) : NextReply (List Record) OpenReturn :=
  if Compact.Attachment.complete construct callbackConstruct fallback selected call then
    .returned (call.2.2.context.2.1.map record)
  else match BodyCallShared.Weighted.inspect construct callbackConstruct fallback selected call with
    | .handoff _ _ => .terminal (observe call, call.2.2.context.2.1.map record, call)
    | _ => .paused

theorem closed_reply (record : Row → Record) (observe : SourceCall → Record)
    (call : SourceCall)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback selected call = true) :
    reply construct callbackConstruct fallback attachment record observe call =
      .returned (call.2.2.context.2.1.map record) := by
  simp [reply, finished]

theorem handoff_reply (record : Row → Record) (observe : SourceCall → Record)
    (call : SourceCall) (loan : Loan)
    (handed : BodyCallShared.Weighted.inspect construct callbackConstruct fallback selected call =
      .handoff loan call) :
    reply construct callbackConstruct fallback attachment record observe call =
      .terminal (observe call, call.2.2.context.2.1.map record, call) := by
  by_cases finished : Compact.Attachment.complete construct callbackConstruct fallback selected call = true
  · simp [BodyCallShared.Weighted.inspect, finished] at handed
  · simp [reply, finished, handed]

/-- A grant can finish without supplying either a closed bag or an open stop.
The paused source remains with its caller, rather than becoming an Observation. -/
theorem running_reply (record : Row → Record) (observe : SourceCall → Record)
    (call : SourceCall)
    (running : call.2.1.terminal = none) (noLoan : call.2.1.pending = none) :
    reply construct callbackConstruct fallback attachment record observe call = .paused := by
  simp [reply, Compact.Attachment.complete, Compact.Attachment.eraseCall,
    BodyCallAdmission.complete, BodyCallShared.Weighted.inspect, running, noLoan]

/-- The concrete publisher preserves the exact source and the independent
weighted meaning while partitioning complete return records. No answer
equality is supplied by the publication checker. -/
theorem closed_partition (record : Row → Record) (call : SourceCall)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (captured : Captured construct callbackConstruct fallback attachment authored items parameter call)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback selected call = true)
    (check : Consumer → Item → Bool × Consumer) (grants : List Nat) (consumer : Consumer) :
    let later := FrozenPublication.schedule check grants
      (FrozenPublication.start call
        (FrozenPublication.records (Observation := OpenReturn) (.inl (call.2.2.context.2.1.map record))) consumer)
    later.2.2.1 = call ∧
      later.2.2.2.accumulator.1 ++ later.2.2.2.pending.toList ++ later.2.2.2.remaining =
        (BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter).map
          (fun row => Sum.inl (record row)) := by
  have actual := completed_source construct callbackConstruct fallback attachment
    authored items parameter call captured finished
  simpa [FrozenPublication.records, actual, List.map_map, Function.comp_def] using
    FrozenPublication.schedule_partition check grants call
      (FrozenPublication.records (Observation := OpenReturn) (.inl (call.2.2.context.2.1.map record))) consumer

/-- Entry and actual source grants construct the source invariant. The only
completion premise is the real finished cut, not the number of granted steps. -/
theorem actual_closed_partition (record : Row → Record)
    (sourceGrants : List (Grant construct callbackConstruct fallback attachment (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (check : Consumer → Item → Bool × Consumer) (grants : List Nat) (consumer : Consumer) :
    let call := Compact.Attachment.schedule construct callbackConstruct fallback selected
      (readGrants construct callbackConstruct fallback attachment sourceGrants)
      (Compact.Attachment.openCall construct callbackConstruct fallback selected authored items parameter ([], context))
    Compact.Attachment.complete construct callbackConstruct fallback selected call = true →
    let later := FrozenPublication.schedule check grants
      (FrozenPublication.start call
        (FrozenPublication.records (Observation := OpenReturn) (.inl (call.2.2.context.2.1.map record))) consumer)
    later.2.2.1 = call ∧
      later.2.2.2.accumulator.1 ++ later.2.2.2.pending.toList ++ later.2.2.2.remaining =
        (BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter).map
          (fun row => Sum.inl (record row)) := by
  intro call finished
  exact closed_partition construct callbackConstruct fallback attachment record call authored items parameter
    (schedule_captured construct callbackConstruct fallback attachment sourceGrants authored items parameter _
      (open_captured construct callbackConstruct fallback attachment authored items parameter context))
    finished check grants consumer

/-- Finishing the checked suffix, including the zero-row case, exposes exactly
the independent source records. Source closure alone does not discharge these
two consumer-side obligations. -/
theorem closed_drained (record : Row → Record) (call : SourceCall)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (captured : Captured construct callbackConstruct fallback attachment authored items parameter call)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback selected call = true)
    (check : Consumer → Item → Bool × Consumer) (grants : List Nat) (consumer : Consumer) :
    let later := FrozenPublication.schedule check grants
      (FrozenPublication.start call
        (FrozenPublication.records (Observation := OpenReturn) (.inl (call.2.2.context.2.1.map record))) consumer)
    later.2.2.2.pending = none → later.2.2.2.remaining = [] →
      later.2.2.2.accumulator.1 =
        (BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter).map
          (fun row => Sum.inl (record row)) := by
  intro later noLoan noRows
  have conserved := (closed_partition construct callbackConstruct fallback attachment record call
    authored items parameter captured finished check grants consumer).2
  change later.2.2.2.accumulator.1 ++ later.2.2.2.pending.toList ++ later.2.2.2.remaining =
    (BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter).map
      (fun row => Sum.inl (record row)) at conserved
  simpa only [noLoan, noRows, Option.toList_none, List.append_nil] using conserved

/-- The singleton open reply retains the full actual residual. Its observed
prefix plus that residual equals the independent weighted source; publication
refusals preserve both parts without an additional source step. -/
theorem open_partition (record : Row → Record) (observe : SourceCall → Record)
    (call : SourceCall)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (captured : Captured construct callbackConstruct fallback attachment authored items parameter call)
    (loan : Loan)
    (handed : BodyCallShared.Weighted.inspect construct callbackConstruct fallback selected call =
      .handoff loan call)
    (check : Consumer → Item → Bool × Consumer) (grants : List Nat) (consumer : Consumer) :
    let packet : OpenReturn := (observe call, call.2.2.context.2.1.map record, call)
    FrozenPublication.prepare call consumer
        (reply construct callbackConstruct fallback attachment record observe call) =
      some (FrozenPublication.start call [Sum.inr packet] consumer) ∧
    let later := FrozenPublication.schedule check grants
      (FrozenPublication.start call [Sum.inr packet] consumer)
    later.2.2.1 = call ∧
      later.2.2.2.accumulator.1 ++ later.2.2.2.pending.toList ++ later.2.2.2.remaining = [Sum.inr packet] ∧
      packet.2.1 ++ (unaccepted construct callbackConstruct fallback attachment call.2.2.computation.2).map record =
        (BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter).map record := by
  intro packet
  constructor
  · rw [handoff_reply construct callbackConstruct fallback attachment record observe call loan handed]
    rfl
  · have kept := FrozenPublication.schedule_partition check grants call [Sum.inr packet] consumer
    refine ⟨kept.1, kept.2, ?_⟩
    simpa [packet, view, List.map_append] using congrArg (List.map record) captured.2.2


#print axioms closed_reply
#print axioms handoff_reply
#print axioms running_reply
#print axioms closed_partition
#print axioms actual_closed_partition
#print axioms closed_drained
#print axioms open_partition

end BodyCallWeighted.Authored.Publication

end Mettapedia.Machines.SourceProducerCardinality

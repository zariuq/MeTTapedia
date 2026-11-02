import Mettapedia.Machines.NativeCallReturn
import Mettapedia.Machines.ResumableRegion
import Mettapedia.Machines.ScopedCommit

/-!
# Contextual computations and retained continuations

Values, immutable suspension references, computations and continuations have
different roles. A dialect supplies lexical lookup, suspension construction,
force interpretation and native effects. The kernel sequences their results;
it does not infer execution permission from the spelling of a value.

Choice saves the lexical context and continuation, while effects remain in the
world. Logical stores, their rollback and Need memoization are not identified
with this lexical context. Those require their own concrete adapters.

Native entry changes control to a retained worker. Each pull retains the
returned branch's context and may perform further producer work. A worker can
fail or stop without invoking its entrance again. Native-return cursors are
one concrete instance of this interface, not its universal representation.
Source debits are explicit nodes: administrative transitions do not invent
source fuel. Worker-internal accounting requires the worker's own refinement.
This module does not assert that every C transition has yet been related to
this kernel or that its abstract transitions have unit native cost.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ContextualCBPV

open NativeCallReturn

variable (Value Call Effect Fault Delay Suspension Context World Worker : Type)

/-- The continuation receives provenance and conditional obligations as well
as the value. Raised control never enters an ordinary value continuation. -/
inductive Computation where
  | returned (value : Value)
  | sequence (producer : Computation) (body : Packet Value Fault Delay → Computation)
  | invoke (call : Call)
  | thunk (reference : Suspension)
  | force (value : Value)
  | choice (first second : Computation)
  | scope (body : Computation)
  | commit (value : Value)
  | commitPacket (packet : Packet Value Fault Delay)
  | failure
  | raised (fault : Fault)
  | handle (producer : Computation) (handler : Fault → Computation)
  | native (effect : Effect)
  | source (occurrence debit : Nat) (body : Computation)

abbrev Code := Computation Value Call Effect Fault Delay Suspension

structure Semantics where
  /-- Current callee lookup does not execute the returned computation. -/
  enter : World → Context → Call → Context × Code Value Call Effect Fault Delay Suspension
  suspend : Context → Suspension → Value
  /-- Ordinary force reads the saved computation; it creates no Need cache. -/
  force : Context → Value → Context × Code Value Call Effect Fault Delay Suspension
  native : Context → World → Effect → World × Worker
  pull : World → Worker → World × Pull (Context × Packet Value Fault Delay) Worker
  /-- Restore lexical scope while retaining the returned logical branch. -/
  resume : Context → Context → Context

inductive Frame where
  | sequence (context : Context)
      (body : Packet Value Fault Delay → Code Value Call Effect Fault Delay Suspension)
  | handler (context : Context) (choiceFloor : Nat)
      (body : Fault → Code Value Call Effect Fault Delay Suspension)
  | restore (context : Context)
  | scope (choiceFloor : Nat)

inductive Control where
  | compute (context : Context) (code : Code Value Call Effect Fault Delay Suspension)
  | delivery (worker : Worker)
  | returned (context : Context) (packet : Packet Value Fault Delay)
  | failed
  | stopped (reason : Stop)
  | unhandled (fault : Fault)

structure Work where
  control : Control Value Call Effect Fault Delay Suspension Context Worker
  frames : List (Frame Value Call Effect Fault Delay Suspension Context) := []

structure State where
  world : World
  focus : Work Value Call Effect Fault Delay Suspension Context Worker
  alternatives : List (Work Value Call Effect Fault Delay Suspension Context Worker) := []
  published : List (Context × Packet Value Fault Delay) := []
  nativeEntries : Nat := 0
  spent : Nat := 0
  sourceTrace : List Nat := []

variable {Value Call Effect Fault Delay Suspension Context World Worker}

/-- Delimiters belong to elaboration. Lexical restoration and exception
handlers do not manufacture a cut scope. The root's saved suffix is empty. -/
def choiceFloor : List (Frame Value Call Effect Fault Delay Suspension Context) → Nat
  | [] => 0
  | .scope floor :: _ => floor
  | _ :: rest => choiceFloor rest

/-- The stack is newest-first. Keep the saved outside suffix, without
restarting it or changing the current logical branch or effect world. -/
def retainOutside {Pending : Type*} (floor : Nat) (pending : List Pending) : List Pending :=
  pending.drop (pending.length - floor)

theorem retainOutside_suffix {Pending : Type*} (inside outside : List Pending) :
    retainOutside outside.length (inside ++ outside) = outside := by
  simp [retainOutside]

abbrev KernelSemantics := Semantics Value Call Effect Fault Delay Suspension Context World Worker
abbrev KernelState := State Value Call Effect Fault Delay Suspension Context World Worker

/-- Commit the current scope while retaining the actual packet and logical
branch. Value-only cuts use the same transition with a completed packet. -/
def commitReturn (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (context : Context) (packet : Packet Value Fault Delay)
    (frames : List (Frame Value Call Effect Fault Delay Suspension Context)) :=
  {state with
    focus := ⟨.returned context packet, frames⟩
    alternatives := retainOutside (choiceFloor frames) state.alternatives}

def initial (world : World) (context : Context)
    (code : Code Value Call Effect Fault Delay Suspension) :
    KernelState (Value := Value) (Call := Call) (Effect := Effect) (Fault := Fault)
      (Delay := Delay) (Suspension := Suspension) (Context := Context) (World := World) (Worker := Worker) :=
  ⟨world, ⟨.compute context code, []⟩, [], [], 0, 0, []⟩

private def continueAlternatives
    (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :=
  match state.alternatives with
  | [] => {state with focus := ⟨.stopped .complete, []⟩}
  | next :: rest => {state with focus := next, alternatives := rest}

@[simp] theorem exhausted_alternatives
    (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (empty : state.alternatives = []) :
    continueAlternatives state = {state with focus := ⟨.stopped .complete, []⟩} := by
  simp [continueAlternatives, empty]

/-- Native work and lexical interpretation occur here. Publication is a
separate transition; the retained cursor has already crossed native entry. -/
def advance (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) : Option (KernelState
      (Value := Value) (Call := Call) (Effect := Effect) (Fault := Fault)
      (Delay := Delay) (Suspension := Suspension) (Context := Context) (World := World) (Worker := Worker)) :=
  let frames := state.focus.frames
  match state.focus.control with
  | .compute context code =>
      match code with
      | .returned value =>
          some {state with focus := ⟨.returned context (.value .completed value), frames⟩}
      | .sequence producer body =>
          some {state with focus := ⟨.compute context producer,
            .sequence context body :: frames⟩}
      | .invoke call =>
          let entered := sem.enter state.world context call
          some {state with focus := ⟨.compute entered.1 entered.2,
            .restore context :: frames⟩}
      | .thunk reference =>
          some {state with focus := ⟨.returned context
            (.value .completed (sem.suspend context reference)), frames⟩}
      | .force value =>
          let forced := sem.force context value
          some {state with focus := ⟨.compute forced.1 forced.2,
            .restore context :: frames⟩}
      | .choice first second =>
          some {state with
            focus := ⟨.compute context first, frames⟩
            alternatives := ⟨.compute context second, frames⟩ :: state.alternatives}
      | .scope body =>
          some {state with focus := ⟨.compute context body,
            .scope state.alternatives.length :: frames⟩}
      | .commit value =>
          some (commitReturn state context (.value .completed value) frames)
      | .commitPacket packet => some (commitReturn state context packet frames)
      | .failure => some {state with focus := ⟨.failed, frames⟩}
      | .raised fault => some {state with focus := ⟨.returned context (.raised fault), frames⟩}
      | .handle producer handler =>
          some {state with focus := ⟨.compute context producer,
            .handler context state.alternatives.length handler :: frames⟩}
      | .native effect =>
          let produced := sem.native context state.world effect
          some {state with
            world := produced.1
            focus := ⟨.delivery produced.2, frames⟩
            nativeEntries := state.nativeEntries + 1}
      | .source _ _ body => some {state with focus := ⟨.compute context body, frames⟩}
  | .delivery worker =>
      let produced := sem.pull state.world worker
      match produced.2 with
      | .returned item next =>
          some {state with
            world := produced.1
            focus := ⟨.returned item.1 item.2, frames⟩
            alternatives := ⟨.delivery next, frames⟩ :: state.alternatives}
      | .stopped .complete => some {state with world := produced.1, focus := ⟨.failed, frames⟩}
      | .stopped reason => some {state with world := produced.1, focus := ⟨.stopped reason, []⟩}
  | .returned context packet =>
      match frames with
      | .sequence saved body :: rest =>
          match packet with
          | .raised _ => some {state with focus := ⟨.returned (sem.resume saved context) packet, rest⟩}
          | _ => some {state with focus := ⟨.compute (sem.resume saved context) (body packet), rest⟩}
      | .handler saved floor handler :: rest =>
          match packet with
          | .raised fault => some {state with
              focus := ⟨.compute saved (handler fault), rest⟩
              alternatives := state.alternatives.drop (state.alternatives.length - floor)}
          | _ => some {state with focus := ⟨.returned (sem.resume saved context) packet, rest⟩}
      | .restore saved :: rest =>
          some {state with focus := ⟨.returned (sem.resume saved context) packet, rest⟩}
      | .scope _ :: rest =>
          some {state with focus := ⟨.returned context packet, rest⟩}
      | [] =>
          match packet with
          | .raised fault => some {state with focus := ⟨.unhandled fault, []⟩}
          | _ => some (continueAlternatives
              {state with published := state.published ++ [(context, packet)]})
  | .failed => some (continueAlternatives state)
  | .stopped _ | .unhandled _ => none

def debit (control : Control Value Call Effect Fault Delay Suspension Context Worker) : Nat :=
  match control with
  | .compute _ (.source _ cost _) => cost
  | _ => 0

def origin (control : Control Value Call Effect Fault Delay Suspension Context Worker) : Option Nat :=
  match control with
  | .compute _ (.source occurrence _ _) => some occurrence
  | _ => none

/-- Source charges belong to source nodes, independently of frame operations. -/
def step (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :=
  (advance sem state).map fun next => {next with
    spent := state.spent + debit state.focus.control
    sourceTrace := match origin state.focus.control with
      | some occurrence => state.sourceTrace ++ [occurrence]
      | none => state.sourceTrace}

def core (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker)) (world : World) (context : Context) :
    MachineCore (Code Value Call Effect Fault Delay Suspension) where
  State := KernelState
  load := initial world context
  step := step sem

/-- A publication acknowledgement does not step a worker. A refused loan
remains the same returned packet and context, with its continuation retained. -/
def publication (work : Work Value Call Effect Fault Delay Suspension Context Worker) :
    Option (Context × Packet Value Fault Delay) :=
  match work.control, work.frames with
  | .returned context (.value role value), [] => some (context, .value role value)
  | .returned context (.conditional value delayed), [] =>
      some (context, .conditional value delayed)
  | _, _ => none

def consumerStep (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (accept : Context × Packet Value Fault Delay → Bool)
    (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :=
  match publication state.focus with
  | some returned => if accept returned then step sem state else none
  | none => step sem state

theorem refused_publication_retains_packet
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (accept : Context × Packet Value Fault Delay → Bool)
    (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (returned : Context × Packet Value Fault Delay)
    (pending : publication state.focus = some returned)
    (refused : accept returned = false) : consumerStep sem accept state = none := by
  simp [consumerStep, pending, refused]

theorem step_charge (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (before after : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (advanced : step sem before = some after) :
    after.spent = before.spent + debit before.focus.control := by
  unfold step at advanced
  cases next : advance sem before with
  | none => simp [next] at advanced
  | some value => simp [next] at advanced; subst after; rfl

theorem step_source_trace
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (before after : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (advanced : step sem before = some after) :
    after.sourceTrace = match origin before.focus.control with
      | some occurrence => before.sourceTrace ++ [occurrence]
      | none => before.sourceTrace := by
  unfold step at advanced
  cases next : advance sem before with
  | none => simp [next] at advanced
  | some value => simp [next] at advanced; subst after; rfl

theorem native_entry_once (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (world : World) (context : Context) (effect : Effect) :
    advance sem (initial world context (.native effect)) = some
      ⟨(sem.native context world effect).1,
        ⟨.delivery (sem.native context world effect).2, []⟩,
        [], [], 1, 0, []⟩ := by
  simp [advance, initial]

theorem thunk_is_not_force (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (world : World) (context : Context) (reference : Suspension) :
    advance sem (initial world context (.thunk reference)) = some
      ⟨world, ⟨.returned context (.value .completed (sem.suspend context reference)), []⟩,
        [], [], 0, 0, []⟩ := by
  simp [advance, initial]

/-- Lower an already admitted worker to an invocation followed by one native
entrance. This adapter changes call lowering, not the suspension interpreter
or the effect service. Admission evidence belongs before this fragment. -/
def nativeWorker (sem : Semantics Value Call Call Fault Delay Suspension Context World Worker) :
    Semantics Value Call Call Fault Delay Suspension Context World Worker :=
  {sem with enter := fun _ context call => (context, .native call)}

/-- The independent invocation reference and the continuation kernel agree on
the complete world and return source of an admitted native worker. No value,
failure, raised control or interrupted source is collapsed at this boundary. -/
theorem admitted_worker_refines
    (sem : Semantics Value Call Call Fault Delay Suspension Context World (Cursor Value Fault Delay Context))
    (world : World) (context : Context) (call : Call)
    (source : NativeCallReturn.Invocation.Program Call Call World Value Fault Delay)
    (admitted : source.admission world call = some call)
    (backend : source.invoke world call =
      ((sem.native context world call).1, (sem.native context world call).2.source)) :
    let entered := (step (nativeWorker sem)
      (initial world context (.invoke call))).bind (step (nativeWorker sem))
    entered.map (fun state =>
      (state.world, match state.focus.control with
        | .delivery cursor => some cursor.source
        | _ => none)) =
      some ((NativeCallReturn.Invocation.reference source world call).1,
        (match (NativeCallReturn.Invocation.reference source world call).2 with
         | .inr result => some result
         | .inl _ => none)) := by
  simp [step, advance, initial, nativeWorker, debit, origin,
    NativeCallReturn.Invocation.reference, admitted, backend]

theorem split_resume (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker)) (world : World) (context : Context)
    (first second : Nat) (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :
    (core sem world context).runSlice (first + second) state =
      let earlier := (core sem world context).runSlice first state
      let later := (core sem world context).runSlice second earlier.1
      (later.1, earlier.2 + later.2) :=
  MachineCore.runSlice_add (core sem world context) first second state

/-- A semantic purse is separate from the physical slice allowance. The
charge is checked before taking a transition, including a native entrance. -/
structure Metered where
  state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker)
  remaining : Nat

def meteredStep (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (meter : Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) : Option (Metered
        (Value := Value) (Call := Call) (Effect := Effect) (Fault := Fault)
        (Delay := Delay) (Suspension := Suspension) (Context := Context) (World := World) (Worker := Worker)) :=
  if debit meter.state.focus.control ≤ meter.remaining then
    (step sem meter.state).map fun next =>
      ⟨next, meter.remaining - debit meter.state.focus.control⟩
  else none

theorem semantic_purse_conserved
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (before after : Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (advanced : meteredStep sem before = some after) :
    after.state.spent + after.remaining = before.state.spent + before.remaining := by
  unfold meteredStep at advanced
  split at advanced
  next enough =>
    cases moved : step sem before.state with
    | none => simp [moved] at advanced
    | some state =>
        simp only [moved, Option.map_some, Option.some.injEq] at advanced
        subst after
        have charged := step_charge sem before.state state moved
        dsimp
        omega
  next => simp at advanced

theorem insufficient_source_fuel
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (meter : Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (insufficient : meter.remaining < debit meter.state.focus.control) :
    meteredStep sem meter = none := by
  simp [meteredStep, Nat.not_le.mpr insufficient]

def meteredCore (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker)) (world : World) (context : Context)
    (fuel : Nat) : MachineCore (Code Value Call Effect Fault Delay Suspension) where
  State := Metered
  load := fun code => ⟨initial world context code, fuel⟩
  step := meteredStep sem

theorem sliced_source_purse_conserved
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (world : World) (context : Context) (sourceFuel physicalSteps : Nat)
    (before : Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :
    let after := ((meteredCore sem world context sourceFuel).runSlice physicalSteps before).1
    after.state.spent + after.remaining = before.state.spent + before.remaining := by
  exact MachineCore.runSlice_preserves (meteredCore sem world context sourceFuel)
    (fun meter => meter.state.spent + meter.remaining)
    (fun before after advanced => semantic_purse_conserved sem before after advanced)
    physicalSteps before

namespace EpisodeAccounting

/-- The episode's finite purse, independent of a worker's physical allowance.
The bound below relates the natural account to the native word operations. -/
structure Purse where
  remaining : Nat
  spent : Nat
  deriving DecidableEq, Repr

def grant (request parent : Option Nat) : Option Nat :=
  match request, parent with
  | none, none => none
  | some requested, none => some requested
  | none, some available => some available
  | some requested, some available => some (min requested available)

theorem grant_le_parent (request : Option Nat) (available credit : Nat)
    (issued : grant request (some available) = some credit) : credit ≤ available := by
  cases request with
  | none =>
      simp only [grant, Option.some.injEq] at issued
      omega
  | some requested =>
      simp only [grant, Option.some.injEq] at issued
      rw [← issued]
      exact Nat.min_le_right _ _

theorem grant_le_request (parent : Option Nat) (requested credit : Nat)
    (issued : grant (some requested) parent = some credit) : credit ≤ requested := by
  cases parent with
  | none =>
      simp only [grant, Option.some.injEq] at issued
      omega
  | some available =>
      simp only [grant, Option.some.injEq] at issued
      rw [← issued]
      exact Nat.min_le_left _ _

theorem grant_unbounded (request parent : Option Nat) :
    grant request parent = none ↔ request = none ∧ parent = none := by
  cases request <;> cases parent <;> simp [grant]

/-- Native admission reads both the immediate request and the current
borrowed purse. An unbounded request cannot erase inherited finite credit. -/
def allowsUnmetered (request inherited : Option Nat) (noDiagnostic : Bool) : Bool :=
  request.isNone && inherited.isNone && noDiagnostic

theorem unmetered_iff_unbounded_grant (request inherited : Option Nat)
    (noDiagnostic : Bool) :
    allowsUnmetered request inherited noDiagnostic = true ↔
      grant request inherited = none ∧ noDiagnostic = true := by
  cases request <;> cases inherited <;> simp [allowsUnmetered, grant]

theorem finite_grant_refuses_unmetered (request inherited : Option Nat)
    (noDiagnostic : Bool) (credit : Nat)
    (bounded : grant request inherited = some credit) :
    allowsUnmetered request inherited noDiagnostic = false := by
  cases request <;> cases inherited <;> simp_all [grant, allowsUnmetered]

theorem inherited_zero_is_not_unbounded :
    allowsUnmetered none (some 0) true = false ∧
      allowsUnmetered none none true = true := by decide

/-- Independent natural-number accounting for one admitted source charge. -/
def debit (cost : Nat) (before : Purse) : Option Purse :=
  if cost ≤ before.remaining then
    some ⟨before.remaining - cost, before.spent + cost⟩
  else none

/-- Native word debit with explicit cost, atomic refusal and guarded addition.
This also admits an administrative zero debit at an empty purse. -/
def nativeDebit (maximum cost : Nat) (before : Purse) : Option Purse :=
  if before.remaining < cost then none
  else some ⟨before.remaining - cost,
    if maximum - cost < before.spent then maximum else before.spent + cost⟩

theorem native_debit_refines (maximum cost : Nat) (before : Purse)
    (inRange : before.spent + before.remaining ≤ maximum) :
    nativeDebit maximum cost before = debit cost before := by
  by_cases enough : cost ≤ before.remaining
  · have notEmpty : ¬ before.remaining < cost := by omega
    have noOverflow : ¬ maximum - cost < before.spent := by omega
    simp [nativeDebit, debit, enough, notEmpty, noOverflow]
  · have insufficient : before.remaining < cost := by omega
    simp [nativeDebit, debit, enough, insufficient]

theorem zero_debit_is_admin (maximum : Nat) (before : Purse)
    (inRange : before.spent + before.remaining ≤ maximum) :
    nativeDebit maximum 0 before = some before := by
  rw [native_debit_refines maximum 0 before inRange]
  simp [debit]

theorem overdraw_preserves_pending_charge (maximum cost : Nat) (before : Purse)
    (insufficient : before.remaining < cost) :
    nativeDebit maximum cost before = none := by
  simp [nativeDebit, insufficient]

/-- The native episode's unit debit: test zero first and saturate its word
counter. Reachable finite purses cannot hit saturation on an admitted step. -/
def nativeTick (maximum : Nat) (before : Purse) : Option Purse :=
  if before.remaining = 0 then none
  else some ⟨before.remaining - 1,
    if before.spent = maximum then before.spent else before.spent + 1⟩

theorem native_tick_refines (maximum : Nat) (before : Purse)
    (inRange : before.spent + before.remaining ≤ maximum) :
    nativeTick maximum before = debit 1 before := by
  by_cases empty : before.remaining = 0
  · simp [nativeTick, debit, empty]
  · have enough : 1 ≤ before.remaining := by omega
    have room : before.spent ≠ maximum := by omega
    simp [nativeTick, debit, empty, enough, room]

theorem debit_conserves (cost : Nat) (before after : Purse)
    (paid : debit cost before = some after) :
    after.spent + after.remaining = before.spent + before.remaining := by
  unfold debit at paid
  split at paid
  · cases paid
    simp only
    omega
  · contradiction

/-- Only performed work is settled. Unused child credit was never debited
from the paused parent and therefore needs no refund. -/
def settle (parent child : Purse) : Purse :=
  ⟨parent.remaining - child.spent, parent.spent + child.spent⟩

/-- The native close uses guarded word addition and truncated subtraction. -/
def nativeSettle (maximum : Nat) (parent child : Purse) : Purse :=
  ⟨if child.spent ≥ parent.remaining then 0 else parent.remaining - child.spent,
    if parent.spent > maximum - child.spent then maximum else parent.spent + child.spent⟩

theorem native_settle_refines (maximum : Nat) (parent child : Purse)
    (inRange : parent.spent + parent.remaining ≤ maximum)
    (borrowed : child.spent ≤ parent.remaining) :
    nativeSettle maximum parent child = settle parent child := by
  have room : ¬parent.spent > maximum - child.spent := by omega
  by_cases exhausted : child.spent ≥ parent.remaining
  · have empty : parent.remaining - child.spent = 0 := by omega
    simp [nativeSettle, settle, room, exhausted, empty]
  · simp [nativeSettle, settle, room, exhausted]

theorem settle_conserves (parent child : Purse)
    (borrowed : child.spent ≤ parent.remaining) :
    (settle parent child).spent + (settle parent child).remaining =
      parent.spent + parent.remaining := by
  simp only [settle]
  omega

theorem settle_add (parent first later : Purse) :
    settle (settle parent first) later =
      settle parent ⟨0, first.spent + later.spent⟩ := by
  simp [settle, Nat.sub_sub, Nat.add_assoc]

structure Loan where
  parent : Purse
  child : Purse
  linked : Bool
  deriving DecidableEq, Repr

def close (maximum : Nat) (loan : Loan) : Loan :=
  if loan.linked then
    {loan with parent := nativeSettle maximum loan.parent loan.child, linked := false}
  else loan

theorem close_once (maximum : Nat) (loan : Loan) :
    close maximum (close maximum loan) = close maximum loan := by
  rcases loan with ⟨parent, child, linked⟩
  cases linked <;> rfl

/-- Join explicit native word debit to the full contextual source step.
The charge is read from the retained computation before its transition. -/
def nativeChargedStep
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (maximum : Nat) (before : Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :
    Option (Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :=
  (nativeDebit maximum (ContextualCBPV.debit before.state.focus.control)
      ⟨before.remaining, before.state.spent⟩).bind fun paid =>
    (advance sem before.state).map fun next =>
      ⟨{next with
        spent := paid.spent
        sourceTrace := match origin before.state.focus.control with
          | some occurrence => before.state.sourceTrace ++ [occurrence]
          | none => before.state.sourceTrace}, paid.remaining⟩

theorem charged_step_refines
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (maximum : Nat) (before : Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (inRange : before.state.spent + before.remaining ≤ maximum) :
    nativeChargedStep sem maximum before = meteredStep sem before := by
  unfold nativeChargedStep
  rw [native_debit_refines maximum _ _ inRange]
  by_cases enough : ContextualCBPV.debit before.state.focus.control ≤ before.remaining
  · simp [debit, enough, meteredStep, step, Option.map_map, Function.comp_def]
  · simp [debit, enough, meteredStep]

/-- Independently implement the unit source step through the native ledger,
then update the complete contextual machine. This is a word-accounting join;
assigning native source charges and pointer ownership remain obligations. -/
def nativeUnitStep
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (maximum : Nat) (before : Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :
    Option (Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :=
  (nativeTick maximum ⟨before.remaining, before.state.spent⟩).bind fun paid =>
    (advance sem before.state).map fun next =>
      ⟨{next with
        spent := paid.spent
        sourceTrace := match origin before.state.focus.control with
          | some occurrence => before.state.sourceTrace ++ [occurrence]
          | none => before.state.sourceTrace}, paid.remaining⟩

theorem unit_step_refines
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (maximum : Nat) (before : Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (unitCharge : ContextualCBPV.debit before.state.focus.control = 1)
    (inRange : before.state.spent + before.remaining ≤ maximum) :
    nativeUnitStep sem maximum before = meteredStep sem before := by
  unfold nativeUnitStep
  rw [native_tick_refines maximum _ inRange]
  by_cases enough : 1 ≤ before.remaining
  · simp [debit, enough, meteredStep, unitCharge, step, Option.map_map, Function.comp_def]
  · simp [debit, enough, meteredStep, unitCharge]

theorem unused_credit_is_not_spent :
    nativeSettle (2 ^ 64 - 1) ⟨8, 0⟩ ⟨5, 3⟩ = ⟨5, 3⟩ ∧
      nativeSettle (2 ^ 64 - 1) ⟨8, 0⟩ ⟨5, 3⟩ ≠ ⟨0, 8⟩ := by decide

end EpisodeAccounting

/-- Moving an administrative sequence across a source charge preserves the
exact world, continuation, alternatives and debit after the two transitions.
The charge remains present on both sides. -/
theorem sequence_charge_commutes
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (world : World) (context : Context) (occurrence cost : Nat)
    (producer : Code Value Call Effect Fault Delay Suspension)
    (body : Packet Value Fault Delay → Code Value Call Effect Fault Delay Suspension) :
    (step sem (initial world context (.source occurrence cost (.sequence producer body)))).bind (step sem) =
    (step sem (initial world context (.sequence (.source occurrence cost producer) body))).bind (step sem) := by
  simp [step, advance, initial, debit, origin]

section CompletedReturn

variable (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))

/-- Elaboration's return computation retains the actual waiting frames.
Its payload can be code-shaped data; no syntax classification is involved. -/
def returnComputation (context : Context) (value : Value) :=
  {state with focus := ⟨.compute context (.returned value), state.focus.frames⟩}

/-- A region that has finished the return transfers its tagged packet at
the same continuation, without reconstructing executable source syntax. -/
def returnPacket (context : Context) (value : Value) :=
  {state with focus := ⟨.returned context (.value .completed value), state.focus.frames⟩}

theorem return_packet_step (context : Context) (value : Value) :
    step sem (returnComputation state context value) =
      some (returnPacket state context value) := by
  simp [step, advance, returnComputation, returnPacket, debit, origin]

/-- Removing the completed administrative return preserves every future
slice's exact endpoint, with one fewer physical transition. All branch,
lexical-context and committed-world fields remain in that endpoint. -/
theorem return_packet_resume (world : World) (context : Context)
    (value : Value) (extra : Nat) :
    (core sem world context).runSlice (extra + 1)
        (returnComputation state context value) =
      let later := (core sem world context).runSlice extra
        (returnPacket state context value)
      (later.1, later.2 + 1) := by
  simp only [MachineCore.runSlice, core, return_packet_step]

/-- Source accounting cannot disappear with the return instruction. This
lowered packet carries the original occurrence and charge exactly once. -/
theorem charged_return_packet (context : Context) (value : Value)
    (occurrence cost : Nat) :
    let source := {state with focus :=
      ⟨.compute context (.source occurrence cost (.returned value)), state.focus.frames⟩}
    (step sem source).bind (step sem) = some
      (returnPacket {state with
        spent := state.spent + cost
        sourceTrace := state.sourceTrace ++ [occurrence]} context value) := by
  simp [step, advance, returnPacket, debit, origin]

/-- Direct packet delivery has not entered the next computation: it cannot
repeat a native effect, publish early or discard a pending alternative. -/
theorem return_packet_keeps_residual (context : Context) (value : Value) :
    let target := returnPacket state context value
    target.world = state.world ∧
      target.nativeEntries = state.nativeEntries ∧
      target.alternatives = state.alternatives ∧
      target.published = state.published ∧
      target.spent = state.spent ∧
      target.sourceTrace = state.sourceTrace ∧
      target.focus.frames = state.focus.frames := by
  simp [returnPacket]

end CompletedReturn

section Commitment

variable (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))

/-- The dialect's delimiter snapshots the actual outside continuation. -/
theorem scope_entry (context : Context)
    (body : Code Value Call Effect Fault Delay Suspension) :
    advance sem {state with focus := ⟨.compute context (.scope body), state.focus.frames⟩} =
      some {state with focus := ⟨.compute context body,
        .scope state.alternatives.length :: state.focus.frames⟩} := rfl

/-- The representation invariant identifies a saved suffix. The transition
retains that suffix and the entire current world, branch and continuation. -/
theorem commit_keeps_outside (context : Context) (value : Value)
    (frames : List (Frame Value Call Effect Fault Delay Suspension Context))
    (inside outside : List (Work Value Call Effect Fault Delay Suspension Context Worker))
    (currentScope : choiceFloor frames = outside.length) :
    advance sem {state with
      focus := ⟨.compute context (.commit value), frames⟩
      alternatives := inside ++ outside} =
      some {state with
        focus := ⟨.returned context (.value .completed value), frames⟩
        alternatives := outside} := by
  simp [advance, commitReturn, currentScope, retainOutside_suffix]

/-- Join the concrete newest-first continuation stack to the independent
ScopedCommit CPS interpreter. Its saved failure continuation is exactly the
suffix retained by the actual contextual transition; the world is not reset. -/
theorem commit_refines_scoped_eval {Result : Type}
    (context : Context) (value : Value)
    (frames : List (Frame Value Call Effect Fault Delay Suspension Context))
    (inside outside : List (Work Value Call Effect Fault Delay Suspension Context Worker))
    (currentScope : choiceFloor frames = outside.length)
    (after : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (advanced : advance sem {state with
      focus := ⟨.compute context (.commit value), frames⟩
      alternatives := inside ++ outside} = some after)
    (body : ScopedCommit.Body Context World)
    (success : ScopedCommit.Success Context World Result)
    (decode : List (Work Value Call Effect Fault Delay Suspension Context Worker) →
      ScopedCommit.Failure World Result) :
    ScopedCommit.eval (.commit body) context success
        (decode (inside ++ outside)) (decode outside) state.world =
      ScopedCommit.eval body context success (decode after.alternatives)
        (decode after.alternatives) after.world := by
  have exactState := commit_keeps_outside sem state context value frames inside outside currentScope
  have actual := Option.some.inj (advanced.symm.trans exactState)
  subst after
  rfl

end Commitment

namespace Controls

inductive Datum where
  | number (value : Nat)
  | suspended (context reference : Nat)
  deriving DecidableEq, Repr

abbrev TestCode := Code Datum Unit Nat Nat Unit Nat

/-- An independent, state-changing native fixture: zero, one, duplicate,
raised and interrupted results have different return constructors. -/
def semantics : Semantics Datum Unit Nat Nat Unit Nat Nat Nat
    (Cursor Datum Nat Unit Nat) where
  enter := fun _ context _ => (context + 1, .native 1)
  suspend := Datum.suspended
  force := fun context value => match value with
    | .number n => (context, .returned (.number n))
    | .suspended saved reference => (saved, .native reference)
  native := fun context world effect =>
    (world + 1, ⟨(match effect with
      | 0 => .failure
      | 1 => .one (.value .completed (.number context))
      | 2 => .frontier .completed #[.number context, .number context]
      | 3 => .one (.raised 7)
      | 5 => .one (.conditional (.number context) ())
      | _ => .interrupted), context, 0⟩)
  pull := fun world cursor => (world, NativeCallReturn.read cursor)
  resume := fun saved _ => saved

def run (context : Nat) (code : TestCode) :=
  ((core semantics 0 context).runSlice 40 (initial 0 context code)).1

def meteredRun (budget : Nat) (code : TestCode) :=
  ((meteredCore semantics 0 4 budget).runSlice 40
    ⟨initial 0 4 code, budget⟩).1

/-- Dropping an internal source charge can commit a native effect before the
source computation has enough credit to reach it. -/
theorem erasing_charge_exposes_early_effect :
    (meteredRun 1 (.source 7 1 (.source 8 1 (.native 1)))).state.world = 0 ∧
      (meteredRun 1 (.source 7 1 (.native 1))).state.world = 1 := by decide

/-- Equal complete answers do not license erasing an internal charge. The
source pays both occurrences before performing and publishing the effect. -/
theorem complete_answers_do_not_determine_budgeted_prefixes :
    (run 4 (.source 7 1 (.source 8 1 (.native 1)))).published =
      (run 4 (.source 7 1 (.native 1))).published ∧
    (meteredRun 2 (.source 7 1 (.source 8 1 (.native 1)))).state.world = 1 ∧
    (meteredRun 2 (.source 7 1 (.source 8 1 (.native 1)))).state.spent = 2 ∧
    (meteredRun 2 (.source 7 1 (.source 8 1 (.native 1)))).state.sourceTrace = [7, 8] := by
  decide

theorem failed_native_keeps_effect :
    (run 4 (.native 0)).world = 1 ∧
    (run 4 (.native 0)).nativeEntries = 1 ∧
    (run 4 (.native 0)).published = [] := by decide

theorem thunk_return_does_not_run_body :
    (run 4 (.thunk 1)).world = 0 ∧
    (run 4 (.thunk 1)).published = [(4, .value .completed (.suspended 4 1))] := by decide

theorem force_reads_capture_and_restores_caller :
    (run 99 (.force (.suspended 4 1))).world = 1 ∧
    (run 99 (.force (.suspended 4 1))).published = [(99, .value .completed (.number 4))] := by decide

theorem ordinary_force_is_not_need :
    (run 99 (.sequence (.force (.suspended 4 1))
      (fun _ => .force (.suspended 4 1)))).nativeEntries = 2 := by decide

theorem duplicate_occurrences_survive :
    (run 4 (.native 2)).nativeEntries = 1 ∧
    (run 4 (.native 2)).published =
      [(4, .value .completed (.number 4)), (4, .value .completed (.number 4))] := by decide

theorem caught_raise_discards_protected_choices :
    (run 4 (.handle (.choice (.raised 7) (.native 1))
      (fun _ => .returned (.number 5)))).world = 0 ∧
    (run 4 (.handle (.choice (.raised 7) (.native 1))
      (fun _ => .returned (.number 5)))).published =
        [(4, .value .completed (.number 5))] := by decide

theorem caught_raise_preserves_outer_choice :
    (run 4 (.choice (.handle (.raised 7) (fun _ => .returned (.number 5)))
      (.native 1))).published =
        [(4, .value .completed (.number 5)), (4, .value .completed (.number 4))] := by decide

theorem caught_raise_keeps_committed_effect :
    (run 4 (.handle (.sequence (.native 1) (fun _ => .raised 7))
      (fun _ => .returned (.number 5)))).world = 1 ∧
    (run 4 (.handle (.sequence (.native 1) (fun _ => .raised 7))
      (fun _ => .returned (.number 5)))).nativeEntries = 1 := by decide

theorem uncaught_raise_is_not_a_value :
    (run 4 (.choice (.native 3) (.native 1))).world = 1 ∧
    (run 4 (.choice (.native 3) (.native 1))).published = [] ∧
    (run 4 (.choice (.native 3) (.native 1))).focus.control = .unhandled 7 :=
  ⟨rfl, rfl, rfl⟩

theorem conditional_return_keeps_obligation :
    (run 4 (.native 5)).published = [(4, .conditional (.number 4) ())] := by decide

theorem blocked_source_never_enters_native :
    let meter := ((meteredCore semantics 0 4 0).runSlice 40
      ⟨initial 0 4 (.source 9 1 (.native 1)), 0⟩).1
    meter.state.world = 0 ∧ meter.state.nativeEntries = 0 ∧ meter.state.spent = 0 := by decide

theorem interruption_is_not_failure :
    (run 4 (.choice (.native 4) (.native 1))).world = 1 ∧
    (run 4 (.choice (.native 4) (.native 1))).nativeEntries = 1 ∧
    (run 4 (.choice (.native 4) (.native 1))).focus.control = .stopped .cancelled :=
  ⟨rfl, rfl, rfl⟩

theorem source_charge_is_not_admin_steps :
    (run 4 (.source 7 2 (.sequence (.source 8 3 (.native 1))
      (fun _ => .source 9 4 (.returned (.number 8)))))).spent = 9 := by decide

theorem source_occurrences_survive_normalization :
    (run 4 (.source 7 2 (.sequence (.source 8 3 (.native 1))
      (fun _ => .source 9 4 (.returned (.number 8)))))).sourceTrace = [7, 8, 9] := by decide

theorem repeated_source_visits_are_not_a_set :
    (run 4 (.choice (.source 7 1 (.returned (.number 8)))
      (.source 7 1 (.returned (.number 8))))).sourceTrace = [7, 7] := by decide

end Controls

namespace CommitmentControls

open Controls

def number (n : Nat) : TestCode := .returned (.number n)

def callScope : TestCode :=
  .choice (.scope (.choice (.commit (.number 1)) (number 2))) (number 9)

theorem outside_choices_survive :
    (run 4 callScope).published =
      [(4, .value .completed (.number 1)), (4, .value .completed (.number 9))] := by
  decide

theorem erasing_delimiter_changes_answers :
    (run 4 callScope).published ≠
      (run 4 (.choice (.choice (.commit (.number 1)) (number 2)) (number 9))).published := by
  decide

theorem choices_after_commit_retain_duplicates :
    (run 4 (.scope (.sequence (.commit (.number 0))
      (fun _ => .choice (number 7) (number 7))))).published =
      [(4, .value .completed (.number 7)), (4, .value .completed (.number 7))] := by
  decide

def afterInnerScope : TestCode :=
  .choice (.scope (.choice
    (.sequence (.scope (number 1)) (fun _ => .commit (.number 2))) (number 3))) (number 9)

theorem caller_scope_restored :
    (run 4 afterInnerScope).published =
      [(4, .value .completed (.number 2)), (4, .value .completed (.number 9))] := by
  decide

theorem capturing_caller_continuation_changes_answers :
    (run 4 afterInnerScope).published ≠
      (run 4 (.choice (.scope (.choice
        (.scope (.sequence (number 1) (fun _ => .commit (.number 2))))
        (number 3))) (number 9))).published := by
  decide

theorem handler_does_not_create_cut_scope :
    (run 4 (.scope (.choice
      (.handle (.sequence (.commit (.number 1)) (fun _ => .raised 7))
        (fun _ => number 5)) (number 9)))).published =
      [(4, .value .completed (.number 5))] := by
  decide

def committedFailure : TestCode :=
  .choice (.scope (.choice
    (.sequence (.native 1) (fun _ =>
      .sequence (.commit (.number 0)) (fun _ => .failure))) (.native 2))) (number 9)

theorem failed_committed_branch_keeps_effect :
    (run 4 committedFailure).world = 1 ∧
      (run 4 committedFailure).nativeEntries = 1 ∧
      (run 4 committedFailure).published = [(4, .value .completed (.number 9))] := by
  decide

def callSemantics : Semantics Datum Unit Nat Nat Unit Nat Nat Nat
    (Cursor Datum Nat Unit Nat) :=
  {semantics with enter := fun _ context _ =>
    (context, .scope (.choice (.commit (.number 1)) (.native 2)))}

theorem callee_declares_its_scope :
    let code : TestCode := .choice (.invoke ()) (number 9)
    let after := ((core callSemantics 0 4).runSlice 40 (initial 0 4 code)).1
    after.published =
      [(4, .value .completed (.number 1)), (4, .value .completed (.number 9))] ∧
      after.world = 0 := by
  decide

def sourceLimited :=
  let code : TestCode :=
    .choice (.scope (.source 17 3 (.commit (.number 1)))) (number 9)
  ((meteredCore semantics 0 4 2).runSlice 40 ⟨initial 0 4 code, 2⟩).1

theorem insufficient_source_fuel_retains_pending_commit :
    sourceLimited.state.published = [] ∧ sourceLimited.state.world = 0 ∧
      sourceLimited.remaining = 2 ∧ debit sourceLimited.state.focus.control = 3 := by
  decide

end CommitmentControls

namespace WorkerControls

abbrev BranchContext := Nat × Nat
abbrev Returned := BranchContext × Packet Nat Nat Unit
abbrev BranchWorker := List Returned × Stop

/-- The first coordinate is lexical scope; the second is a persistent logical
branch. A resumed caller keeps its scope and the callee's branch updates. -/
def semantics : Semantics Nat Unit Nat Nat Unit Nat BranchContext Nat BranchWorker where
  enter := fun _ context _ => ((context.1 + 1, context.2), .native 0)
  suspend := fun context reference => context.1 * 100 + context.2 + reference
  force := fun context value => (context, .returned value)
  native := fun context world effect =>
    (world + 1,
      (if effect == 0 then
        [((context.1, context.2 + 1), .value .completed 4),
         ((context.1, context.2 + 2), .value .completed 5)]
       else [((context.1, context.2 + 1), .raised 7)], .complete))
  pull := fun world worker => (world + 1, referenceRead worker)
  resume := fun caller returned => (caller.1, returned.2)

def run (sem : Semantics Nat Unit Nat Nat Unit Nat BranchContext Nat BranchWorker)
    (code : Code Nat Unit Nat Nat Unit Nat) :=
  ((core sem 0 (1, 10)).runSlice 80 (initial 0 (1, 10) code)).1

theorem worker_keeps_each_returned_branch :
    (run semantics (.sequence (.native 0) (fun _ => .thunk 0))).published =
      [((1, 11), .value .completed 111), ((1, 12), .value .completed 112)] := by decide

theorem callee_restores_scope_and_keeps_bindings :
    (run semantics (.sequence (.invoke ()) (fun _ => .thunk 0))).published =
      [((1, 11), .value .completed 111), ((1, 12), .value .completed 112)] := by decide

theorem replacing_branch_with_entrance_changes_answers :
    (run {semantics with resume := fun saved _ => saved}
      (.sequence (.invoke ()) (fun _ => .thunk 0))).published ≠
      (run semantics (.sequence (.invoke ()) (fun _ => .thunk 0))).published := by decide

theorem pull_effects_do_not_reenter_native :
    (run semantics (.native 0)).world = 4 ∧
    (run semantics (.native 0)).nativeEntries = 1 := by decide

theorem handler_restores_branch_but_keeps_effects :
    (run semantics (.handle (.native 1) (fun _ => .thunk 0))).published =
      [((1, 10), .value .completed 110)] ∧
    (run semantics (.handle (.native 1) (fun _ => .thunk 0))).world = 2 := by decide

end WorkerControls

end Mettapedia.Machines.ContextualCBPV

#print axioms Mettapedia.Machines.ContextualCBPV.Controls.erasing_charge_exposes_early_effect
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.complete_answers_do_not_determine_budgeted_prefixes

#print axioms Mettapedia.Machines.ContextualCBPV.retainOutside_suffix
#print axioms Mettapedia.Machines.ContextualCBPV.scope_entry
#print axioms Mettapedia.Machines.ContextualCBPV.commit_keeps_outside
#print axioms Mettapedia.Machines.ContextualCBPV.commit_refines_scoped_eval
#print axioms Mettapedia.Machines.ContextualCBPV.CommitmentControls.outside_choices_survive
#print axioms Mettapedia.Machines.ContextualCBPV.CommitmentControls.erasing_delimiter_changes_answers
#print axioms Mettapedia.Machines.ContextualCBPV.CommitmentControls.choices_after_commit_retain_duplicates
#print axioms Mettapedia.Machines.ContextualCBPV.CommitmentControls.caller_scope_restored
#print axioms Mettapedia.Machines.ContextualCBPV.CommitmentControls.capturing_caller_continuation_changes_answers
#print axioms Mettapedia.Machines.ContextualCBPV.CommitmentControls.handler_does_not_create_cut_scope
#print axioms Mettapedia.Machines.ContextualCBPV.CommitmentControls.failed_committed_branch_keeps_effect
#print axioms Mettapedia.Machines.ContextualCBPV.CommitmentControls.callee_declares_its_scope
#print axioms Mettapedia.Machines.ContextualCBPV.CommitmentControls.insufficient_source_fuel_retains_pending_commit

#print axioms Mettapedia.Machines.ContextualCBPV.step_charge
#print axioms Mettapedia.Machines.ContextualCBPV.step_source_trace
#print axioms Mettapedia.Machines.ContextualCBPV.refused_publication_retains_packet
#print axioms Mettapedia.Machines.ContextualCBPV.native_entry_once
#print axioms Mettapedia.Machines.ContextualCBPV.thunk_is_not_force
#print axioms Mettapedia.Machines.ContextualCBPV.admitted_worker_refines
#print axioms Mettapedia.Machines.ContextualCBPV.split_resume
#print axioms Mettapedia.Machines.ContextualCBPV.semantic_purse_conserved
#print axioms Mettapedia.Machines.ContextualCBPV.insufficient_source_fuel
#print axioms Mettapedia.Machines.ContextualCBPV.sliced_source_purse_conserved
#print axioms Mettapedia.Machines.ContextualCBPV.sequence_charge_commutes
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.failed_native_keeps_effect
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.thunk_return_does_not_run_body
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.force_reads_capture_and_restores_caller
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.ordinary_force_is_not_need
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.duplicate_occurrences_survive
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.caught_raise_discards_protected_choices
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.caught_raise_preserves_outer_choice
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.caught_raise_keeps_committed_effect
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.uncaught_raise_is_not_a_value
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.conditional_return_keeps_obligation
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.blocked_source_never_enters_native
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.interruption_is_not_failure
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.source_charge_is_not_admin_steps
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.source_occurrences_survive_normalization
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.repeated_source_visits_are_not_a_set
#print axioms Mettapedia.Machines.ContextualCBPV.WorkerControls.worker_keeps_each_returned_branch
#print axioms Mettapedia.Machines.ContextualCBPV.WorkerControls.callee_restores_scope_and_keeps_bindings
#print axioms Mettapedia.Machines.ContextualCBPV.WorkerControls.replacing_branch_with_entrance_changes_answers
#print axioms Mettapedia.Machines.ContextualCBPV.WorkerControls.pull_effects_do_not_reenter_native
#print axioms Mettapedia.Machines.ContextualCBPV.WorkerControls.handler_restores_branch_but_keeps_effects

#print axioms Mettapedia.Machines.ContextualCBPV.exhausted_alternatives
#print axioms Mettapedia.Machines.ContextualCBPV.return_packet_step
#print axioms Mettapedia.Machines.ContextualCBPV.return_packet_resume
#print axioms Mettapedia.Machines.ContextualCBPV.charged_return_packet
#print axioms Mettapedia.Machines.ContextualCBPV.return_packet_keeps_residual

#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.grant_le_parent
#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.grant_le_request
#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.grant_unbounded
#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.native_tick_refines
#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.debit_conserves
#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.native_settle_refines
#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.settle_conserves
#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.settle_add
#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.close_once
#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.unit_step_refines
#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.unused_credit_is_not_spent

#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.native_debit_refines

#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.zero_debit_is_admin

#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.overdraw_preserves_pending_charge

#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.charged_step_refines

#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.unmetered_iff_unbounded_grant

#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.finite_grant_refuses_unmetered

#print axioms Mettapedia.Machines.ContextualCBPV.EpisodeAccounting.inherited_zero_is_not_unbounded

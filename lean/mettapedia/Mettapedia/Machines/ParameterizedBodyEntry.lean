import Mettapedia.Machines.ContextualCBPV
import Mettapedia.Machines.RegisterCode
import Mettapedia.Machines.SharedContinuation

/-!
# Direct entry into a parameterized computation body

The source binds an ordered list of distinct parameter identities to ready
values. The target initializes positional slots and leaves the remaining local
slots empty. The compiler's parameter-position map reads those slots. Neither
entry manufactures a named equation or interprets a ready operand.

The environment refinement joins entry to the existing contextual CBPV machine
for every physical slice. It does not prove the complete C compiler, native
pointer ownership, source-fuel accounting or mutable-source admission.

`CompletedCursor` independently refines an eager entered root to a reserved
root ticket around the maintained register worker. It preserves every bounded
worker slice and an independently supplied source price. Finality requires an
actual completed return or established logical-failure packet, with no pending
native packet or caller frontier. Later authority changes cannot reopen that
completed computation; reopening work or cancellation revokes its certificate.
The native packet classifier, source-price assignment, GC roots, and C loan and
acknowledgement operations remain native correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ParameterizedBodyEntry

variable {Name Value : Type} [DecidableEq Name]

abbrev Environment (Name Value : Type) := Name → Option Value

def locate (name : Name) : List Name → Option Nat
  | [] => none
  | first :: rest => if name = first then some 0 else (locate name rest).map Nat.succ

def slots (values : List Value) (locals : Nat) : List (Option Value) :=
  values.map some ++ List.replicate locals none

def source (parameters : List Name) (values : List Value) : Environment Name Value :=
  fun name => (parameters.zip values).lookup name

def target (parameters : List Name) (values : List Value) (locals : Nat) :
    Environment Name Value :=
  fun name => (locate name parameters).bind fun index => ((slots values locals)[index]?).join

def admitted (parameters : List Name) (values : List Value) : Bool :=
  decide (parameters.Nodup ∧ parameters.length = values.length)

theorem slots_prefix (values : List Value) (locals : Nat) :
    (slots values locals).take values.length = values.map some := by
  simp [slots]

theorem source_target_read (parameters : List Name) (values : List Value)
    (locals : Nat) (lengths : parameters.length = values.length) (name : Name) :
    source parameters values name = target parameters values locals name := by
  induction parameters generalizing values with
  | nil => cases values <;> simp_all [source, target, locate]
  | cons parameter rest ih =>
      cases values with
      | nil => simp at lengths
      | cons value values =>
          have restLengths : rest.length = values.length := by simpa using lengths
          by_cases same : name = parameter
          · subst name
            simp [source, target, locate, slots]
          · have previous := ih values restLengths
            have different : (name == parameter) = false := beq_eq_false_iff_ne.mpr same
            simp only [source, List.zip_cons_cons, List.lookup_cons, different]
            change source rest values name = _
            rw [previous]
            cases found : locate name rest <;>
              simp [target, locate, same, slots, found]

theorem environments_refine (parameters : List Name) (values : List Value)
    (locals : Nat) (lengths : parameters.length = values.length) :
    source parameters values = target parameters values locals := by
  funext name
  exact source_target_read parameters values locals lengths name

theorem admission_lengths (parameters : List Name) (values : List Value)
    (accepted : admitted parameters values = true) :
    parameters.length = values.length := by
  exact (of_decide_eq_true accepted).2

theorem admitted_environment_refines (parameters : List Name) (values : List Value)
    (locals : Nat) (accepted : admitted parameters values = true) :
    source parameters values = target parameters values locals := by
  exact environments_refine parameters values locals (admission_lengths parameters values accepted)

section Kernel

variable {Call Effect Fault Delay Suspension World Worker : Type}

abbrev Code := ContextualCBPV.Code Value Call Effect Fault Delay Suspension

variable (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension
    (Environment Name Value) World Worker)
    (world : World) (parameters : List Name) (values : List Value) (locals : Nat)
    (elaborate : Environment Name Value → Code (Value := Value) (Call := Call)
      (Effect := Effect) (Fault := Fault) (Delay := Delay) (Suspension := Suspension))

theorem kernel_entry_refines (lengths : parameters.length = values.length) :
    ContextualCBPV.initial (Worker := Worker) world (source parameters values)
        (elaborate (source parameters values)) =
      ContextualCBPV.initial (Worker := Worker) world (target parameters values locals)
        (elaborate (target parameters values locals)) := by
  rw [environments_refine parameters values locals lengths]

theorem kernel_slice_refines (lengths : parameters.length = values.length)
    (allowance : Nat) :
    (ContextualCBPV.core sem world (source parameters values)).runSlice allowance
        (ContextualCBPV.initial (Worker := Worker) world (source parameters values)
          (elaborate (source parameters values))) =
      (ContextualCBPV.core sem world (target parameters values locals)).runSlice allowance
        (ContextualCBPV.initial (Worker := Worker) world (target parameters values locals)
          (elaborate (target parameters values locals))) := by
  rw [environments_refine parameters values locals lengths]

end Kernel

namespace Controls

theorem distinct_parameters_preserve_shared_values :
    target ["x", "y"] [7, 7] 4 "x" = some 7 ∧
      target ["x", "y"] [7, 7] 4 "y" = some 7 := by decide +kernel

theorem distinct_parameters_are_not_collapsed :
    target ["x", "y"] [7, 9] 4 "x" = some 7 ∧
      target ["x", "y"] [7, 9] 4 "y" = some 9 := by decide +kernel

theorem duplicate_parameters_refused :
    admitted ["x", "x"] [7, 9] = false := by decide +kernel

theorem missing_argument_refused :
    admitted ["x", "y"] [7] = false := by decide +kernel

theorem fresh_local_is_not_a_parameter :
    target ["x"] [7] 16 "unbound" = none := by decide +kernel

end Controls

namespace CompletedCursor

open RegisterCode

variable {V L O P H Mark Context Fault Delay World Control Frame : Type}

structure Ticket (V Mark : Type) where
  arguments : List V
  entryMark : Mark
  deriving DecidableEq, Repr

structure EnteredRoot (V Mark : Type) extends Ticket V Mark where
  nextEquation : Nat
  matched : Bool
  deriving DecidableEq, Repr

def enteredRoot (ticket : Ticket V Mark) : EnteredRoot V Mark :=
  ⟨ticket, 1, true⟩

inductive Root (V Mark : Type) where
  | pending (ticket : Ticket V Mark)
  | installed (frame : EnteredRoot V Mark)
  deriving DecidableEq, Repr

/-- This bundles existing worker and continuation representations. It adds no
second binding store: all local reads use the retained worker's registers.
`established` is an actual tagged terminal report, never inferred from decline. -/
structure Live (V L O P H Context Fault Delay World Control Frame : Type) where
  worker : RegisterCode.Retained.State V L O P H
  native : Option (NativeCallReturn.Cursor V Fault Delay Context)
  callers : SharedContinuation.ArenaState Context Control Frame V
  world : World
  established : Option (NativeCallReturn.Source V Fault Delay)
  /-- Previously accrued source debit carried by this ownership boundary.
  RegisterCode's instruction/call fuel does not define a source price. -/
  spent : Nat

local notation "LiveState" => Live V L O P H Context Fault Delay World Control Frame
local notation "SourceState" => EnteredRoot V Mark × LiveState
local notation "TargetState" => Root V Mark × LiveState

/-- The source root has already passed entry and its debit. The target ticket
stands for that same entered root; no equation is matched a second time. -/
def decodeRoot : Root V Mark → EnteredRoot V Mark
  | .pending ticket => enteredRoot ticket
  | .installed frame => frame

def decode (state : TargetState) : SourceState := (decodeRoot state.1, state.2)

def promote (state : TargetState) : TargetState :=
  match state.1 with
  | .pending ticket => (.installed (enteredRoot ticket), state.2)
  | .installed _ => state

theorem promote_exact (state : TargetState) : decode (promote state) = decode state := by
  rcases state with ⟨root, live⟩
  cases root <;> rfl

theorem promote_idempotent (state : TargetState) : promote (promote state) = promote state := by
  rcases state with ⟨root, live⟩
  cases root <;> rfl

/-- Promotion changes no PC, slots, packet, caller DAG, world or debit. -/
theorem promote_preserves_live (state : TargetState) : (promote state).2 = state.2 := by
  rcases state with ⟨root, live⟩
  cases root <;> rfl

theorem promote_keeps_entry_mark (ticket : Ticket V Mark) (live : LiveState) :
    (decode (promote (.pending ticket, live))).1.entryMark = ticket.entryMark ∧
    (decode (promote (.pending ticket, live))).1.arguments = ticket.arguments ∧
    (decode (promote (.pending ticket, live))).1.nextEquation = 1 ∧
    (decode (promote (.pending ticket, live))).1.matched = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Private reservation/admission failure occurs before any worker transition.
A small-window refusal follows this same no-entry branch. -/
def reserve (reserved admitted : Bool) (ticket : Ticket V Mark) (live : LiveState) :
    Option TargetState :=
  if reserved && admitted then some (.pending ticket, live) else none

theorem reservation_refusal (admitted : Bool) (ticket : Ticket V Mark) (live : LiveState) :
    reserve false admitted ticket live = none := by simp [reserve]

theorem admission_refusal (reserved : Bool) (ticket : Ticket V Mark) (live : LiveState) :
    reserve reserved false ticket live = none := by simp [reserve]

/-- The eager source independently decodes one actual register instruction.
The continuation/native frontier must be handled before code can run again. -/
def sourceStep (sem : Sem V L O P H) (answer : H → List V → Option V)
    (state : SourceState) : Option SourceState :=
  if state.2.native.isSome || !state.2.callers.frontier.isEmpty ||
      state.2.established.isSome then none
  else match state.2.worker with
    | .running [] _ | .returned _ _ | .declined _ _ => none
    | .running (instruction :: rest) registers =>
        let next := match RegisterCode.step sem answer instruction registers with
          | none => .declined (instruction :: rest) registers
          | some (.next next) => .running rest next
          | some (.ret value) => .returned value registers
        some (state.1, { state.2 with worker := next })

/-- The deferred-root target uses the maintained worker directly. A refusal
has an actual residual and promotes its root before handing that state out. -/
def targetStep (sem : Sem V L O P H) (answer : H → List V → Option V)
    (state : TargetState) : Option TargetState :=
  if state.2.native.isSome || !state.2.callers.frontier.isEmpty ||
      state.2.established.isSome then none
  else ((RegisterCode.Retained.core sem answer).step state.2.worker).map fun next =>
    let moved := (state.1, { state.2 with worker := next })
    match next with
    | .declined _ _ => promote moved
    | _ => moved

theorem worker_step_refines (sem : Sem V L O P H) (answer : H → List V → Option V)
    (state : TargetState) :
    (targetStep sem answer state).map decode = sourceStep sem answer (decode state) := by
  rcases state with ⟨root, live⟩
  cases live with
  | mk worker native callers world established spent =>
      by_cases blocked : (native.isSome || !callers.frontier.isEmpty || established.isSome) = true
      · simp [targetStep, sourceStep, decode, blocked]
      · cases worker with
        | returned value registers =>
            simp [targetStep, sourceStep, RegisterCode.Retained.core, decode, blocked]
        | declined code registers =>
            simp [targetStep, sourceStep, RegisterCode.Retained.core, decode, blocked]
        | running code registers =>
            cases code with
            | nil => simp [targetStep, sourceStep, RegisterCode.Retained.core, decode, blocked]
            | cons instruction rest =>
                cases executed : RegisterCode.step sem answer instruction registers with
                | none =>
                    cases root <;> simp [targetStep, sourceStep, blocked,
                      RegisterCode.Retained.core, executed, decode, promote, decodeRoot]
                | some result =>
                    cases result <;> simp [targetStep, sourceStep, RegisterCode.Retained.core,
                      executed, decode, blocked]

def sourceCore (sem : Sem V L O P H) (answer : H → List V → Option V) : MachineCore SourceState where
  State := SourceState
  load := id
  step := sourceStep sem answer

def targetCore (sem : Sem V L O P H) (answer : H → List V → Option V) : MachineCore TargetState where
  State := TargetState
  load := id
  step := targetStep sem answer

/-- Every physical slice preserves full residual state and exact worker-step
count. Root promotion itself introduces no source or kernel debit. -/
theorem every_slice_refines (sem : Sem V L O P H) (answer : H → List V → Option V)
    (allowance : Nat) (state : TargetState) :
    let direct := MachineCore.runSlice (targetCore sem answer) allowance state
    let eager := MachineCore.runSlice (sourceCore sem answer) allowance (decode state)
    decode direct.1 = eager.1 ∧ direct.2 = eager.2 := by
  induction allowance generalizing state with
  | zero => exact ⟨rfl, rfl⟩
  | succ allowance ih =>
      have refinement := worker_step_refines sem answer state
      cases next : targetStep sem answer state with
      | none =>
          have stopped : sourceStep sem answer (decode state) = none := by
            simpa [next] using refinement.symm
          simp [MachineCore.runSlice, targetCore, sourceCore, next, stopped]
      | some moved =>
          have advanced : sourceStep sem answer (decode state) = some (decode moved) := by
            simpa [next] using refinement.symm
          simpa [MachineCore.runSlice, targetCore, sourceCore, next, advanced] using ih moved

/-- The source decides each transition's price. Deferred root storage preserves
that arbitrary account; worker transition counts do not select the price. -/
theorem priced_slice_refines (sem : Sem V L O P H) (answer : H → List V → Option V)
    (price : SourceState → Nat) (allowance : Nat) (state : TargetState) :
    MachineCore.sliceCost (targetCore sem answer) (fun live => price (decode live))
        allowance state =
      MachineCore.sliceCost (sourceCore sem answer) price allowance (decode state) := by
  induction allowance generalizing state with
  | zero => rfl
  | succ allowance ih =>
      have refinement := worker_step_refines sem answer state
      cases next : targetStep sem answer state with
      | none =>
          have stopped : sourceStep sem answer (decode state) = none := by
            simpa [next] using refinement.symm
          simp [MachineCore.sliceCost_succ, targetCore, sourceCore, next, stopped]
      | some moved =>
          have advanced : sourceStep sem answer (decode state) = some (decode moved) := by
            simpa [next] using refinement.symm
          simpa [MachineCore.sliceCost_succ, targetCore, sourceCore, next, advanced] using
            congrArg (price (decode state) + ·) (ih moved)

/-- Split execution resumes at the saved PC, retaining both the exact worker
account and any independent source account. -/
theorem split_execution_exact (sem : Sem V L O P H) (answer : H → List V → Option V)
    (price : SourceState → Nat) (first second : Nat)
    (packet : (Nat × TargetState) × Nat) :
    MachineCore.accountedPaidSlice (targetCore sem answer) (fun live => price (decode live))
        (first + second) packet =
      MachineCore.accountedPaidSlice (targetCore sem answer) (fun live => price (decode live))
        second (MachineCore.accountedPaidSlice (targetCore sem answer)
          (fun live => price (decode live)) first packet) :=
  MachineCore.accountedPaidSlice_add (targetCore sem answer)
    (fun live => price (decode live)) first second packet

/-- Boundary retention installs the root while preserving already-entered
native data and the caller DAG, rather than evaluating the source body again. -/
def retainNative (packet : NativeCallReturn.Cursor V Fault Delay Context)
    (state : TargetState) : TargetState :=
  promote (state.1, { state.2 with native := some packet })

theorem native_retention_exact
    (packet : NativeCallReturn.Cursor V Fault Delay Context) (state : TargetState) :
    decode (retainNative packet state) =
      ((decode state).1, { state.2 with native := some packet }) := by
  simp only [retainNative, promote_exact]
  rfl

/-- Resuming the actual native cursor selects precisely its remaining
contextual occurrences, using the independent ordered packet interpretation. -/
theorem native_resume_refines
    (packet : NativeCallReturn.Cursor V Fault Delay Context) (state : TargetState) :
    (retainNative packet state).2.native.map
        (fun cursor => (NativeCallReturn.read cursor).mapState NativeCallReturn.residual) =
      some (NativeCallReturn.referenceRead (NativeCallReturn.residual packet)) := by
  have kept := promote_preserves_live (state.1, { state.2 with native := some packet })
  simp only [retainNative, kept, Option.map_some]
  rw [NativeCallReturn.read_refines]

def logicalZero (state : TargetState) : TargetState :=
  (state.1, { state.2 with established := some .failure })

/-- Completed return provenance, or the worker's explicit logical-zero tag.
Declined/fallen-through state and absent frames never imply completion. -/
def completed (live : LiveState) : Option (NativeCallReturn.Source V Fault Delay) :=
  match live.established with
  | some .failure => some .failure
  | some _ => none
  | none => match live.worker with
    | .returned value _ => some (.one (.value .completed value))
    | _ => none

def exhausted (live : LiveState) : Bool :=
  live.native.isNone && live.callers.frontier.isEmpty && (completed live).isSome

/-- Source/host authority gates FUTURE worker transitions, not an earned
value whose entire retained stream is already structurally exhausted. -/
def permission (authority : Bool) (live : LiveState) : Bool := exhausted live || authority

theorem completed_finality_ignores_authority (live : LiveState)
    (done : exhausted live = true) (before after : Bool) :
    permission before live = true ∧ permission after live = true := by simp [permission, done]

theorem unfinished_requires_authority (live : LiveState)
    (pending : exhausted live = false) (authority : Bool) :
    permission authority live = authority := by simp [permission, pending]


/-- An entered root is structural metadata. A retained ticket is never an
untried equation or permission to match the original source body again. -/
def rootReady (root : Root V Mark) : Bool :=
  let frame := decodeRoot root
  frame.nextEquation == 1 && frame.matched

def structuralFinal (state : TargetState) : Bool := rootReady state.1 && exhausted state.2

def certify (state : TargetState) : Option (NativeCallReturn.Source V Fault Delay) :=
  if structuralFinal state then completed state.2 else none

/-- The live structural witness is checked after a loan. Source/host tokens
are needed only if another worker transition can occur. -/
def guardedStep (authority : Bool) (sem : Sem V L O P H)
    (answer : H → List V → Option V) (state : TargetState) : Option TargetState :=
  if structuralFinal state then none
  else if authority then targetStep sem answer state else none

theorem stale_state_runs_no_worker (sem : Sem V L O P H)
    (answer : H → List V → Option V) (state : TargetState) :
    guardedStep false sem answer state = none := by simp [guardedStep]

theorem structurally_final_is_inert (sem : Sem V L O P H)
    (answer : H → List V → Option V) (state : TargetState)
    (terminal : structuralFinal state = true) (authority : Bool) :
    guardedStep authority sem answer state = none := by simp [guardedStep, terminal]

/-- Actual earned values remain inert even if every future primitive and
callee interpretation changes. Refusal is not used as successful provenance. -/
theorem returned_readback_ignores_authority
    (before after : Sem V L O P H) (old new : H → List V → Option V)
    (value : V) (registers : Regs V) :
    RegisterCode.Retained.readback before old (.returned value registers) =
      RegisterCode.Retained.readback after new (.returned value registers) := rfl

theorem returned_slice_never_reenters
    (sem : Sem V L O P H) (answer : H → List V → Option V)
    (value : V) (registers : Regs V) (allowance incoming : Nat) :
    MachineCore.paidSlice (RegisterCode.Retained.core sem answer) allowance
      (incoming, .returned value registers) = (incoming, .returned value registers) :=
  RegisterCode.Retained.observed_paidSlice sem answer (.returned value registers)
    (some (.ret value)) rfl allowance incoming

theorem promotion_keeps_finality (state : TargetState) :
    structuralFinal (promote state) = structuralFinal state := by
  rcases state with ⟨root, live⟩
  cases root <;> rfl

theorem no_native_can_be_skipped (root : Root V Mark) (live : LiveState)
    (packet : NativeCallReturn.Cursor V Fault Delay Context)
    (pending : live.native = some packet) :
    structuralFinal (root, live) = false := by simp [structuralFinal, exhausted, pending]

theorem no_caller_or_alternative_can_be_skipped (root : Root V Mark) (live : LiveState)
    (task : SharedContinuation.RootTask Context Control)
    (rest : List (SharedContinuation.RootTask Context Control))
    (pending : live.callers.frontier = task :: rest) :
    structuralFinal (root, live) = false := by simp [structuralFinal, exhausted, pending]

/-- Reservation failure precedes even an opaque worker or native entry action.
The action's result may contain arbitrary effects and accounting observations. -/
def enterReserved {Result : Type} (reserved admitted : Bool)
    (ticket : Ticket V Mark) (live : LiveState) (run : TargetState → Result) : Option Result :=
  (reserve reserved admitted ticket live).map run

theorem reservation_precedes_all_work {Result : Type} (admitted : Bool)
    (ticket : Ticket V Mark) (live : LiveState) (run : TargetState → Result) :
    enterReserved false admitted ticket live run = none := by simp [enterReserved, reserve]

/-- Cancellation is a terminal control report, not logical exhaustion. The
owner still retains its actual worker and caller state for disposal. -/
def cancel (state : TargetState) : TargetState :=
  (state.1, { state.2 with established := some .interrupted })

theorem cancellation_revokes_certificate (state : TargetState) :
    certify (cancel state) = none := by
  simp [certify, structuralFinal, exhausted, completed, cancel]

/-- Reopening or transferring an untried alternative revokes finality by
changing the live frontier, without modifying the established value's syntax. -/
def reopen (task : SharedContinuation.RootTask Context Control) (state : TargetState) : TargetState :=
  (state.1, { state.2 with callers := { state.2.callers with
    frontier := task :: state.2.callers.frontier } })

theorem reopened_work_revokes_certificate (task : SharedContinuation.RootTask Context Control)
    (state : TargetState) : certify (reopen task state) = none := by
  simp [certify, structuralFinal, exhausted, reopen]

namespace Controls

abbrev TestLive := Live Nat Nat Unit Unit Unit Nat String Nat Nat Nat Nat
abbrev TestRoot := Root Nat Nat

def emptyCallers : SharedContinuation.ArenaState Nat Nat Nat Nat := ⟨[], [], []⟩
def registers : Regs Nat := fun slot => if slot = 0 then some 7 else none

def earned : TestLive :=
  ⟨.returned 7 registers, none, emptyCallers, 13, none, 17⟩
def ticket : Ticket Nat Nat := ⟨[7, 7, 9], 5⟩
def state : TestRoot × TestLive := (.pending ticket, earned)

theorem completed_value_has_structural_finality :
    structuralFinal state = true ∧ certify state = some (.one (.value .completed 7)) := by decide

theorem shared_and_distinct_arguments_survive_promotion :
    (decode (promote state)).1.arguments = [7, 7, 9] ∧
    (promote state).2.world = 13 ∧ (promote state).2.spent = 17 := by decide

/-- The original mark predates work; substituting a later materialization
mark changes the retained ownership interval even if the value agrees. -/
theorem replacing_entry_mark_is_detected :
    (decode (promote state)).1.entryMark ≠ 99 := by decide

def refused : TestLive := { earned with worker := .declined [.ret (.reg 0)] registers }

theorem refusal_is_not_logical_zero :
    completed refused = none ∧ structuralFinal (.pending ticket, refused) = false := by decide

theorem explicit_logical_zero_has_its_own_tag :
    certify (logicalZero (.pending ticket, refused)) = some .failure := by decide

def held : NativeCallReturn.Cursor Nat String Nat Nat := ⟨.one (.conditional 7 42), 4, 0⟩
def withNative : TestLive := { earned with native := some held }

theorem conditional_packet_is_still_pending :
    structuralFinal (.pending ticket, withNative) = false ∧
    (retainNative held state).2.native = some held := by decide

def enteredNative : NativeCallReturn.Cursor Nat String Nat Nat :=
  ⟨.frontier .completed #[5, 7, 7, 9], 4, 1⟩

theorem native_frontier_keeps_offset_order_and_duplicates :
    (retainNative enteredNative state).2.native = some enteredNative ∧
      NativeCallReturn.residual enteredNative =
        ([(4, .value .completed 7), (4, .value .completed 7),
          (4, .value .completed 9)], .complete) := by decide

def doubleFrontier : TestLive :=
  { earned with callers := ⟨[], [⟨4, 2, 0⟩, ⟨4, 2, 0⟩], []⟩ }

theorem duplicated_alternatives_are_not_final :
    structuralFinal (.pending ticket, doubleFrontier) = false ∧
    (promote (.pending ticket, doubleFrontier)).2.callers.frontier.length = 2 := by decide

/-- Dropping the root ticket would replace an entered equation by an
unmatched one, permitting replay of the original body. -/
theorem resetting_root_entry_is_detected :
    (decode state).1.nextEquation ≠ 0 ∧ (decode state).1.matched = true := by decide

def remainingCode : TestLive :=
  { earned with worker := .running [.ret (.reg 0)] registers }

theorem remaining_instruction_prevents_finality :
    structuralFinal (.pending ticket, remainingCode) = false := by decide

/-- Rewinding after a paid prefix produces a different retained PC/code word. -/
theorem rewinding_residual_is_detected :
    (.declined [.ret (.reg 0)] registers : RegisterCode.Retained.State Nat Nat Unit Unit Unit) ≠
      .declined [.move 0 (.lit 1), .ret (.reg 0)] registers := by
  intro impossible
  cases impossible

/-- The saved suffix reads the slot already written by the prefix. A rewind
really changes its result, even though both executions eventually return. -/
private def sem : Sem Nat Nat Unit Unit Unit where
  patReads _ := []
  patSlots _ := []
  lit := id
  op _ _ := none
  truth _ := none
  bindLet _ _ _ := none
  bindLet_frame := by intro p value before after refused; simp at refused
  bindLet_local := by intro p value before after agree; exact Option.Rel.none
  enter _ _ := none

private def noCall (_ : Unit) (_ : List Nat) : Option Nat := none

theorem rewinding_changes_the_earned_value :
    RegisterCode.Retained.observe
        (MachineCore.runSlice (RegisterCode.Retained.core sem noCall) 2
          (.running [.ret (.reg 0)] registers)).1 = some (some (.ret 7)) ∧
    RegisterCode.Retained.observe
        (MachineCore.runSlice (RegisterCode.Retained.core sem noCall) 2
          (.running [.move 0 (.lit 1), .ret (.reg 0)] registers)).1 =
      some (some (.ret 1)) := by exact ⟨rfl, rfl⟩

theorem interrupted_report_cannot_become_logical_zero :
    completed ({ earned with established := some .interrupted } : TestLive) = none ∧
      certify (.pending ticket, { earned with established := some .interrupted }) = none := by
  decide

theorem invalid_report_cannot_become_completed_value :
    completed ({ earned with established := some .invalid } : TestLive) = none ∧
      certify (.pending ticket, { earned with established := some .invalid }) = none := by
  decide

theorem logical_zero_cannot_drop_pending_native :
    certify (logicalZero (.pending ticket, withNative)) = none := by decide

theorem deleting_pending_callers_is_detected :
    certify (.pending ticket, doubleFrontier) = none ∧
      certify (.pending ticket, { doubleFrontier with callers := emptyCallers }) =
        some (.one (.value .completed 7)) := by decide

theorem reservation_failure_does_not_enter_effect :
    enterReserved false true ticket earned (fun _ => 100 + 1) = none := by decide

theorem unyield_like_work_reopens_stream :
    certify (reopen ⟨4, 2, 0⟩ state) = none := by decide

end Controls

end CompletedCursor

end Mettapedia.Machines.ParameterizedBodyEntry

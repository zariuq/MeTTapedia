import Mettapedia.Machines.Kernel.InvocationContext

/-!
# An installed program's Network grant

The provider sees the run through its held lifecycle query and the invoking
task through the kernel's transport stamp. Shell binds a program row under
its current run. Use of the register Web lane requires that run to be live
and the stamped task to match the grant. Files continues to use run-scoped
authority with either continuation strategy.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.ProgramNetworkGrant

open InvocationContext (Selection)

inductive Observation where
  | unavailable
  | detached (run : Nat)
  | live (run : Nat)
  deriving DecidableEq

def Observation.run : Observation → Option Nat
  | .unavailable => none
  | .detached run | .live run => some run

structure Row where
  target : Nat
  enrolled : Option Nat
  deriving DecidableEq

def bind (row : Row) (observed : Observation) (fromShell : Bool) (run : Nat) : Row :=
  if fromShell && run != 0 && observed.run == some run then
    { row with enrolled := some run }
  else row

def retire (row : Row) (observed : Observation) (run : Nat) : Row :=
  if observed = .detached run ∧ row.enrolled = some run then
    { row with enrolled := none }
  else row

def allowed (row : Row) (observed : Observation) (dispatch : Selection) : Bool :=
  match observed with
  | .live run =>
    match dispatch.context row.target run with
    | some caller => caller.task.id == run && row.enrolled == some run
    | none => false
  | _ => false

theorem foreign_issuer_preserves (row : Row) (observed : Observation) (run : Nat) :
    bind row observed false run = row := by
  simp [bind]

theorem stale_bind_preserves (row : Row) (current stale : Nat) (issuer : Bool)
    (different : current ≠ stale) :
    bind row (.live current) issuer stale = row ∧
      bind row (.detached current) issuer stale = row := by
  simp [bind, Observation.run, different]

theorem stale_exit_preserves (target current stale : Nat) (different : current ≠ stale) :
    retire ⟨target, some current⟩ (.detached current) stale = ⟨target, some current⟩ := by
  simp [retire, different]

theorem allowed_requires_current_grant (row : Row) (current : Nat) (dispatch : Selection)
    (accepted : allowed row (.live current) dispatch = true) :
    row.enrolled = some current := by
  cases selected : dispatch.context row.target current with
  | none => simp [allowed, selected] at accepted
  | some caller =>
    exact (by simpa [allowed, selected] using accepted :
      caller.task.id = current ∧ row.enrolled = some current).2

theorem main_allowed_iff (row : Row) (current : Nat)
    (targetValid : row.target ≠ 0) (currentValid : current ≠ 0) :
    allowed row (.live current) (.main row.target current) = true ↔
      row.enrolled = some current := by
  simp [allowed, InvocationContext.Selection.context, targetValid, currentValid]

theorem rebirth_requires_new_grant (target old fresh : Nat)
    (targetValid : target ≠ 0) (freshValid : fresh ≠ 0) (different : old ≠ fresh) :
    allowed ⟨target, some old⟩ (.live fresh) (.main target fresh) = false := by
  simp [allowed, InvocationContext.Selection.context, targetValid, freshValid, different]

theorem worker_cannot_use_main_grant (row : Row) (run task : Nat) (attached : Bool)
    (different : task ≠ run) :
    allowed row (.live run) (.worker row.target task run attached) = false := by
  by_cases attachedHere : row.target ≠ 0 ∧ run ≠ 0 ∧ task ≠ 0 ∧ task ≠ run ∧ attached = true
  · have selected : (Selection.worker row.target task run attached).context row.target run =
        some ⟨run, ⟨task, run, .worker⟩⟩ := by
      simpa [InvocationContext.Selection.context] using attachedHere
    simp [allowed, selected, different]
  · have selected : (Selection.worker row.target task run attached).context row.target run = none := by
      simp [InvocationContext.Selection.context, attachedHere]
    simp [allowed, selected]

example :
    let row := bind ⟨42, none⟩ (.detached 51) true 51
    allowed row (.live 51) (.main 42 51) = true ∧
      allowed row (.live 52) (.main 42 52) = false := by decide

/-! ## Staged activation

Shell settles the Files bind first. A launch that requests Network settles a
separate reply before it can activate. Identifiers come from RPC admission.
-/

namespace Launch

inductive Phase where
  | files | network | ready | active | refused
  deriving DecidableEq

inductive Event where
  | filesReply (id : Nat) (ok : Bool)
  | networkReply (id : Nat) (ok : Bool)
  | activate
  deriving DecidableEq

def step (filesId : Nat) (networkId : Option Nat) (phase : Phase) (event : Event) : Phase :=
  match phase, event with
  | .files, .filesReply id ok =>
      if id = filesId then
        if ok then (if networkId.isSome then .network else .ready) else .refused
      else phase
  | .network, .networkReply id ok =>
      if networkId = some id then (if ok then .ready else .refused) else phase
  | .ready, .activate => .active
  | _, _ => phase

private def PastFiles (phase : Phase) : Prop :=
  phase = .network ∨ phase = .ready ∨ phase = .active

private def PastNetwork (phase : Phase) : Prop :=
  phase = .ready ∨ phase = .active

private theorem files_step {filesId : Nat} {networkId : Option Nat} {phase : Phase}
    {event : Event} (past : PastFiles (step filesId networkId phase event)) :
    PastFiles phase ∨ event = .filesReply filesId true := by
  cases phase with
  | files =>
    cases event with
    | filesReply id ok =>
      by_cases correct : id = filesId <;> cases ok <;> cases networkId <;>
        simp_all [step, PastFiles]
    | networkReply => simp [step, PastFiles] at past
    | activate => simp [step, PastFiles] at past
  | network => exact Or.inl (Or.inl rfl)
  | ready => exact Or.inl (Or.inr (Or.inl rfl))
  | active => exact Or.inl (Or.inr (Or.inr rfl))
  | refused => cases event <;> simp [step, PastFiles] at past

private theorem network_step {filesId networkId : Nat} {phase : Phase} {event : Event}
    (past : PastNetwork (step filesId (some networkId) phase event)) :
    PastNetwork phase ∨ event = .networkReply networkId true := by
  cases phase with
  | files =>
    cases event with
    | filesReply id ok =>
      by_cases correct : id = filesId <;> cases ok <;> simp_all [step, PastNetwork]
    | networkReply => simp [step, PastNetwork] at past
    | activate => simp [step, PastNetwork] at past
  | network =>
    cases event with
    | filesReply => simp [step, PastNetwork] at past
    | networkReply id ok =>
      by_cases correct : networkId = id <;> cases ok <;> simp_all [step, PastNetwork]
    | activate => simp [step, PastNetwork] at past
  | ready => exact Or.inl (Or.inl rfl)
  | active => exact Or.inl (Or.inr rfl)
  | refused => cases event <;> simp [step, PastNetwork] at past

private theorem witness {State Label : Type} (step : State → Label → State)
    (P : State → Prop) (wanted : Label)
    (one : ∀ s e, P (step s e) → P s ∨ e = wanted)
    (state : State) (events : List Label) (after : P (events.foldl step state)) :
    P state ∨ wanted ∈ events := by
  induction events generalizing state with
  | nil => exact Or.inl after
  | cons event rest ih =>
    rcases ih (step state event) after with h | h
    · rcases one state event h with h | rfl
      · exact Or.inl h
      · exact Or.inr (List.Mem.head _)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem activation_requires_files (filesId : Nat) (networkId : Option Nat) (events : List Event)
    (active : events.foldl (step filesId networkId) .files = .active) :
    .filesReply filesId true ∈ events := by
  simpa [PastFiles] using witness (step filesId networkId) PastFiles (.filesReply filesId true)
    (fun _ _ => files_step) .files events (Or.inr (Or.inr active))

theorem activation_requires_network (filesId networkId : Nat) (events : List Event)
    (active : events.foldl (step filesId (some networkId)) .files = .active) :
    .networkReply networkId true ∈ events := by
  simpa [PastNetwork] using witness (step filesId (some networkId)) PastNetwork
    (.networkReply networkId true) (fun _ _ => network_step) .files events (Or.inr active)

example : [Event.filesReply 7 true, .networkReply 9 true, .activate].foldl
    (step 7 (some 9)) .files = .active := by decide
example : [Event.filesReply 7 true, .networkReply 7 true, .activate].foldl
    (step 7 (some 9)) .files = .network := by decide
example : [Event.filesReply 7 true, .activate].foldl (step 7 none) .files = .active := by decide

#print axioms activation_requires_files
#print axioms activation_requires_network

end Launch

#print axioms stale_bind_preserves
#print axioms stale_exit_preserves
#print axioms allowed_requires_current_grant
#print axioms rebirth_requires_new_grant
#print axioms worker_cannot_use_main_grant

end Mettapedia.Machines.Kernel.ProgramNetworkGrant

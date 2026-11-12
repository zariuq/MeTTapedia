import Mettapedia.Logic.Relation.FiniteReachability

/-!
# Profile admission and local completion recovery

A native provider path has two independent boundaries.  First, a finite module
and capability graph determines whether the selected profile is supported.
Admission checks the declared transitive requirements before constructing a
provider state.  An unsupported profile therefore has no provider request to
roll back or retry.  Import spelling and import-error classification are local
admission concerns, not evidence about completion recovery.

Second, an admitted call retains its received answer across local write
rollback.  Only initial submission increments the provider-request count.
After any finite number of local rollbacks, a subsequent successful local
commit and publication settles the same answer without another provider
request.  The progress assumption is exactly that finite rollback prefix
followed by a successful commit while the owned continuation remains alive;
there is no exactly-once external-execution claim.

The recovery transitions are the canonical machine counterpart of the existing
completion-recovery model.  The graph is deliberately small and concrete; it is
not a universal module system or a correctness proof of a runtime loader.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProfileRecoveryContract

/-! ## Finite dependency and capability admission -/

inductive Module where
  | nativeLlm | accounting | lifetime | policy | path
  | chatgptAgent | requestContext | libImport
  deriving DecidableEq, Repr

def allModules : List Module :=
  [.nativeLlm, .accounting, .lifetime, .policy, .path,
    .chatgptAgent, .requestContext, .libImport]

instance : Fintype Module where
  elems := allModules.toFinset
  complete module := by cases module <;> simp [allModules]

/-- Static imports relevant to the native command path. -/
def dependencies : Module → List Module
  | .nativeLlm => [.accounting, .chatgptAgent]
  | .accounting => [.lifetime]
  | .lifetime => [.policy]
  | .policy => [.path]
  | .chatgptAgent => [.requestContext]
  | .requestContext => [.libImport]
  | .path | .libImport => []

inductive Reachable (edges : Module → List Module) : Module → Module → Prop where
  | refl (start : Module) : Reachable edges start start
  | step {start middle target : Module} (edge : middle ∈ edges start)
      (rest : Reachable edges middle target) : Reachable edges start target

namespace Reachable

theorem trans {edges : Module → List Module} {start middle target : Module}
    (first : Reachable edges start middle) (second : Reachable edges middle target) :
    Reachable edges start target := by
  induction first with
  | refl => exact second
  | step edge _ ih => exact .step edge (ih second)

theorem iff_reflTransGen {edges : Module → List Module} {start target : Module} :
    Reachable edges start target ↔
      Relation.ReflTransGen (fun source next => next ∈ edges source) start target := by
  constructor
  · intro reachable
    induction reachable with
    | refl => exact .refl
    | step edge _ ih => exact .head edge ih
  · intro reachable
    induction reachable with
    | refl => exact .refl _
    | tail _ edge ih => exact ih.trans (.step edge (.refl _))

end Reachable

structure Profile where
  supported : Module → Bool
  required : List Module
  roots : List Module

/-- A profile declares its closure explicitly.  The graph independently
provides reachability witnesses for auditing that declaration. -/
def Closed (profile : Profile) : Prop :=
  ∀ {start target : Module}, start ∈ profile.roots →
    Reachable dependencies start target →
      target ∈ profile.required ∧ profile.supported target = true

/-- The independently computed transitive closure of the declared roots. -/
def dependencyClosure (profile : Profile) : Finset Module :=
  Mettapedia.Logic.Relation.reachSet
    (fun source => (dependencies source).toFinset) profile.roots.toFinset

theorem mem_dependencyClosure {profile : Profile} {target : Module} :
    target ∈ dependencyClosure profile ↔
      ∃ start ∈ profile.roots, Reachable dependencies start target := by
  rw [dependencyClosure, Mettapedia.Logic.Relation.mem_reachSet_iff]
  simp only [List.mem_toFinset]
  constructor
  · rintro ⟨start, member, reachable⟩
    exact ⟨start, member, Reachable.iff_reflTransGen.mpr reachable⟩
  · rintro ⟨start, member, reachable⟩
    exact ⟨start, member, Reachable.iff_reflTransGen.mp reachable⟩

theorem closed_iff_dependencyClosure (profile : Profile) :
    Closed profile ↔ ∀ target ∈ dependencyClosure profile,
      target ∈ profile.required ∧ profile.supported target = true := by
  constructor
  · intro closed target member
    obtain ⟨start, root, reachable⟩ := mem_dependencyClosure.mp member
    exact closed root reachable
  · intro closed start target root reachable
    exact closed target (mem_dependencyClosure.mpr ⟨start, root, reachable⟩)

def heSupported : Module → Bool
  | .libImport => false
  | _ => true

def heProfile : Profile := ⟨heSupported, allModules, [.nativeLlm]⟩
def pettaProfile : Profile := ⟨fun _ => true, allModules, [.nativeLlm]⟩

/-- The path-import failure has a direct-module fallback.  The old classifier
does not recognize the HE `unknownLibrary` error; the repaired one does. -/
inductive ImportError where
  | expectsModuleName | unknownLibrary
  deriving DecidableEq, Repr

def oldFallback : ImportError → Bool
  | .expectsModuleName => true
  | .unknownLibrary => false

def repairedFallback : ImportError → Bool
  | .expectsModuleName | .unknownLibrary => true

theorem old_path_fallback_refused : oldFallback .unknownLibrary = false := rfl
theorem repaired_path_fallback_admitted : repairedFallback .unknownLibrary = true := rfl

/-- After the path boundary, the native HE profile still has a reachable,
unsupported `lib_import` dependency through the ChatGPT/request-context chain. -/
theorem he_missing_reachable_capability :
    Reachable dependencies .nativeLlm .libImport ∧ heSupported .libImport = false := by
  constructor
  · exact Reachable.step (start := .nativeLlm) (middle := .chatgptAgent) (target := .libImport)
      (by decide) <| Reachable.step (start := .chatgptAgent) (middle := .requestContext)
        (target := .libImport) (by decide) <|
          Reachable.step (start := .requestContext) (middle := .libImport)
            (target := .libImport) (by decide) (.refl .libImport)
  · rfl

theorem he_not_closed : ¬ Closed heProfile := by
  intro closed
  have missing := closed (start := .nativeLlm) (target := .libImport)
    (by simp [heProfile]) he_missing_reachable_capability.1
  simp [heProfile, heSupported] at missing

theorem petta_closed : Closed pettaProfile := by
  intro start target _ _
  constructor
  · simp [pettaProfile, allModules]
    cases target <;> simp
  · rfl

/-! ## Captured answer and local settlement -/

universe u v

variable {Id : Type u} {Payload : Type v}

structure Answer (Id : Type u) (Payload : Type v) where
  identity : Id
  value : Payload
  deriving DecidableEq, Repr

inductive Phase where
  | ready | submitted | received | retryLocal | committed | published
  deriving DecidableEq, Repr

inductive WriteResult where
  | committed | rolledBack
  deriving DecidableEq, Repr

inductive Event (Id : Type u) (Payload : Type v) where
  | submit
  | receive (answer : Answer Id Payload)
  | write (result : WriteResult)
  | publish
  deriving DecidableEq, Repr

structure State (Id : Type u) (Payload : Type v) where
  identity : Id
  phase : Phase
  retained : Option (Answer Id Payload)
  durable : Option (Answer Id Payload)
  providerRequests : Nat
  settlements : Nat

def initial (answer : Answer Id Payload) : State Id Payload :=
  ⟨answer.identity, .ready, none, none, 0, 0⟩

def afterReceive (answer : Answer Id Payload) : State Id Payload :=
  ⟨answer.identity, .received, some answer, none, 1, 0⟩

def retryState (answer : Answer Id Payload) : State Id Payload :=
  { afterReceive answer with phase := .retryLocal }

def owned [DecidableEq Id] (state : State Id Payload) (answer : Answer Id Payload) : Bool :=
  answer.identity == state.identity

def writing : Phase → Bool
  | .received | .retryLocal => true
  | _ => false

def commit (state : State Id Payload) (phase : Phase) : State Id Payload :=
  { state with phase := phase, durable := state.retained }

def step [DecidableEq Id] [DecidableEq Payload]
    (state : State Id Payload) : Event Id Payload → State Id Payload
  | .submit =>
      if state.phase == .ready then
        { state with phase := .submitted, providerRequests := state.providerRequests + 1 }
      else state
  | .receive answer =>
      if state.phase == .submitted && owned state answer then
        { state with phase := .received, retained := some answer }
      else state
  | .write result =>
      if writing state.phase && state.retained.isSome then
        match result with
        | .committed => commit state .committed
        | .rolledBack => { state with phase := .retryLocal }
      else state
  | .publish =>
      if state.phase == .committed && state.durable == state.retained &&
          state.retained.isSome then
        { state with phase := .published, settlements := state.settlements + 1 }
      else state

def run [DecidableEq Id] [DecidableEq Payload]
    (state : State Id Payload) : List (Event Id Payload) → State Id Payload
  | [] => state
  | event :: rest => run (step state event) rest

theorem run_append [DecidableEq Id] [DecidableEq Payload]
    (state : State Id Payload) (first second : List (Event Id Payload)) :
    run state (first ++ second) = run (run state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons event rest ih => exact ih (step state event)

/-- More useful than an event-classification helper: once submitted, no event
can return the call to its unsubmitted state. -/
theorem step_never_rearms [DecidableEq Id] [DecidableEq Payload]
    (state : State Id Payload) (event : Event Id Payload)
    (used : state.phase ≠ .ready) : (step state event).phase ≠ .ready := by
  cases event with
  | submit => simp [step, used]
  | receive answer =>
      simp only [step]
      split
      · simp
      · exact used
  | write result =>
      simp only [step]
      split
      · cases result <;> simp [commit]
      · exact used
  | publish =>
      simp only [step]
      split
      · simp
      · exact used

theorem used_call_keeps_request_count [DecidableEq Id] [DecidableEq Payload]
    (state : State Id Payload) (event : Event Id Payload)
    (used : state.phase ≠ .ready) :
    (step state event).providerRequests = state.providerRequests := by
  cases event with
  | submit => simp [step, used]
  | receive answer =>
      simp only [step]
      split <;> rfl
  | write result =>
      simp only [step]
      split
      · cases result <;> rfl
      · rfl
  | publish =>
      simp only [step]
      split <;> rfl

theorem retries_cannot_make_another_provider_request [DecidableEq Id] [DecidableEq Payload]
    (state : State Id Payload) (events : List (Event Id Payload))
    (used : state.phase ≠ .ready) :
    (run state events).providerRequests = state.providerRequests := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      rw [run, ih (step state event) (step_never_rearms state event used)]
      exact used_call_keeps_request_count state event used

theorem submit_receive [DecidableEq Id] [DecidableEq Payload]
    (answer : Answer Id Payload) :
    run (initial answer) [.submit, .receive answer] = afterReceive answer := by
  simp [run, step, initial, afterReceive, owned]

theorem first_rollback [DecidableEq Id] [DecidableEq Payload]
    (answer : Answer Id Payload) :
    step (afterReceive answer) (.write .rolledBack) = retryState answer := by
  simp [step, afterReceive, retryState, writing]

theorem rollback_preserves_retry [DecidableEq Id] [DecidableEq Payload]
    (answer : Answer Id Payload) :
    step (retryState answer) (.write .rolledBack) = retryState answer := by
  simp [step, retryState, afterReceive, writing]

theorem arbitrary_rollbacks_retain_retry [DecidableEq Id] [DecidableEq Payload]
    (answer : Answer Id Payload) (count : Nat) :
    run (retryState answer) (List.replicate count (.write .rolledBack)) = retryState answer := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [List.replicate_succ, run, rollback_preserves_retry] using ih

def rollbackPrefix [DecidableEq Id] [DecidableEq Payload]
    (_answer : Answer Id Payload) (count : Nat) : List (Event Id Payload) :=
  [.write .rolledBack] ++ List.replicate count (.write .rolledBack)

def recoveryEvents [DecidableEq Id] [DecidableEq Payload]
    (answer : Answer Id Payload) (count : Nat) : List (Event Id Payload) :=
  rollbackPrefix answer count ++ [.write .committed, .publish]

theorem rollback_prefix [DecidableEq Id] [DecidableEq Payload]
    (answer : Answer Id Payload) (count : Nat) :
    run (afterReceive answer) (rollbackPrefix answer count) = retryState answer := by
  rw [rollbackPrefix, run_append]
  simp [run, first_rollback, arbitrary_rollbacks_retain_retry]

theorem settle_after_rollbacks [DecidableEq Id] [DecidableEq Payload]
    (answer : Answer Id Payload) :
    let final := run (retryState answer) [.write .committed, .publish]
    final.phase = .published ∧ final.providerRequests = 1 ∧ final.settlements = 1 ∧
      final.retained = some answer ∧ final.durable = some answer ∧
        final.identity = answer.identity := by
  simp [run, step, retryState, afterReceive, writing, commit]

/-- Conditional finite progress: for every finite rollback count, if the next
local commit succeeds, the originally received answer is settled once. -/
theorem rollback_recovery_for_any_finite_wait [DecidableEq Id] [DecidableEq Payload]
    (answer : Answer Id Payload) (count : Nat) :
    let final := run (afterReceive answer) (recoveryEvents answer count)
    final.phase = .published ∧ final.providerRequests = 1 ∧ final.settlements = 1 ∧
      final.retained = some answer ∧ final.durable = some answer ∧
        final.identity = answer.identity := by
  simp only [recoveryEvents, run_append, rollback_prefix]
  exact settle_after_rollbacks answer

/-- Repeating either delivery event after publication adds no settlement. -/
theorem repeated_settlement_is_ignored [DecidableEq Id] [DecidableEq Payload]
    (state : State Id Payload) (published : state.phase = .published) :
    step state .publish = state ∧ step state (.write .committed) = state := by
  simp [step, published, writing]

/-! ## Compose admission with recovery -/

/-- The historical checker trusted the caller's declaration and checked only
that the roots occurred in it.  It is retained as the executable old rule. -/
def legacyAdmit (profile : Profile) (answer : Answer Id Payload) : Option (State Id Payload) :=
  if profile.required.all profile.supported &&
      profile.roots.all fun root => profile.required.contains root then
    some (initial answer)
  else none

/-- Boolean closure check, enumerated over the finite module universe. -/
def closureChecked (profile : Profile) : Bool :=
  allModules.all fun target =>
    if target ∈ dependencyClosure profile then
      profile.required.contains target && profile.supported target
    else true

/-- Admission computes the transitive dependency closure itself and accepts
only when every reachable module is declared and supported. -/
def admit (profile : Profile) (answer : Answer Id Payload) : Option (State Id Payload) :=
  if closureChecked profile then some (initial answer) else none

theorem admit_some_closed (profile : Profile) (answer : Answer Id Payload)
    {state : State Id Payload} (admitted : admit profile answer = some state) :
    Closed profile := by
  apply (closed_iff_dependencyClosure profile).mpr
  intro target member
  have targetInAll : target ∈ allModules := by cases target <;> simp [allModules]
  unfold admit closureChecked at admitted
  split at admitted
  · rename_i checked
    have checkedTarget := List.all_eq_true.mp checked target targetInAll
    simp only [member, ↓reduceIte, Bool.and_eq_true] at checkedTarget
    exact ⟨by simpa using checkedTarget.1, checkedTarget.2⟩
  · contradiction

def providerEffects (admitted : Option (State Id Payload)) : Nat :=
  match admitted with
  | none => 0
  | some state => state.providerRequests

/-- Unsupported HE admission refuses before a provider state or effect exists. -/
theorem he_admission_refused_before_effects (answer : Answer Id Payload) :
    admit heProfile answer = none ∧ providerEffects (admit heProfile answer) = 0 := by
  exact ⟨rfl, rfl⟩

theorem petta_admission_succeeds (answer : Answer Id Payload) :
    admit pettaProfile answer = some (initial answer) := by
  rfl

/-- Historical composition validated the declared roots without binding them
to the native LLM entrypoint that this consumer proceeds to execute. -/
def legacyRecoverSupported [DecidableEq Id] [DecidableEq Payload]
    (profile : Profile) (answer : Answer Id Payload) (rollbacks : Nat) :
    Option (State Id Payload) :=
  (admit profile answer).map fun start =>
    run start ([.submit, .receive answer] ++ recoveryEvents answer rollbacks)

/-- Closure is relative to declared roots. This consumer actually executes the
native LLM path, so it must also require that entrypoint among those roots. -/
def recoverSupported [DecidableEq Id] [DecidableEq Payload]
    (profile : Profile) (answer : Answer Id Payload) (rollbacks : Nat) :
    Option (State Id Payload) :=
  if Module.nativeLlm ∈ profile.roots then
    legacyRecoverSupported profile answer rollbacks
  else none

theorem recoverSupported_missing_entrypoint [DecidableEq Id] [DecidableEq Payload]
    (profile : Profile) (answer : Answer Id Payload) (rollbacks : Nat)
    (missing : Module.nativeLlm ∉ profile.roots) :
    recoverSupported profile answer rollbacks = none := by
  simp [recoverSupported, missing]

theorem recoverSupported_success_has_closed_entrypoint [DecidableEq Id] [DecidableEq Payload]
    (profile : Profile) (answer : Answer Id Payload) (rollbacks : Nat)
    {final : State Id Payload}
    (success : recoverSupported profile answer rollbacks = some final) :
    Module.nativeLlm ∈ profile.roots ∧ Closed profile := by
  unfold recoverSupported at success
  split at success
  · rename_i root
    refine ⟨root, ?_⟩
    unfold legacyRecoverSupported at success
    cases admitted : admit profile answer with
    | none => simp [admitted] at success
    | some state => exact admit_some_closed profile answer admitted
  · contradiction

/-- The supported profile composes admission, one provider submission, captured
receipt, finite local rollback, local commit, and exactly one settlement. -/
theorem petta_admission_recovery_composes [DecidableEq Id] [DecidableEq Payload]
    (answer : Answer Id Payload) (rollbacks : Nat) :
    ∃ final, recoverSupported pettaProfile answer rollbacks = some final ∧
      final.phase = .published ∧ final.providerRequests = 1 ∧ final.settlements = 1 ∧
        final.retained = some answer ∧ final.durable = some answer ∧
          final.identity = answer.identity := by
  refine ⟨run (afterReceive answer) (recoveryEvents answer rollbacks), ?_, ?_⟩
  · rw [recoverSupported, if_pos (by simp [pettaProfile])]
    unfold legacyRecoverSupported
    rw [petta_admission_succeeds]
    simp only [Option.map_some]
    apply congrArg some
    rw [run_append, submit_receive]
  · exact rollback_recovery_for_any_finite_wait answer rollbacks

namespace Controls

abbrev Identity := String

def answer : Answer Identity String := ⟨"call-7", "(nop)"⟩

/-- The concrete regression retains the same answer and request identity after
one rollback; a second publication does not create a second settlement. -/
theorem concrete_rollback_and_duplicate_delivery :
    ∃ final, recoverSupported pettaProfile answer 0 = some final ∧
      final.identity = answer.identity ∧ final.retained = some answer ∧
      final.providerRequests = 1 ∧ final.settlements = 1 ∧
      (step final .publish).settlements = 1 := by
  obtain ⟨final, recovered, phase, requests, settlements, retained, durable, identity⟩ :=
    petta_admission_recovery_composes answer 0
  refine ⟨final, recovered, identity, retained, requests, settlements, ?_⟩
  · have same := (repeated_settlement_is_ignored final phase).1
    rw [same]
    exact settlements

end Controls

#print axioms he_missing_reachable_capability
#print axioms he_not_closed
#print axioms petta_closed
#print axioms retries_cannot_make_another_provider_request
#print axioms rollback_recovery_for_any_finite_wait
#print axioms repeated_settlement_is_ignored
#print axioms he_admission_refused_before_effects
#print axioms admit_some_closed
#print axioms petta_admission_recovery_composes
#print axioms recoverSupported_missing_entrypoint
#print axioms recoverSupported_success_has_closed_entrypoint
#print axioms Controls.concrete_rollback_and_duplicate_delivery

end Mettapedia.Machines.ProfileRecoveryContract

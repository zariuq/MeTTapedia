import Mathlib.Data.List.Count
import Lean.Elab.Tactic.Omega

/-!
# Scoped owner and query cancellation

The source keeps one owner and the ordered non-null query obligations. The
implementation walks owner/query records, including the engine's root record.
Saved scopes restore the previous legacy token, observation bit and protected
chain. A temporary worker token changes only the legacy reading.

Tokens denote identities, not their current Boolean contents. Each poll uses
a supplied stable reading; later polls may read different contents. Stack
pointer validity, atomic loads, thread synchronization, lifetime and native
scope/worker integration are separate obligations. Scope exit restores token
identities and local observation state; it does not restore token contents.

Slice entry delegates all source-account changes to an existing debit service.
It introduces no purse representation or source price. Cancellation can be
observed before any physical allowance and leaves that supplied ledger intact.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.ScopedCancellation

universe u v
variable {Token : Type u}

def readOptional (read : Token → Bool) : Option Token → Bool
  | none => false
  | some token => read token

namespace Reference

structure Environment (Token : Type u) where
  legacy : Option Token
  observed : Bool
  owner : Option Token
  queries : List Token
  rooted : Bool
  deriving DecidableEq, Repr

def enterEngine [DecidableEq Token] (token : Option Token) (env : Environment Token) : Environment Token :=
  ⟨token, false, token,
    if env.rooted && env.owner == token then env.queries else [], true⟩

def enterQuery (token : Option Token) (env : Environment Token) : Environment Token :=
  ⟨token, false, if env.rooted then env.owner else env.legacy,
    token.toList ++ env.queries, true⟩

def replaceLegacy (token : Option Token) (env : Environment Token) : Environment Token :=
  {env with legacy := token, observed := false}

/-- Source cancellation is the disjunction of the current worker, the owning
engine and every active query obligation. -/
def requested (read : Token → Bool) (env : Environment Token) : Bool :=
  readOptional read env.legacy || readOptional read env.owner || env.queries.any read

end Reference

namespace Native

structure Pair (Token : Type u) where
  owner : Option Token
  query : Option Token
  deriving DecidableEq, Repr

structure Environment (Token : Type u) where
  legacy : Option Token
  observed : Bool
  chain : List (Pair Token)
  deriving DecidableEq, Repr

def ownerOf : List (Pair Token) → Option Token
  | [] => none
  | pair :: _ => pair.owner

def Uniform (env : Environment Token) : Prop :=
  ∀ pair ∈ env.chain, pair.owner = ownerOf env.chain

/-- A different engine starts a scope-owned root record. Same-owner reentry
keeps the entire query chain, even when the legacy token names a worker. -/
def enterEngine [DecidableEq Token] (token : Option Token) (env : Environment Token) : Environment Token :=
  {env with legacy := token, observed := false, chain :=
    match env.chain with
    | [] => [⟨token, none⟩]
    | pair :: _ => if pair.owner == token then env.chain else [⟨token, none⟩]}

def enterQuery (token : Option Token) (env : Environment Token) : Environment Token :=
  {env with legacy := token, observed := false, chain :=
    ⟨match env.chain with | [] => env.legacy | pair :: _ => pair.owner, token⟩ :: env.chain}

def replaceLegacy (token : Option Token) (env : Environment Token) : Environment Token :=
  {env with legacy := token, observed := false}

/-- This is the short-circuit loop over the native pair chain, rather than
the source's flat query-obligation interpretation. -/
def scan (read : Token → Bool) : List (Pair Token) → Bool
  | [] => false
  | pair :: rest =>
      if readOptional read pair.owner then true
      else if readOptional read pair.query then true
      else scan read rest

def requested (read : Token → Bool) (env : Environment Token) : Bool :=
  if readOptional read env.legacy then true else scan read env.chain

def decode (env : Environment Token) : Reference.Environment Token :=
  ⟨env.legacy, env.observed, ownerOf env.chain, env.chain.filterMap Pair.query, !env.chain.isEmpty⟩

end Native

theorem optional_read_eq_any (read : Token → Bool) (token : Option Token) :
    readOptional read token = token.toList.any read := by
  cases token <;> simp [readOptional]

theorem engine_entry_refines [DecidableEq Token] (token : Option Token) (env : Native.Environment Token) :
    Native.decode (Native.enterEngine token env) = Reference.enterEngine token (Native.decode env) := by
  rcases env with ⟨legacy, observed, chain⟩
  cases chain with
  | nil => simp [Native.decode, Native.enterEngine, Native.ownerOf, Reference.enterEngine]
  | cons pair rest =>
      by_cases same : pair.owner = token
      · simp [Native.decode, Native.enterEngine, Native.ownerOf, Reference.enterEngine, same]
      · simp [Native.decode, Native.enterEngine, Native.ownerOf, Reference.enterEngine, same]

theorem query_entry_refines (token : Option Token) (env : Native.Environment Token) :
    Native.decode (Native.enterQuery token env) = Reference.enterQuery token (Native.decode env) := by
  rcases env with ⟨legacy, observed, chain⟩
  cases chain <;> cases token <;>
    simp [Native.decode, Native.enterQuery, Native.ownerOf, Reference.enterQuery]

theorem worker_replacement_refines (token : Option Token) (env : Native.Environment Token) :
    Native.decode (Native.replaceLegacy token env) =
      Reference.replaceLegacy token (Native.decode env) := rfl

theorem engine_entry_uniform [DecidableEq Token] (token : Option Token) (env : Native.Environment Token)
    (uniform : Native.Uniform env) : Native.Uniform (Native.enterEngine token env) := by
  rcases env with ⟨legacy, observed, chain⟩
  cases chain with
  | nil => simp [Native.enterEngine, Native.Uniform, Native.ownerOf]
  | cons pair rest =>
      by_cases same : pair.owner = token
      · simpa [Native.enterEngine, same, Native.Uniform] using uniform
      · simp [Native.enterEngine, same, Native.Uniform, Native.ownerOf]

theorem query_entry_uniform (token : Option Token) (env : Native.Environment Token)
    (uniform : Native.Uniform env) : Native.Uniform (Native.enterQuery token env) := by
  rcases env with ⟨legacy, observed, chain⟩
  cases chain with
  | nil => simp [Native.enterQuery, Native.Uniform, Native.ownerOf]
  | cons pair rest =>
      intro node member
      change node ∈ _ :: pair :: rest at member
      rcases List.mem_cons.mp member with rfl | old
      · rfl
      · exact uniform node old

theorem worker_replacement_uniform (token : Option Token) (env : Native.Environment Token)
    (uniform : Native.Uniform env) : Native.Uniform (Native.replaceLegacy token env) := uniform

theorem scan_without_owner (read : Token → Bool) (owner : Option Token)
    (chain : List (Native.Pair Token))
    (uniform : ∀ pair ∈ chain, pair.owner = owner) (quiet : readOptional read owner = false) :
    Native.scan read chain = (chain.filterMap Native.Pair.query).any read := by
  induction chain with
  | nil => rfl
  | cons pair rest ih =>
      have head := uniform pair List.mem_cons_self
      have tail := ih (fun node member => uniform node (List.mem_cons_of_mem _ member))
      simp only [Native.scan, head, quiet, Bool.false_eq_true, ↓reduceIte]
      cases query : pair.query with
      | none => simp [query, readOptional, tail]
      | some token =>
          cases value : read token <;> simp [query, readOptional, tail, value]

theorem poll_refines (read : Token → Bool) (env : Native.Environment Token)
    (uniform : Native.Uniform env) :
    Reference.requested read (Native.decode env) = Native.requested read env := by
  rcases env with ⟨legacy, observed, chain⟩
  cases chain with
  | nil =>
      change (readOptional read legacy || false || false) =
        (if readOptional read legacy then true else false)
      cases readOptional read legacy <;> rfl
  | cons pair rest =>
      cases worker : readOptional read legacy with
      | true => simp [Reference.requested, Native.decode, Native.requested, worker]
      | false =>
          cases owner : readOptional read pair.owner with
          | true => simp [Reference.requested, Native.decode, Native.ownerOf, Native.requested,
              Native.scan, worker, owner]
          | false =>
              have quiet := scan_without_owner read pair.owner (pair :: rest) uniform owner
              simp [Reference.requested, Native.decode, Native.ownerOf, Native.requested, worker,
                owner, quiet]

structure Poll (Environment : Type u) where
  next : Environment
  cancelled : Bool
  firstObservation : Bool

def Reference.poll (read : Token → Bool) (env : Reference.Environment Token) :
    Poll (Reference.Environment Token) :=
  let cancelled := Reference.requested read env
  ⟨{env with observed := env.observed || cancelled}, cancelled, cancelled && !env.observed⟩

def Native.poll (read : Token → Bool) (env : Native.Environment Token) :
    Poll (Native.Environment Token) :=
  if Native.requested read env then
    ⟨{env with observed := true}, true, !env.observed⟩
  else ⟨env, false, false⟩

theorem poll_observation_refines (read : Token → Bool) (env : Native.Environment Token)
    (uniform : Native.Uniform env) :
    Reference.poll read (Native.decode env) =
      let result := Native.poll read env
      ⟨Native.decode result.next, result.cancelled, result.firstObservation⟩ := by
  unfold Reference.poll
  rw [poll_refines read env uniform]
  cases cancelled : Native.requested read env <;>
    cases observed : env.observed <;>
      simp [Native.poll, cancelled, Native.decode, observed]

theorem poll_preserves_uniform (read : Token → Bool) (env : Native.Environment Token)
    (uniform : Native.Uniform env) : Native.Uniform (Native.poll read env).next := by
  unfold Native.poll
  split <;> exact uniform

inductive Action (Token : Type u) where
  | enterEngine (token : Option Token)
  | enterQuery (token : Option Token)
  | replaceLegacy (token : Option Token)
  | leave
  | poll (read : Token → Bool)

inductive Event (Token : Type u) where
  | enteredEngine (token : Option Token)
  | enteredQuery (token : Option Token)
  | replacedLegacy (token : Option Token)
  | left
  | unmatchedLeave
  | polled (cancelled firstObservation : Bool)
  deriving DecidableEq, Repr

structure Transition (State : Type u) (Token : Type v) where
  next : State
  events : List (Event Token)

namespace Reference

structure State (Token : Type u) where
  current : Environment Token
  saved : List (Environment Token)
  deriving DecidableEq, Repr

def step [DecidableEq Token] (state : State Token) : Action Token → Transition (State Token) Token
  | .enterEngine token =>
      ⟨⟨enterEngine token state.current, state.current :: state.saved⟩, [.enteredEngine token]⟩
  | .enterQuery token =>
      ⟨⟨enterQuery token state.current, state.current :: state.saved⟩, [.enteredQuery token]⟩
  | .replaceLegacy token => ⟨{state with current := replaceLegacy token state.current}, [.replacedLegacy token]⟩
  | .leave => match state.saved with
      | [] => ⟨state, [.unmatchedLeave]⟩
      | parent :: rest => ⟨⟨parent, rest⟩, [.left]⟩
  | .poll read =>
      let observed := poll read state.current
      ⟨{state with current := observed.next}, [.polled observed.cancelled observed.firstObservation]⟩

end Reference

namespace Native

structure State (Token : Type u) where
  current : Environment Token
  saved : List (Environment Token)
  deriving DecidableEq, Repr

def State.Valid (state : State Token) : Prop :=
  Uniform state.current ∧ ∀ env ∈ state.saved, Uniform env

def step [DecidableEq Token] (state : State Token) : Action Token → Transition (State Token) Token
  | .enterEngine token =>
      let saved := state.current
      let current := enterEngine token state.current
      ⟨⟨current, saved :: state.saved⟩, [.enteredEngine token]⟩
  | .enterQuery token =>
      let saved := state.current
      let current := enterQuery token state.current
      ⟨⟨current, saved :: state.saved⟩, [.enteredQuery token]⟩
  | .replaceLegacy token => ⟨{state with current := replaceLegacy token state.current}, [.replacedLegacy token]⟩
  | .leave =>
      match state.saved with
      | parent :: rest => ⟨⟨parent, rest⟩, [.left]⟩
      | [] => ⟨state, [.unmatchedLeave]⟩
  | .poll read =>
      let observed := poll read state.current
      ⟨{state with current := observed.next}, [.polled observed.cancelled observed.firstObservation]⟩

def decodeState (state : State Token) : Reference.State Token :=
  ⟨decode state.current, state.saved.map decode⟩

end Native

theorem step_refines [DecidableEq Token] (state : Native.State Token)
    (valid : state.Valid) (action : Action Token) :
    Reference.step (Native.decodeState state) action =
      let result := Native.step state action
      ⟨Native.decodeState result.next, result.events⟩ := by
  cases action with
  | enterEngine token => simp [Reference.step, Native.step, Native.decodeState, engine_entry_refines]
  | enterQuery token => simp [Reference.step, Native.step, Native.decodeState, query_entry_refines]
  | replaceLegacy token => simp [Reference.step, Native.step, Native.decodeState, worker_replacement_refines]
  | leave =>
      rcases state with ⟨current, saved⟩
      cases saved <;> rfl
  | poll read =>
      simp [Reference.step, Native.step, Native.decodeState,
        poll_observation_refines read state.current valid.1]

theorem step_preserves_validity [DecidableEq Token] (state : Native.State Token)
    (valid : state.Valid) (action : Action Token) : (Native.step state action).next.Valid := by
  rcases state with ⟨current, saved⟩
  obtain ⟨currentValid, savedValid⟩ := valid
  cases action with
  | enterEngine token =>
      refine ⟨engine_entry_uniform token current currentValid, ?_⟩
      intro env member
      rcases List.mem_cons.mp member with rfl | old
      · exact currentValid
      · exact savedValid env old
  | enterQuery token =>
      refine ⟨query_entry_uniform token current currentValid, ?_⟩
      intro env member
      rcases List.mem_cons.mp member with rfl | old
      · exact currentValid
      · exact savedValid env old
  | replaceLegacy token => exact ⟨worker_replacement_uniform token current currentValid, savedValid⟩
  | leave =>
      cases saved with
      | nil => exact ⟨currentValid, savedValid⟩
      | cons parent rest =>
          exact ⟨savedValid parent List.mem_cons_self,
            fun env member => savedValid env (List.mem_cons_of_mem _ member)⟩
  | poll read => exact ⟨poll_preserves_uniform read current currentValid, savedValid⟩

def run {State : Type u} (step : State → Action Token → Transition State Token) :
    State → List (Action Token) → Transition State Token
  | state, [] => ⟨state, []⟩
  | state, action :: rest =>
      let first := step state action
      let later := run step first.next rest
      ⟨later.next, first.events ++ later.events⟩

/-- Arbitrary finite nesting, engine switching, worker substitution and
polling preserve complete saved contexts and exact observation chronology. -/
theorem trace_refines [DecidableEq Token] (state : Native.State Token)
    (valid : state.Valid) (actions : List (Action Token)) :
    run Reference.step (Native.decodeState state) actions =
      let result := run Native.step state actions
      ⟨Native.decodeState result.next, result.events⟩ := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      simp only [run, step_refines state valid action,
        ih (Native.step state action).next (step_preserves_validity state valid action)]

theorem same_owner_keeps_complete_chain [DecidableEq Token]
    (token : Option Token) (env : Native.Environment Token)
    (rooted : env.chain ≠ []) (same : Native.ownerOf env.chain = token) :
    (Native.enterEngine token env).chain = env.chain := by
  rcases env with ⟨legacy, observed, chain⟩
  cases chain with
  | nil => exact False.elim (rooted rfl)
  | cons pair rest =>
      change pair.owner = token at same
      simp [Native.enterEngine, same]

theorem other_owner_starts_independent_root [DecidableEq Token]
    (token : Option Token) (env : Native.Environment Token)
    (different : Native.ownerOf env.chain ≠ token) :
    (Native.enterEngine token env).chain = [⟨token, none⟩] := by
  rcases env with ⟨legacy, observed, chain⟩
  cases chain with
  | nil => rfl
  | cons pair rest =>
      change pair.owner ≠ token at different
      simp [Native.enterEngine, different]

theorem engine_request_survives_worker_substitution [DecidableEq Token]
    (read : Token → Bool) (env : Native.Environment Token) (uniform : Native.Uniform env)
    (engine worker : Option Token) (requested : readOptional read engine = true) :
    Native.requested read (Native.replaceLegacy worker (Native.enterEngine engine env)) = true := by
  rw [← poll_refines read _
    (worker_replacement_uniform worker _ (engine_entry_uniform engine env uniform)),
    worker_replacement_refines, engine_entry_refines]
  simp [Reference.requested, Reference.replaceLegacy, Reference.enterEngine, requested]

theorem ancestor_query_survives_nested_query (read : Token → Bool)
    (env : Native.Environment Token) (uniform : Native.Uniform env)
    (ancestor : Token) (member : ancestor ∈ env.chain.filterMap Native.Pair.query)
    (requested : read ancestor = true) (inner worker : Option Token) :
    Native.requested read (Native.replaceLegacy worker (Native.enterQuery inner env)) = true := by
  have queryTrue : (env.chain.filterMap Native.Pair.query).any read = true :=
    List.any_eq_true.mpr ⟨ancestor, member, requested⟩
  rw [← poll_refines read _
    (worker_replacement_uniform worker _ (query_entry_uniform inner env uniform)),
    worker_replacement_refines, query_entry_refines]
  simp [Reference.requested, Reference.replaceLegacy, Reference.enterQuery, Native.decode, queryTrue]

theorem ancestor_query_survives_same_engine [DecidableEq Token]
    (read : Token → Bool) (env : Native.Environment Token) (uniform : Native.Uniform env)
    (engine worker : Option Token) (rooted : env.chain ≠ [])
    (same : Native.ownerOf env.chain = engine) (ancestor : Token)
    (member : ancestor ∈ env.chain.filterMap Native.Pair.query) (requested : read ancestor = true) :
    Native.requested read (Native.replaceLegacy worker (Native.enterEngine engine env)) = true := by
  have kept := same_owner_keeps_complete_chain engine env rooted same
  have queryTrue : (env.chain.filterMap Native.Pair.query).any read = true :=
    List.any_eq_true.mpr ⟨ancestor, member, requested⟩
  rw [← poll_refines read _
    (worker_replacement_uniform worker _ (engine_entry_uniform engine env uniform))]
  simp [Reference.requested, Native.decode, Native.replaceLegacy, kept, queryTrue]

theorem leave_restores_complete_saved_context [DecidableEq Token]
    (current parent : Native.Environment Token) (rest : List (Native.Environment Token)) :
    Native.step ⟨current, parent :: rest⟩ .leave = ⟨⟨parent, rest⟩, [.left]⟩ := rfl

/-! The account type and its operation belong to the source evaluator. This
adapter only chooses whether that existing operation is entered. The poll
precedes physical allowance inspection and contributes no source debit. -/
inductive SliceStatus where
  | cancelled
  | paused
  | advanced
  | refused
  deriving DecidableEq, Repr

structure SliceResult (Environment : Type u) (Ledger : Type v) where
  environment : Environment
  ledger : Ledger
  status : SliceStatus
  firstObservation : Bool

def Reference.sliceEntry {Ledger : Type v}
    (read : Token → Bool) (allowance : Nat) (env : Reference.Environment Token)
    (ledger : Ledger) (sourceDebit : Ledger → Option Ledger) :
    SliceResult (Reference.Environment Token) Ledger :=
  let observed := Reference.poll read env
  if observed.cancelled then ⟨observed.next, ledger, .cancelled, observed.firstObservation⟩
  else match allowance with
    | 0 => ⟨observed.next, ledger, .paused, observed.firstObservation⟩
    | _ + 1 => match sourceDebit ledger with
      | none => ⟨observed.next, ledger, .refused, observed.firstObservation⟩
      | some paid => ⟨observed.next, paid, .advanced, observed.firstObservation⟩

def Native.sliceEntry {Ledger : Type v}
    (read : Token → Bool) (allowance : Nat) (env : Native.Environment Token)
    (ledger : Ledger) (sourceDebit : Ledger → Option Ledger) :
    SliceResult (Native.Environment Token) Ledger :=
  let observed := Native.poll read env
  if observed.cancelled then ⟨observed.next, ledger, .cancelled, observed.firstObservation⟩
  else if allowance == 0 then ⟨observed.next, ledger, .paused, observed.firstObservation⟩
  else match sourceDebit ledger with
    | some paid => ⟨observed.next, paid, .advanced, observed.firstObservation⟩
    | none => ⟨observed.next, ledger, .refused, observed.firstObservation⟩

theorem slice_entry_refines {Ledger : Type v} (read : Token → Bool) (allowance : Nat)
    (env : Native.Environment Token) (uniform : Native.Uniform env)
    (ledger : Ledger) (sourceDebit : Ledger → Option Ledger) :
    Reference.sliceEntry read allowance (Native.decode env) ledger sourceDebit =
      let result := Native.sliceEntry read allowance env ledger sourceDebit
      ⟨Native.decode result.environment, result.ledger, result.status, result.firstObservation⟩ := by
  unfold Reference.sliceEntry
  rw [poll_observation_refines read env uniform]
  unfold Native.sliceEntry
  cases cancelled : (Native.poll read env).cancelled <;> cases allowance <;>
    simp [cancelled]
  cases sourceDebit ledger <;> rfl

theorem cancellation_does_not_debit {Ledger : Type v} (read : Token → Bool) (allowance : Nat)
    (env : Native.Environment Token) (requested : Native.requested read env = true)
    (ledger : Ledger) (sourceDebit : Ledger → Option Ledger) :
    Native.sliceEntry read allowance env ledger sourceDebit =
      ⟨{env with observed := true}, ledger, .cancelled, !env.observed⟩ := by
  simp [Native.sliceEntry, Native.poll, requested]

theorem zero_allowance_preserves_existing_ledger {Ledger : Type v}
    (read : Token → Bool) (env : Native.Environment Token)
    (ledger : Ledger) (sourceDebit : Ledger → Option Ledger) :
    (Native.sliceEntry read 0 env ledger sourceDebit).ledger = ledger := by
  cases cancelled : (Native.poll read env).cancelled <;>
    simp [Native.sliceEntry, cancelled]

theorem zero_allowance_still_observes_cancel {Ledger : Type v}
    (read : Token → Bool) (env : Native.Environment Token)
    (requested : Native.requested read env = true) (ledger : Ledger)
    (sourceDebit : Ledger → Option Ledger) :
    (Native.sliceEntry read 0 env ledger sourceDebit).status = .cancelled ∧
      (Native.sliceEntry read 0 env ledger sourceDebit).ledger = ledger := by
  rw [cancellation_does_not_debit read 0 env requested ledger sourceDebit]
  exact ⟨rfl, rfl⟩

namespace Controls

def empty : Native.State Nat := ⟨⟨none, false, []⟩, []⟩
def only (wanted : Nat) (token : Nat) : Bool := token == wanted
def quiet (_ : Nat) : Bool := false

def nested : Native.Environment Nat :=
  Native.enterQuery (some 11) (Native.enterQuery (some 10)
    (Native.enterEngine (some 1) empty.current))

theorem initial_state_valid : empty.Valid := by
  simp [empty, Native.State.Valid, Native.Uniform]

theorem bare_engine_owner_survives_worker_token :
    let entered := Native.enterEngine (some 1) empty.current
    Native.requested (only 1) (Native.replaceLegacy (some 90) entered) = true := by decide

theorem ancestor_query_survives_calls_and_queries :
    Native.requested (only 10) (Native.replaceLegacy (some 90) nested) = true ∧
      Native.requested (only 10)
        (Native.replaceLegacy (some 90) (Native.enterEngine (some 1) nested)) = true := by decide

theorem independent_engine_and_its_query_ignore_old_cancellation :
    let independent := Native.enterEngine (some 2) nested
    Native.requested (only 10) independent = false ∧
      Native.requested (only 10) (Native.enterQuery (some 12) independent) = false := by decide

theorem leaving_independent_engine_resumes_outer_query :
    let result := run Native.step empty [.enterEngine (some 1), .enterQuery (some 10),
      .enterEngine (some 2), .poll (only 10), .leave, .poll (only 10)]
    result.events = [.enteredEngine (some 1), .enteredQuery (some 10), .enteredEngine (some 2),
      .polled false false, .left, .polled true true] := by decide

theorem leave_restores_prior_observation_bit :
    let result := run Native.step empty [.enterEngine (some 1), .poll (only 1),
      .enterQuery (some 10), .poll (only 1), .leave, .poll (only 1)]
    result.events = [.enteredEngine (some 1), .polled true true, .enteredQuery (some 10),
      .polled true true, .left, .polled true false] := by decide

theorem restoration_does_not_rollback_token_contents :
    let result := run Native.step empty [.enterEngine (some 1), .poll quiet,
      .enterEngine (some 2), .poll quiet, .leave, .poll (only 1)]
    result.events = [.enteredEngine (some 1), .polled false false, .enteredEngine (some 2),
      .polled false false, .left, .polled true true] := by decide

theorem nullable_query_and_legacy_preserve_owner :
    let owner := Native.enterEngine (some 1) empty.current
    Native.requested (only 1) (Native.replaceLegacy none (Native.enterQuery none owner)) = true ∧
      Native.requested (only 10) (Native.enterQuery (some 10) empty.current) = true := by decide

theorem worker_request_is_still_observed :
    Native.requested (only 90) (Native.replaceLegacy (some 90) nested) = true := by decide

/-- The former rootless engine algorithm loses this real owner request. -/
theorem missing_engine_root_hides_owner_under_worker :
    let correct := Native.replaceLegacy (some 90) (Native.enterEngine (some 1) empty.current)
    Native.requested (only 1) correct = true ∧
      Native.requested (only 1) {correct with chain := []} = false := by decide

theorem dropped_parent_loses_ancestor_query :
    Native.requested (only 10) nested = true ∧
      Native.requested (only 10) {nested with chain := [⟨some 1, some 11⟩]} = false := by decide

theorem keeping_old_chain_contaminates_an_independent_engine :
    Native.requested (only 10) (Native.enterEngine (some 2) nested) = false ∧
      Native.requested (only 10) {nested with legacy := some 2, observed := false} = true := by decide

theorem legacy_only_poll_misses_protected_query :
    let worker := Native.replaceLegacy (some 90) nested
    Native.requested (only 10) worker = true ∧ readOptional (only 10) worker.legacy = false := by decide

theorem dropping_restored_chain_loses_pending_query :
    let old := Native.replaceLegacy (some 90) nested
    let entered := (Native.step (⟨old, []⟩ : Native.State Nat) (.enterEngine (some 2))).next
    let restored := (Native.step entered .leave).next.current
    Native.requested (only 10) restored = true ∧
      Native.requested (only 10) {restored with chain := []} = false := by decide

theorem dropping_restored_legacy_loses_worker_request :
    let old := Native.replaceLegacy (some 90) nested
    let entered := (Native.step (⟨old, []⟩ : Native.State Nat) (.enterEngine (some 2))).next
    let restored := (Native.step entered .leave).next.current
    Native.requested (only 90) restored = true ∧
      Native.requested (only 90) {restored with legacy := some 2} = false := by decide

theorem dropping_restored_observation_recounts_the_request :
    let old := (Native.poll (only 10) nested).next
    let entered := (Native.step (⟨old, []⟩ : Native.State Nat) (.enterEngine (some 2))).next
    let restored := (Native.step entered .leave).next.current
    (Native.poll (only 10) restored).firstObservation = false ∧
      (Native.poll (only 10) {restored with observed := false}).firstObservation = true := by decide

theorem zero_allowance_observes_cancel_without_source_debit :
    let env := Native.enterEngine (some 1) empty.current
    let result := Native.sliceEntry (only 1) 0 env [3] (fun ledger => some (ledger ++ [5]))
    result.status = .cancelled ∧ result.firstObservation = true ∧ result.ledger = [3] := by decide

theorem physical_pause_does_not_debit_but_admitted_work_uses_the_service :
    let env := Native.enterEngine (some 1) empty.current
    let paused := Native.sliceEntry quiet 0 env [3] (fun ledger => some (ledger ++ [5]))
    let advanced := Native.sliceEntry quiet 1 env [3] (fun ledger => some (ledger ++ [5]))
    paused.status = .paused ∧ paused.ledger = [3] ∧
      advanced.status = .advanced ∧ advanced.ledger = [3, 5] := by decide

/-- Checking the slice limit before cancellation gives the wrong status,
even though both paths leave the source account unchanged. -/
theorem checking_allowance_before_cancel_hides_interruption :
    let env := Native.enterEngine (some 1) empty.current
    let actual := Native.sliceEntry (only 1) 0 env [3] (fun ledger => some (ledger ++ [5]))
    let faulty : SliceResult (Native.Environment Nat) (List Nat) := ⟨env, [3], .paused, false⟩
    actual.status ≠ faulty.status ∧ actual.ledger = faulty.ledger := by decide

end Controls

end Mettapedia.Machines.ScopedCancellation

import Mettapedia.Machines.IncrementalConformance.ForeignState

/-!
# Retained foreign query lifecycle

The finite service of `ForeignState` is extended by ordered alternatives,
nonbacktrackable effects, exceptions and explicit suspension. The replay runner
reconstructs a domain from the accepted event history; the retained runner
filters its existing domain. Their query continuations and replies agree,
including duplicate answer occurrences and the effect sequence.

A query checkpoint restores only solver state. Effects already performed survive
rejection, exceptions, cancellation and discarding an answer. Cutting a selected
answer instead keeps its solver state and removes its remaining alternatives.
Suspension stores the unevaluated suffix: resumption never repeats the prefix.
These are service-boundary laws, not a language-wide effect or scheduling policy.

The client chooses demanded variable tuples. Projected observations are proved
from the independent replay/retained relation; requesting an empty tuple does not
imply that the full constraint state is empty or dispensable.

This model contains pure finite-domain goals and inert attributes. It does not
model arbitrary SWI attribute hooks, nested FFI frames, cleanup callbacks,
thread affinity, physical term references, solver propagation costs or C code.
The native adapter must realize these lifecycle operations and qualify every
additional effect and handle lifetime separately.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.ForeignQueryLifecycle

open ForeignState

universe u v w a e x t

inductive Instruction (Var : Type u) (Val : Type v) (Attr : Type w)
    (Effect : Type e) (Fault : Type x) (Token : Type t) where
  | post (event : Event Var Val Attr)
  | effect (event : Effect)
  | raise (fault : Fault)
  | await (token : Token)
  deriving DecidableEq

structure Alternative (Var : Type u) (Val : Type v) (Attr : Type w)
    (Answer : Type a) (Effect : Type e) (Fault : Type x) (Token : Type t) where
  code : List (Instruction Var Val Attr Effect Fault Token)
  answer : Answer
  deriving DecidableEq

inductive Signal (Var : Type u) (Val : Type v) (Attr : Type w)
    (Answer : Type a) (Effect : Type e) (Fault : Type x) (Token : Type t) where
  | answer (value : Answer)
  | rejected
  | raised (fault : Fault)
  | suspended (token : Token)
      (continuation : Alternative Var Val Attr Answer Effect Fault Token)
  deriving DecidableEq

structure Evaluation (State : Type*) (Var : Type u) (Val : Type v) (Attr : Type w)
    (Answer : Type a) (Effect : Type e) (Fault : Type x) (Token : Type t) where
  signal : Signal Var Val Attr Answer Effect Fault Token
  store : State
  effects : List Effect

variable {Var : Type u} {Val : Type v} {Attr : Type w}
    {Answer : Type a} {Effect : Type e} {Fault : Type x} {Token : Type t}

/-- A foreign primitive is evaluated exactly once before its reply is inspected.
The effect list records actions already performed, not actions to replay. -/
def execute {State : Type*}
    (call : Event Var Val Attr → State → Bool × State)
    (answer : Answer) : List (Instruction Var Val Attr Effect Fault Token) →
      State → List Effect → Evaluation State Var Val Attr Answer Effect Fault Token
  | [], state, effects => ⟨.answer answer, state, effects⟩
  | .post event :: rest, state, effects =>
      let result := call event state
      if result.1 then execute call answer rest result.2 effects
      else ⟨.rejected, result.2, effects⟩
  | .effect event :: rest, state, effects =>
      execute call answer rest state (effects ++ [event])
  | .raise fault :: _, state, effects => ⟨.raised fault, state, effects⟩
  | .await token :: rest, state, effects =>
      ⟨.suspended token ⟨rest, answer⟩, state, effects⟩

/-- A committed prefix of effect instructions precedes the retained suffix.
The interpreter does not copy those instructions into the continuation. -/
theorem execute_effect_prefix {State : Type*}
    (call : Event Var Val Attr → State → Bool × State)
    (answer : Answer) (committed : List Effect)
    (suffix : List (Instruction Var Val Attr Effect Fault Token))
    (state : State) (effects : List Effect) :
    execute call answer (committed.map Instruction.effect ++ suffix) state effects =
      execute call answer suffix state (effects ++ committed) := by
  induction committed generalizing effects with
  | nil => simp
  | cons event rest ih =>
      simpa [execute, List.append_assoc] using ih (effects ++ [event])

/-- Suspension retains the exact suffix and the already published effect log,
even when the prefix contains repeated equal effect occurrences. -/
theorem await_after_effect_prefix {State : Type*}
    (call : Event Var Val Attr → State → Bool × State)
    (answer : Answer) (committed : List Effect) (token : Token)
    (suffix : List (Instruction Var Val Attr Effect Fault Token))
    (state : State) (effects : List Effect) :
    execute call answer (committed.map Instruction.effect ++ .await token :: suffix)
        state effects =
      ⟨.suspended token ⟨suffix, answer⟩, state, effects ++ committed⟩ := by
  rw [execute_effect_prefix]
  rfl

variable [DecidableEq Var] [DecidableEq Val] [Fintype Var] [Fintype Val]

/-- The relation comes from the independently specified constraint runners;
it is not an assumed simulation of arbitrary foreign execution. -/
def EvaluationsRelated
    (reference : Evaluation (List (Event Var Val Attr)) Var Val Attr Answer Effect Fault Token)
    (retained : Evaluation (Retained Var Val Attr) Var Val Attr Answer Effect Fault Token) : Prop :=
  reference.signal = retained.signal ∧
  reference.effects = retained.effects ∧
  Related reference.store retained.store

/-- All finite instruction suffixes preserve the exact reply, continuation and
persistent effects as well as the independently reconstructed solver domain. -/
theorem execute_related (answer : Answer)
    (code : List (Instruction Var Val Attr Effect Fault Token))
    {history : List (Event Var Val Attr)} {state : Retained Var Val Attr}
    (related : Related history state) (effects : List Effect) :
    EvaluationsRelated (execute referenceCall answer code history effects)
      (execute retainedCall answer code state effects) := by
  induction code generalizing history state effects with
  | nil => exact ⟨rfl, rfl, related⟩
  | cons instruction rest ih =>
      cases instruction with
      | post event =>
          obtain ⟨same, next⟩ := call_related event related
          simp only [execute, same]
          split_ifs
          · exact ih next effects
          · exact ⟨rfl, rfl, next⟩
      | effect event => exact ih related (effects ++ [event])
      | raise fault => exact ⟨rfl, rfl, related⟩
      | await token => exact ⟨rfl, rfl, related⟩

/-- A checkpoint contains backtrackable state, never the persistent effect log. -/
structure Query (State : Type*) (Var : Type u) (Val : Type v) (Attr : Type w)
    (Answer : Type a) (Effect : Type e) (Fault : Type x) (Token : Type t) where
  base : State
  alternatives : List (Alternative Var Val Attr Answer Effect Fault Token)
  selected : Option State
  paused : Option (Token × Alternative Var Val Attr Answer Effect Fault Token × State)
  effects : List Effect

inductive Reply (Answer : Type a) (Fault : Type x) (Token : Type t) where
  | answer (value : Answer)
  | exhausted
  | raised (fault : Fault)
  | suspended (token : Token)
  | unexpectedResume
  deriving DecidableEq

/-- Start one query over an existing branch-owned solver snapshot. -/
def start {State : Type*} (base : State)
    (alternatives : List (Alternative Var Val Attr Answer Effect Fault Token))
    (effects : List Effect) : Query State Var Val Attr Answer Effect Fault Token :=
  ⟨base, alternatives, none, none, effects⟩

/-- Search from the base after each rejected alternative. Actions already taken
remain in the effect log. A raise terminates this query, not the surrounding
language; its handler decides the next operation. -/
def search {State : Type*}
    (call : Event Var Val Attr → State → Bool × State) (base : State) :
    List (Alternative Var Val Attr Answer Effect Fault Token) → List Effect →
      Reply Answer Fault Token × Query State Var Val Attr Answer Effect Fault Token
  | [], effects => (.exhausted, start base [] effects)
  | alternative :: rest, effects =>
      let result := execute call alternative.answer alternative.code base effects
      match result.signal with
      | .answer value =>
          (.answer value, ⟨base, rest, some result.store, none, result.effects⟩)
      | .rejected => search call base rest result.effects
      | .raised fault => (.raised fault, start base [] result.effects)
      | .suspended token continuation =>
          (.suspended token,
            ⟨base, rest, none, some (token, continuation, result.store), result.effects⟩)

/-- `next` does not execute through an unresolved suspension. It exposes the
same pending request until the correct token is supplied to `resume`. -/
def next {State : Type*}
    (call : Event Var Val Attr → State → Bool × State)
    (query : Query State Var Val Attr Answer Effect Fault Token) :
    Reply Answer Fault Token × Query State Var Val Attr Answer Effect Fault Token :=
  match query.paused with
  | none => search call query.base query.alternatives query.effects
  | some (token, _, _) => (.suspended token, query)

/-- Resume the retained suffix at its suspended solver state. On rejection,
continue with the next alternative at the original query checkpoint. -/
def resume [DecidableEq Token] {State : Type*}
    (call : Event Var Val Attr → State → Bool × State) (token : Token)
    (query : Query State Var Val Attr Answer Effect Fault Token) :
    Reply Answer Fault Token × Query State Var Val Attr Answer Effect Fault Token :=
  match query.paused with
  | none => (.unexpectedResume, query)
  | some (expected, continuation, state) =>
      if token = expected then
        let result := execute call continuation.answer continuation.code state query.effects
        match result.signal with
        | .answer value =>
            (.answer value,
              ⟨query.base, query.alternatives, some result.store, none, result.effects⟩)
        | .rejected => search call query.base query.alternatives result.effects
        | .raised fault => (.raised fault, start query.base [] result.effects)
        | .suspended later suffix =>
            (.suspended later,
              ⟨query.base, query.alternatives, none,
                some (later, suffix, result.store), result.effects⟩)
      else (.unexpectedResume, query)

omit [DecidableEq Var] [DecidableEq Val] [Fintype Var] [Fintype Val] in
/-- A pause after arbitrary committed effects, followed by a matching resume,
has exactly the reply and retained query of the uninterrupted program with the
pause removed. The suffix may itself reject, raise, answer or suspend again. -/
theorem resume_after_effect_prefix [DecidableEq Token] {State : Type*}
    (call : Event Var Val Attr → State → Bool × State)
    (answer : Answer) (committed : List Effect) (token : Token)
    (suffix : List (Instruction Var Val Attr Effect Fault Token))
    (state : State) (effects : List Effect) :
    resume call token
        (next call (start state
          [⟨committed.map Instruction.effect ++ .await token :: suffix, answer⟩]
          effects)).2 =
      next call (start state
        [⟨committed.map Instruction.effect ++ suffix, answer⟩] effects) := by
  simp only [next, start, search, await_after_effect_prefix]
  simp only [resume, ↓reduceIte]
  rw [execute_effect_prefix]
  cases (execute call answer suffix state (effects ++ committed)).signal <;> rfl

/-- Discarding/cancelling a query restores its solver checkpoint and releases
all alternative and suspended continuations. Persistent effects survive. -/
def discard {State : Type*} (query : Query State Var Val Attr Answer Effect Fault Token) :
    Query State Var Val Attr Answer Effect Fault Token :=
  start query.base [] query.effects

/-- Cut is admitted only after an answer was selected. A paused query must be
resumed or discarded, not silently treated as a successful answer. -/
def cut {State : Type*} (query : Query State Var Val Attr Answer Effect Fault Token) :
    Option (Query State Var Val Attr Answer Effect Fault Token) :=
  match query.selected, query.paused with
  | some state, none => some (start state [] query.effects)
  | _, _ => none

def QueriesRelated
    (reference : Query (List (Event Var Val Attr)) Var Val Attr Answer Effect Fault Token)
    (retained : Query (Retained Var Val Attr) Var Val Attr Answer Effect Fault Token) : Prop :=
  Related reference.base retained.base ∧
  reference.alternatives = retained.alternatives ∧
  Option.Rel Related reference.selected retained.selected ∧
  Option.Rel
    (fun r n => r.1 = n.1 ∧ r.2.1 = n.2.1 ∧ Related r.2.2 n.2.2)
    reference.paused retained.paused ∧
  reference.effects = retained.effects

/-- Query construction preserves the solver relation without replaying effects. -/
theorem start_related {history : List (Event Var Val Attr)}
    {state : Retained Var Val Attr} (related : Related history state)
    (alternatives : List (Alternative Var Val Attr Answer Effect Fault Token))
    (effects : List Effect) :
    QueriesRelated (start history alternatives effects) (start state alternatives effects) :=
  ⟨related, rfl, .none, .none, rfl⟩

/-- Ordered search returns corresponding answers, terminal errors or suspended
continuations. Equal answer values are distinct occurrences when branches repeat. -/
theorem search_related {history : List (Event Var Val Attr)}
    {state : Retained Var Val Attr} (related : Related history state)
    (alternatives : List (Alternative Var Val Attr Answer Effect Fault Token))
    (effects : List Effect) :
    (search referenceCall history alternatives effects).1 =
      (search retainedCall state alternatives effects).1 ∧
    QueriesRelated (search referenceCall history alternatives effects).2
      (search retainedCall state alternatives effects).2 := by
  induction alternatives generalizing effects with
  | nil => exact ⟨rfl, start_related related [] effects⟩
  | cons alternative rest ih =>
      obtain ⟨same, sameEffects, store⟩ :=
        execute_related alternative.answer alternative.code related effects
      simp only [search]
      cases signal : (execute referenceCall alternative.answer alternative.code history effects).signal with
      | answer value =>
          rw [← same, signal]
          exact ⟨rfl, related, rfl, .some store, .none, sameEffects⟩
      | rejected =>
          rw [← same, signal]
          rw [sameEffects]
          exact ih _
      | raised fault =>
          rw [← same, signal]
          rw [sameEffects]
          exact ⟨rfl, start_related related [] _⟩
      | suspended token continuation =>
          rw [← same, signal]
          exact ⟨rfl, related, rfl, .none, .some ⟨rfl, rfl, store⟩, sameEffects⟩

/-- Advancing a selected answer restores the query base before exploring the
next branch; awaiting a response does not repeat work already performed. -/
theorem next_related
    {reference : Query (List (Event Var Val Attr)) Var Val Attr Answer Effect Fault Token}
    {retained : Query (Retained Var Val Attr) Var Val Attr Answer Effect Fault Token}
    (related : QueriesRelated reference retained) :
    (next referenceCall reference).1 = (next retainedCall retained).1 ∧
      QueriesRelated (next referenceCall reference).2 (next retainedCall retained).2 := by
  obtain ⟨base, alternatives, selected, paused, effects⟩ := related
  generalize hr : reference.paused = r at paused
  generalize hn : retained.paused = n at paused
  cases paused with
  | none =>
      simp only [next, hr, hn]
      rw [alternatives, effects]
      exact search_related base _ _
  | @some r n same =>
      simp only [next, hr, hn]
      exact ⟨congrArg Reply.suspended same.1,
        base, alternatives, selected, by rw [hr, hn]; exact .some same, effects⟩

omit [DecidableEq Var] [DecidableEq Val] [Fintype Var] [Fintype Val] in
/-- A wrong or stale suspension token never dispatches foreign code. -/
theorem resume_wrong_token [DecidableEq Token] {State : Type*}
    (call : Event Var Val Attr → State → Bool × State)
    (query : Query State Var Val Attr Answer Effect Fault Token)
    (expected supplied : Token)
    (continuation : Alternative Var Val Attr Answer Effect Fault Token) (state : State)
    (paused : query.paused = some (expected, continuation, state))
    (different : supplied ≠ expected) :
    resume call supplied query = (.unexpectedResume, query) := by
  simp [resume, paused, different]

theorem resume_related [DecidableEq Token] (token : Token)
    {reference : Query (List (Event Var Val Attr)) Var Val Attr Answer Effect Fault Token}
    {retained : Query (Retained Var Val Attr) Var Val Attr Answer Effect Fault Token}
    (related : QueriesRelated reference retained) :
    (resume referenceCall token reference).1 = (resume retainedCall token retained).1 ∧
      QueriesRelated (resume referenceCall token reference).2
        (resume retainedCall token retained).2 := by
  obtain ⟨base, alternatives, selected, paused, effects⟩ := related
  generalize hr : reference.paused = r at paused
  generalize hn : retained.paused = n at paused
  cases paused with
  | none =>
      simp only [resume, hr, hn]
      exact ⟨trivial, base, alternatives, selected, by rw [hr, hn]; exact .none, effects⟩
  | @some r n same =>
      rcases r with ⟨expected, continuation, state⟩
      rcases n with ⟨expected', continuation', state'⟩
      simp only at same
      rcases same with ⟨rfl, rfl, store⟩
      simp only [resume, hr, hn]
      by_cases sameToken : token = expected
      · simp only [if_pos sameToken]
        rw [effects]
        obtain ⟨sameSignal, sameEffects, nextLocal⟩ :=
          execute_related continuation.answer continuation.code store retained.effects
        cases signal : (execute referenceCall continuation.answer continuation.code state
          retained.effects).signal with
        | answer value =>
            rw [← sameSignal, signal]
            exact ⟨rfl, base, alternatives, .some nextLocal, .none, sameEffects⟩
        | rejected =>
            rw [← sameSignal, signal, alternatives, sameEffects]
            exact search_related base _ _
        | raised fault =>
            rw [← sameSignal, signal, sameEffects]
            exact ⟨rfl, start_related base [] _⟩
        | suspended later suffix =>
            rw [← sameSignal, signal]
            exact ⟨rfl, base, alternatives, .none,
              .some ⟨rfl, rfl, nextLocal⟩, sameEffects⟩
      · simp only [if_neg sameToken]
        exact ⟨trivial, base, alternatives, selected,
          by rw [hr, hn]; exact .some ⟨rfl, rfl, store⟩, effects⟩

theorem discard_related
    {reference : Query (List (Event Var Val Attr)) Var Val Attr Answer Effect Fault Token}
    {retained : Query (Retained Var Val Attr) Var Val Attr Answer Effect Fault Token}
    (related : QueriesRelated reference retained) :
    QueriesRelated (discard reference) (discard retained) := by
  unfold discard
  rw [related.2.2.2.2]
  exact start_related related.1 [] _

theorem cut_related
    {reference : Query (List (Event Var Val Attr)) Var Val Attr Answer Effect Fault Token}
    {retained : Query (Retained Var Val Attr) Var Val Attr Answer Effect Fault Token}
    (related : QueriesRelated reference retained) :
    Option.Rel QueriesRelated (cut reference) (cut retained) := by
  obtain ⟨base, alternatives, selected, paused, effects⟩ := related
  generalize hr : reference.selected = r at selected
  generalize hn : retained.selected = n at selected
  cases selected with
  | none => simp [cut, hr, hn]
  | @some r n store =>
      generalize hpr : reference.paused = pr at paused
      generalize hpn : retained.paused = pn at paused
      cases paused with
      | none =>
          simp only [cut, hr, hn, hpr, hpn]
          apply Option.Rel.some
          rw [effects]
          exact start_related store [] _
      | some same => simp [cut, hr, hn, hpr, hpn]

inductive Command (Token : Type t) where
  | next
  | resume (token : Token)
  | discard
  | cut
  deriving DecidableEq

inductive Observation (Answer : Type a) (Fault : Type x) (Token : Type t) where
  | service (reply : Reply Answer Fault Token)
  | discarded
  | committed
  | deniedCut
  deriving DecidableEq

/-- A finite host-control trace decides each query operation locally. Neither
cut nor discard silently enumerates pending alternatives. -/
def step [DecidableEq Token] {State : Type*}
    (call : Event Var Val Attr → State → Bool × State) (command : Command Token)
    (query : Query State Var Val Attr Answer Effect Fault Token) :
    Observation Answer Fault Token × Query State Var Val Attr Answer Effect Fault Token :=
  match command with
  | .next =>
      let result := next call query
      (.service result.1, result.2)
  | .resume token =>
      let result := resume call token query
      (.service result.1, result.2)
  | .discard => (.discarded, discard query)
  | .cut =>
      match cut query with
      | none => (.deniedCut, query)
      | some committed => (.committed, committed)

theorem step_related [DecidableEq Token] (command : Command Token)
    {reference : Query (List (Event Var Val Attr)) Var Val Attr Answer Effect Fault Token}
    {retained : Query (Retained Var Val Attr) Var Val Attr Answer Effect Fault Token}
    (related : QueriesRelated reference retained) :
    (step referenceCall command reference).1 = (step retainedCall command retained).1 ∧
      QueriesRelated (step referenceCall command reference).2
        (step retainedCall command retained).2 := by
  cases command with
  | next =>
      obtain ⟨same, following⟩ := next_related related
      exact ⟨congrArg Observation.service same, following⟩
  | resume token =>
      obtain ⟨same, following⟩ := resume_related token related
      exact ⟨congrArg Observation.service same, following⟩
  | discard => exact ⟨rfl, discard_related related⟩
  | cut =>
      have same := cut_related related
      generalize hr : cut reference = r at same
      generalize hn : cut retained = n at same
      cases same with
      | none =>
          simp only [step, hr, hn]
          exact ⟨trivial, related⟩
      | some following =>
          simp only [step, hr, hn]
          exact ⟨trivial, following⟩

def run [DecidableEq Token] {State : Type*}
    (call : Event Var Val Attr → State → Bool × State) :
    List (Command Token) → Query State Var Val Attr Answer Effect Fault Token →
      List (Observation Answer Fault Token) × Query State Var Val Attr Answer Effect Fault Token
  | [], query => ([], query)
  | command :: rest, query =>
      let result := step call command query
      let later := run call rest result.2
      (result.1 :: later.1, later.2)

/-- Every finite command trace preserves ordered replies, exceptions,
suspension continuations, selected/base solver state and persistent effects. -/
theorem run_related [DecidableEq Token] (commands : List (Command Token))
    {reference : Query (List (Event Var Val Attr)) Var Val Attr Answer Effect Fault Token}
    {retained : Query (Retained Var Val Attr) Var Val Attr Answer Effect Fault Token}
    (related : QueriesRelated reference retained) :
    (run referenceCall commands reference).1 = (run retainedCall commands retained).1 ∧
      QueriesRelated (run referenceCall commands reference).2
        (run retainedCall commands retained).2 := by
  induction commands generalizing reference retained with
  | nil => exact ⟨rfl, related⟩
  | cons command rest ih =>
      obtain ⟨same, following⟩ := step_related command related
      obtain ⟨sameRest, final⟩ := ih following
      exact ⟨congrArg₂ List.cons same sameRest, final⟩

omit [DecidableEq Var] [DecidableEq Val] [Fintype Var] [Fintype Val] in
/-- Persistent effects are not part of solver rollback. -/
theorem discard_effects {State : Type*}
    (query : Query State Var Val Attr Answer Effect Fault Token) :
    (discard query).effects = query.effects := rfl

omit [DecidableEq Var] [DecidableEq Val] [Fintype Var] [Fintype Val] in
theorem discard_releases_continuations {State : Type*}
    (query : Query State Var Val Attr Answer Effect Fault Token) :
    (discard query).alternatives = [] ∧ (discard query).paused = none ∧
      (discard query).selected = none := ⟨rfl, rfl, rfl⟩

omit [DecidableEq Var] [DecidableEq Val] [Fintype Var] [Fintype Val] in
/-- Releasing choicepoints and retaining the selected branch are different
operations; their difference is observed by subsequent solver calls. -/
theorem cut_selected {State : Type*}
    (query : Query State Var Val Attr Answer Effect Fault Token) (state : State)
    (selected : query.selected = some state) (notPaused : query.paused = none) :
    cut query = some (start state [] query.effects) := by simp [cut, selected, notPaused]

/-- Demanded observations retain only the requested tuple; the solver state
itself remains available for later constraints and broader observations. -/
def demandObservation (demand : List Var) (state : Retained Var Val Attr) :
    Finset (List Val) := state.solutions.image fun valuation => demand.map valuation

def referenceDemand (demand : List Var) (history : List (Event Var Val Attr)) :
    Finset (List Val) := (referenceSolutions history).image fun valuation => demand.map valuation

theorem demand_related (demand : List Var) {history : List (Event Var Val Attr)}
    {state : Retained Var Val Attr} (related : Related history state) :
    demandObservation demand state = referenceDemand demand history := by
  rw [demandObservation, referenceDemand, related.1]

omit [DecidableEq Var] [Fintype Var] [Fintype Val] in
/-- The result size is bounded by the represented solution count; exporting a
projection need not export its generating constraints or complete valuations. -/
theorem demand_card_le (demand : List Var) (state : Retained Var Val Attr) :
    (demandObservation demand state).card ≤ state.solutions.card := Finset.card_image_le

namespace Controls

abbrev I := Instruction Bool Bool Nat Nat Nat Nat
abbrev A := Alternative Bool Bool Nat Nat Nat Nat Nat
abbrev S := Retained Bool Bool Nat
abbrev Q := Query S Bool Bool Nat Nat Nat Nat Nat

/-- Duplicate branches yield duplicate answers; the first branch's effects do
not vanish merely because its constraint is contradictory. -/
def orderedAlternatives : List A :=
  [⟨[.effect 10, .post (.post (.bind false true)),
      .post (.post (.bind false false))], 7⟩,
   ⟨[.effect 20, .post (.post (.bind false false))], 7⟩,
   ⟨[.effect 30, .post (.post (.bind false true))], 7⟩]

def first : Reply Nat Nat Nat × Q :=
  next retainedCall (start (initial : S) orderedAlternatives [])

def second : Reply Nat Nat Nat × Q := next retainedCall first.2

theorem rejected_effects_survive_and_duplicates_are_occurrences :
    first.1 = .answer 7 ∧ second.1 = .answer 7 ∧
      first.2.effects = [10, 20] ∧ second.2.effects = [10, 20, 30] ∧
      (next retainedCall second.2).1 = .exhausted := by decide

/-- A selected answer's bindings disappear on discard but survive cut. -/
theorem cut_and_discard_differ :
    let selected := first.2.selected.getD initial
    (retainedCall (.post (.bind false true)) selected).1 = false ∧
      (retainedCall (.post (.bind false true)) (discard first.2).base).1 = true ∧
      cut first.2 = some (start selected [] [10, 20]) := by
  refine ⟨by decide, by decide, ?_⟩
  rfl

/-- Exceptions preserve preceding effects, restore the base, and do not run the
remaining alternatives or the throwing branch's suffix. -/
def throwing : List A :=
  [⟨[.effect 1, .post (.post (.bind false true)), .raise 42, .effect 2], 7⟩,
   ⟨[.effect 3], 8⟩]

theorem exception_is_not_failed_alternative :
    let result := next retainedCall (start (initial : S) throwing [])
    result.1 = .raised 42 ∧ result.2.effects = [1] ∧
      (retainedCall (.post (.bind false false)) result.2.base).1 = true ∧
      result.2.alternatives = [] := by decide

/-- The paused prefix posts a constraint and emits one effect. Resuming its
suffix uses both without replaying either operation. -/
def pausing : A :=
  ⟨[.effect 1, .post (.post (.bind false true)), .await 9,
      .effect 2, .post (.post (.bind true false))], 7⟩

def paused : Reply Nat Nat Nat × Q :=
  next retainedCall (start (initial : S) [pausing] [])

theorem resume_keeps_prefix_once :
    paused.1 = .suspended 9 ∧ paused.2.effects = [1] ∧
      (next retainedCall paused.2).2.effects = [1] ∧
      (resume retainedCall 8 paused.2).1 = .unexpectedResume ∧
      (resume retainedCall 8 paused.2).2.effects = [1] ∧
      (resume retainedCall 9 paused.2).1 = .answer 7 ∧
      (resume retainedCall 9 paused.2).2.effects = [1, 2] := by decide

/-- Reopening the original alternative after suspension is observably wrong:
it repeats an already performed persistent action and suspends again. -/
theorem replaying_suspended_prefix_is_wrong :
    (execute retainedCall pausing.answer pausing.code (initial : S) paused.2.effects).effects =
      [1, 1] ∧
    (execute retainedCall pausing.answer pausing.code (initial : S) paused.2.effects).signal ≠
      .answer 7 := by decide

/-- Final solver state does not determine persistent actions: failure rolls
bindings back but cannot undo an action that has already happened. -/
theorem rolling_effects_back_would_lose_observations :
    let result := next retainedCall (start (initial : S)
      ([⟨[.effect 10, .post (.post (.bind false true)),
           .post (.post (.bind false false))], 7⟩] : List A) [])
    result.1 = .exhausted ∧ result.2.effects = [10] ∧ result.2.effects ≠ [] := by decide

def boundLeft : S := (retainedCall (.post (.bind false true)) initial).2

theorem narrow_demand_does_not_justify_dropping_state :
    demandObservation [] boundLeft = demandObservation [] (initial : S) ∧
      demandObservation [false] boundLeft ≠ demandObservation [false] (initial : S) ∧
      (retainedCall (.post (.bind false false)) boundLeft).1 = false ∧
      (retainedCall (.post (.bind false false)) (initial : S)).1 = true := by decide

/-- A paused cut is rejected; the wrong token is observationally distinct from
solver exhaustion, and discarding after an answer is explicit in the trace. -/
theorem finite_lifecycle_trace_retains_protocol_observations :
    let result := run retainedCall
      [.next, .cut, .resume 8, .resume 9, .discard, .next]
      (start (initial : S) [pausing] [])
    result.1 = [.service (.suspended 9), .deniedCut,
      .service .unexpectedResume, .service (.answer 7), .discarded,
      .service .exhausted] ∧ result.2.effects = [1, 2] := by decide

end Controls
end Mettapedia.Machines.IncrementalConformance.ForeignQueryLifecycle

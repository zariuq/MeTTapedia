import Mettapedia.GSLT.LanguageDef.CommittedFallback
import Mettapedia.GSLT.Core.SemanticImplementation

/-!
# Lowering committed fallback to a native choice marker

The source rules are `CommittedFallback.Step`. The target is an independently
defined switch over a cursor, a query selector and a persistent success marker.
It uses the same host operations, worlds and answer payloads, not a second
checker. `cover` gives both step preservation and no invented target steps
from compiled states. The target is a GSLT in its own right.

This is a control-representation theorem. It does not verify a C allocator,
trail restoration, ownership, effectful answer consumers, the source parser,
or all of PeTTa's typing rules. In particular, the answer log records query
answers, before an enclosing continuation filters or executes them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CommittedFallbackNative

open Mettapedia.GSLT.LanguageDef.HostCalls (Pull)
open Mettapedia.GSLT.LanguageDef.CommittedFallback
open Mettapedia.GSLT.IndexedOperational

variable {Cursor Answer World Fault : Type}

/-- A flat target record; the success bit belongs to the fallback choice,
not to a backtrackable answer binding. -/
structure Native (Cursor Answer World Fault : Type) where
  cursor : Option Cursor
  useFallback : Bool
  succeeded : Bool
  error : Option Fault
  world : World
  answers : List Answer
  deriving DecidableEq, Repr

def encode (s : State Cursor Answer World Fault) : Native Cursor Answer World Fault :=
  match s.phase with
  | .probing c => ⟨some c, false, false, none, s.world, s.answers⟩
  | .committed c => ⟨some c, false, true, none, s.world, s.answers⟩
  | .fallback c => ⟨some c, true, false, none, s.world, s.answers⟩
  | .done => ⟨none, false, false, none, s.world, s.answers⟩
  | .fault e => ⟨none, false, false, some e, s.world, s.answers⟩

/-- Decoding rejects impossible combinations, rather than giving them a new
source meaning. It is a proof boundary, not a hot-path runtime operation. -/
def decode (n : Native Cursor Answer World Fault) : Option (State Cursor Answer World Fault) :=
  match n.cursor, n.useFallback, n.succeeded, n.error with
  | some c, false, false, none => some ⟨.probing c, n.world, n.answers⟩
  | some c, false, true, none => some ⟨.committed c, n.world, n.answers⟩
  | some c, true, false, none => some ⟨.fallback c, n.world, n.answers⟩
  | none, false, false, none => some ⟨.done, n.world, n.answers⟩
  | none, false, false, some e => some ⟨.fault e, n.world, n.answers⟩
  | _, _, _, _ => none

@[simp] theorem decode_encode (s : State Cursor Answer World Fault) :
    decode (encode s) = some s := by
  rcases s with ⟨phase, world, answers⟩
  cases phase <;> rfl

theorem encode_injective : Function.Injective
    (encode (Cursor := Cursor) (Answer := Answer) (World := World) (Fault := Fault)) := by
  intro s t same
  have := congrArg decode same
  simpa only [decode_encode, Option.some.injEq] using this

@[simp] theorem encode_world (s : State Cursor Answer World Fault) :
    (encode s).world = s.world := by
  rcases s with ⟨phase, world, answers⟩
  cases phase <;> rfl

@[simp] theorem encode_answers (s : State Cursor Answer World Fault) :
    (encode s).answers = s.answers := by
  rcases s with ⟨phase, world, answers⟩
  cases phase <;> rfl

/-- Direct target control. The marker is set before publishing the first
exact answer; later exact answers remain available. Exhaustion consults it. -/
def next (q : Queries Cursor Answer World Fault) (n : Native Cursor Answer World Fault) :
    Option (Native Cursor Answer World Fault) := do
  let c ← n.cursor
  if n.error.isSome then none else
    let pulled := if n.useFallback then q.fallback c n.world else q.exact c n.world
    match pulled.2 with
    | .error e => some ⟨none, false, false, some e, pulled.1, n.answers⟩
    | .ok .done =>
        if n.useFallback || n.succeeded then
          some ⟨none, false, false, none, pulled.1, n.answers⟩
        else
          some ⟨some (q.startFallback pulled.1), true, false, none, pulled.1, n.answers⟩
    | .ok (.yield a rest) =>
        some ⟨some rest, n.useFallback, !n.useFallback, none, pulled.1, n.answers ++ [a]⟩
    | .ok (.suspend rest) =>
        some {n with cursor := some rest, world := pulled.1}

def TargetStep (q : Queries Cursor Answer World Fault)
    (s t : Native Cursor Answer World Fault) : Prop := next q s = some t

theorem preserves_step {q : Queries Cursor Answer World Fault}
    {s t : State Cursor Answer World Fault} (step : Step q s t) :
    TargetStep q (encode s) (encode t) := by
  cases step <;> simp_all [TargetStep, encode, next]

/-- Every transition from a compiled state has a source rule. This is the
backward obligation absent from a mere forward simulation. -/
theorem reflects_step {q : Queries Cursor Answer World Fault}
    {s : State Cursor Answer World Fault} {t : Native Cursor Answer World Fault}
    (step : TargetStep q (encode s) t) :
    ∃ s', Step q s s' ∧ encode s' = t := by
  rcases s with ⟨phase, world, answers⟩
  cases phase with
  | done => simp [TargetStep, encode, next] at step
  | fault e => simp [TargetStep, encode, next] at step
  | probing c =>
      cases pulled : q.exact c world with
      | mk world' result =>
          cases result with
          | error e =>
              simp [TargetStep, encode, next, pulled] at step
              exact ⟨⟨.fault e, world', answers⟩, .probingFault pulled, step⟩
          | ok reply =>
              cases reply with
              | done =>
                  simp [TargetStep, encode, next, pulled] at step
                  exact ⟨⟨.fallback (q.startFallback world'), world', answers⟩,
                    .probingDone pulled, step⟩
              | yield a rest =>
                  simp [TargetStep, encode, next, pulled] at step
                  exact ⟨⟨.committed rest, world', answers ++ [a]⟩,
                    .probingYield pulled, step⟩
              | suspend rest =>
                  simp [TargetStep, encode, next, pulled] at step
                  exact ⟨⟨.probing rest, world', answers⟩, .probingSuspend pulled, step⟩
  | committed c =>
      cases pulled : q.exact c world with
      | mk world' result =>
          cases result with
          | error e =>
              simp [TargetStep, encode, next, pulled] at step
              exact ⟨⟨.fault e, world', answers⟩, .committedFault pulled, step⟩
          | ok reply =>
              cases reply with
              | done =>
                  simp [TargetStep, encode, next, pulled] at step
                  exact ⟨⟨.done, world', answers⟩, .committedDone pulled, step⟩
              | yield a rest =>
                  simp [TargetStep, encode, next, pulled] at step
                  exact ⟨⟨.committed rest, world', answers ++ [a]⟩,
                    .committedYield pulled, step⟩
              | suspend rest =>
                  simp [TargetStep, encode, next, pulled] at step
                  exact ⟨⟨.committed rest, world', answers⟩, .committedSuspend pulled, step⟩
  | fallback c =>
      cases pulled : q.fallback c world with
      | mk world' result =>
          cases result with
          | error e =>
              simp [TargetStep, encode, next, pulled] at step
              exact ⟨⟨.fault e, world', answers⟩, .fallbackFault pulled, step⟩
          | ok reply =>
              cases reply with
              | done =>
                  simp [TargetStep, encode, next, pulled] at step
                  exact ⟨⟨.done, world', answers⟩, .fallbackDone pulled, step⟩
              | yield a rest =>
                  simp [TargetStep, encode, next, pulled] at step
                  exact ⟨⟨.fallback rest, world', answers ++ [a]⟩,
                    .fallbackYield pulled, step⟩
              | suspend rest =>
                  simp [TargetStep, encode, next, pulled] at step
                  exact ⟨⟨.fallback rest, world', answers⟩, .fallbackSuspend pulled, step⟩

theorem step_iff (q : Queries Cursor Answer World Fault)
    (s t : State Cursor Answer World Fault) :
    TargetStep q (encode s) (encode t) ↔ Step q s t := by
  constructor
  · intro step
    obtain ⟨s', sourceStep, encoded⟩ := reflects_step step
    have same := encode_injective encoded
    subst s'
    exact sourceStep
  · exact preserves_step

/-- Valid representation is closed under native execution. -/
theorem target_step_closed {q : Queries Cursor Answer World Fault}
    {s t : Native Cursor Answer World Fault} (valid : ∃ source, encode source = s)
    (step : TargetStep q s t) : ∃ source, encode source = t := by
  obtain ⟨source, rfl⟩ := valid
  obtain ⟨source', _, represented⟩ := reflects_step step
  exact ⟨source', represented⟩

theorem source_deterministic {q : Queries Cursor Answer World Fault}
    {s t u : State Cursor Answer World Fault} (first : Step q s t) (second : Step q s u) :
    t = u := by
  apply encode_injective
  exact Option.some.inj ((preserves_step first).symm.trans (preserves_step second))

/-- The source calculus is ordinary operational rewriting, with no additional
equations identifying differently ordered answer occurrences. -/
def sourceGSLT (q : Queries Cursor Answer World Fault) : Mettapedia.GSLT.GSLT where
  Term := State Cursor Answer World Fault
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step q
  rewrites_resp_left := by intro s s' t same step; cases same; exact ⟨t, step, rfl⟩
  rewrites_resp_right := by intro s t t' step same; cases same; exact step

def targetGSLT (q : Queries Cursor Answer World Fault) : Mettapedia.GSLT.GSLT where
  Term := Native Cursor Answer World Fault
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := TargetStep q
  rewrites_resp_left := by intro s s' t same step; cases same; exact ⟨t, step, rfl⟩
  rewrites_resp_right := by intro s t t' step same; cases same; exact step

/-- An actual two-sided GSLT compilation seam, rather than a digest or rule-name
agreement. The target switch is not defined by calling the source relation. -/
def cover (q : Queries Cursor Answer World Fault) :
    SemanticCoveredTranslation (sourceGSLT q) (targetGSLT q) where
  mapTerm := encode
  mapEquiv := by intro s t same; cases same; rfl
  mapStep := preserves_step
  liftStep := reflects_step

/-- Reflection lifts arbitrary native endpoints, deriving validity rather
than assuming the final state is already a compiled source state. -/
theorem reflects_reaches {q : Queries Cursor Answer World Fault}
    {start finish : Native Cursor Answer World Fault}
    (route : Relation.ReflTransGen (TargetStep q) start finish) :
    ∀ s, encode s = start → ∃ t, Reaches q s t ∧ encode t = finish := by
  induction route with
  | refl => intro s same; exact ⟨s, .refl, same⟩
  | tail _ step ih =>
      intro s same
      obtain ⟨middle, before, encoded⟩ := ih s same
      rw [← encoded] at step
      obtain ⟨finish, after, encodedFinish⟩ := reflects_step step
      exact ⟨finish, before.tail after, encodedFinish⟩

theorem native_reaches_iff (q : Queries Cursor Answer World Fault)
    (s t : State Cursor Answer World Fault) :
    Relation.ReflTransGen (TargetStep q) (encode s) (encode t) ↔ Reaches q s t := by
  constructor
  · intro route
    obtain ⟨t', reach, same⟩ := reflects_reaches route s rfl
    have := encode_injective same
    subst t'
    exact reach
  · intro route
    induction route with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail (preserves_step step)

/-- The observation includes ordered payloads and the performed world, not
only the existence of a successful query. Stores can be part of each payload. -/
theorem reachable_observation_exact {q : Queries Cursor Answer World Fault}
    {s : State Cursor Answer World Fault} {t : Native Cursor Answer World Fault}
    (route : Relation.ReflTransGen (TargetStep q) (encode s) t) :
    ∃ source, Reaches q s source ∧ source.answers = t.answers ∧ source.world = t.world := by
  obtain ⟨source, reach, encoded⟩ := reflects_reaches route s rfl
  refine ⟨source, reach, ?_, ?_⟩
  · simpa only [encode_answers] using congrArg Native.answers encoded
  · simpa only [encode_world] using congrArg Native.world encoded

/-- Native query control after an exact answer cannot enter fallback.
This does not model an enclosing consumer's execution or side effects. -/
theorem native_committed_never_fallback {q : Queries Cursor Answer World Fault}
    {c : Cursor} {w : World} {as : List Answer} {t : State Cursor Answer World Fault}
    (route : Relation.ReflTransGen (TargetStep q)
      (encode ⟨.committed c, w, as⟩) (encode t)) : ¬ IsFallback t.phase :=
  committed_never_fallback ((native_reaches_iff q _ _).mp route)

namespace Controls

/-- Only the native target is run; the source remains an inductive relation. -/
def tick (q : Queries Cursor Answer World Fault) (s : Native Cursor Answer World Fault) :
    Native Cursor Answer World Fault := (next q s).getD s

def run (q : Queries Cursor Answer World Fault) :
    Nat → Native Cursor Answer World Fault → Native Cursor Answer World Fault
  | 0, state => state
  | n + 1, state => run q n (tick q state)

def listQueries : Queries (List Nat) Nat Nat String where
  exact c w := (w + 1, .ok (match c with
    | [] => .done
    | a :: rest => .yield a rest))
  fallback c w := (w + 1, .ok (match c with
    | [] => .done
    | a :: rest => .yield a rest))
  startFallback _ := [99]

theorem duplicate_answers_not_cut :
    (run listQueries 3 (encode ⟨.probing [7, 7], 0, []⟩)).answers = [7, 7] := by decide

theorem answerless_exhaustion_uses_fallback :
    (run listQueries 3 (encode ⟨.probing [], 0, []⟩)).answers = [99] := by decide

theorem exhaustion_world_is_retained :
    (run listQueries 3 (encode ⟨.probing [], 0, []⟩)).world = 3 := by decide

/-- Dropping every successful exact answer is not answerless exact exhaustion. -/
theorem consumer_failure_does_not_reopen_fallback :
    ((run listQueries 3 (encode ⟨.probing [7, 7], 0, []⟩)).answers.filter (· == 99)) = [] :=
  by decide

def suspendedQueries : Queries Nat Nat Nat String where
  exact c w := (w + 1, .ok (.suspend (c + 1)))
  fallback _ w := (w + 1, .ok (.yield 99 0))
  startFallback _ := 0

theorem suspension_is_not_exhaustion :
    run suspendedQueries 8 (encode ⟨.probing 0, 0, []⟩) =
      encode ⟨.probing 8, 8, []⟩ := by decide

def faultQueries : Queries Nat Nat Nat String where
  exact _ w := (w + 1, .error "query fault")
  fallback _ w := (w + 1, .ok (.yield 99 0))
  startFallback _ := 0

theorem fault_is_not_exhaustion :
    run faultQueries 8 (encode ⟨.probing 0, 0, []⟩) =
      encode ⟨.fault "query fault", 1, []⟩ := by decide

/-- An unconditional fallback would invent an answer after an exact success. -/
def forgetCommit (q : Queries Cursor Answer World Fault) :
    Nat → Native Cursor Answer World Fault → Native Cursor Answer World Fault
  | 0, state => state
  | n + 1, state =>
      forgetCommit q n ((next q {state with succeeded := false}).getD state)

theorem forgetting_commit_invents_fallback :
    (forgetCommit listQueries 3 (encode ⟨.probing [7], 0, []⟩)).answers = [7, 99] ∧
      (run listQueries 3 (encode ⟨.probing [7], 0, []⟩)).answers = [7] := by decide

def bindingQueries : Queries (List (Nat × Nat)) (Nat × Nat) Nat String where
  exact c w := (w + 1, .ok (match c with
    | [] => .done
    | a :: rest => .yield a rest))
  fallback _ w := (w + 1, .ok .done)
  startFallback _ := []

/-- The same value with two different answer contexts remains two occurrences. -/
theorem binding_payloads_are_retained :
    (run bindingQueries 3 (encode ⟨.probing [(7, 1), (7, 2)], 0, []⟩)).answers =
      [(7, 1), (7, 2)] := by decide

/-- Existence cannot reconstruct relational refinements, even with just one
value and one binding in each stream. -/
theorem no_boolean_answer_decoder :
    ¬ ∃ decode : Bool → List (Nat × Nat),
      ∀ answers, decode (!answers.isEmpty) = answers := by
  rintro ⟨decode, exactAnswers⟩
  have first := exactAnswers [(7, 1)]
  have second := exactAnswers [(7, 2)]
  simp only [List.isEmpty_cons, Bool.not_false] at first second
  have same := first.symm.trans second
  simp at same

end Controls

end Mettapedia.GSLT.LanguageDef.CommittedFallbackNative

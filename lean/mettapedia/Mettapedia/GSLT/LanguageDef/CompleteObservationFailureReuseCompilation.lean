import Mettapedia.GSLT.Dynamics.AnswerEffect
import Mathlib.Tactic

/-!
# Completed-empty reuse for complete search observations

The source language below has authored choice, named recursive calls, answer
occurrences, and an explicit caller continuation.  Two independent executable
evaluators implement its complete-observation strategy.  The second keeps a
bounded cache of exact `(revision, call)` keys, with no answers in cache entries.
It stores a key only after that call's own body has normally returned no answers.

This is a complete-observation strategy: a bind first completes its producer,
then visits its caller continuations in answer-occurrence order.  Interrupted
computations publish their terminal reason, not a partial answer prefix.  This
does not model a streaming evaluator's interleaving of caller effects with later
callee answers.  Effect, cut, exception, and physical decline are explicit
terminal boundaries here; none is an empty answer computation.

Program revisions select actual authored bodies.  Equal revision identifiers
must designate the same program authority; reusing a revision identifier for a
different mutable program is outside this model.  Keys are exact, not variants.
There is no claim about variable renaming, a C call delimiter, physical key
ownership, or profitability.  Fuel bounds interpreter recursion; reuse may
change sufficient fuel, so arbitrary equal-fuel observations need not agree.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CompleteObservationFailureReuseCompilation

open Mettapedia.GSLT.Dynamics.AnswerEffects

/-- These boundaries interrupt this complete-observation strategy. -/
inductive Interruption where
  | effect (label : Nat)
  | cut
  | exception (label : Nat)
  | decline
  deriving DecidableEq, Repr

/-- Lists retain source occurrence order and duplicate answers. -/
inductive Observation where
  | complete (answers : List Nat)
  | interrupted (reason : Interruption)
  deriving DecidableEq, Repr

/-- Exhaustion is an incomplete interpreter execution, not a terminal empty
observation and not a physical-provider decline. -/
inductive Verdict where
  | terminal (observation : Observation)
  | exhausted
  deriving DecidableEq, Repr

inductive Expr where
  | zero
  | answer (value : Nat)
  | choice (left right : Expr)
  | call (key : Nat)
  | bind (producer : Expr) (next : Nat → Expr)
  | underRevision (revision : Nat) (body : Expr)
  | interrupt (reason : Interruption)

abbrev Program := Nat → Nat → Expr
abbrev Key := Nat × Nat
abbrev Cache := List Key

/-- Caller continuations occur once per producer occurrence, including equal
answers.  This is the executable list-effect bind spine. -/
def continuations (next : Nat → Expr) : List Nat → Expr
  | [] => .zero
  | answer :: rest => .choice (next answer) (continuations next rest)

def prepend (answers : List Nat) : Observation → Observation
  | .complete following => .complete (listEffect.choice answers following)
  | .interrupted reason => .interrupted reason

/-- The ordinary evaluator has no cache or memoization oracle. -/
def reference (program : Program) : Nat → Nat → Expr → Verdict
  | 0, _, _ => .exhausted
  | _ + 1, _, .zero => .terminal (.complete [])
  | _ + 1, _, .answer value => .terminal (.complete [value])
  | _ + 1, _, .interrupt reason => .terminal (.interrupted reason)
  | fuel + 1, revision, .choice left right =>
      match reference program fuel revision left with
      | .exhausted => .exhausted
      | .terminal (.interrupted reason) => .terminal (.interrupted reason)
      | .terminal (.complete answers) =>
          match reference program fuel revision right with
          | .exhausted => .exhausted
          | .terminal observation => .terminal (prepend answers observation)
  | fuel + 1, revision, .call key =>
      reference program fuel revision (program revision key)
  | fuel + 1, revision, .bind producer next =>
      match reference program fuel revision producer with
      | .exhausted => .exhausted
      | .terminal (.interrupted reason) => .terminal (.interrupted reason)
      | .terminal (.complete answers) =>
          reference program fuel revision (continuations next answers)
  | fuel + 1, _, .underRevision revision body =>
      reference program fuel revision body

/-- Finite authored call/return executions, independently specified without
fuel, cache, or a supplied total denotation. -/
inductive Executes (program : Program) : Nat → Expr → Observation → Prop where
  | zero (revision : Nat) : Executes program revision .zero (.complete [])
  | answer (revision value : Nat) :
      Executes program revision (.answer value) (.complete [value])
  | interrupt (revision : Nat) (reason : Interruption) :
      Executes program revision (.interrupt reason) (.interrupted reason)
  | choiceComplete {revision : Nat} {left right : Expr} {answers : List Nat}
      {observation : Observation}
      (first : Executes program revision left (.complete answers))
      (second : Executes program revision right observation) :
      Executes program revision (.choice left right) (prepend answers observation)
  | choiceInterrupted {revision : Nat} {left right : Expr} {reason : Interruption}
      (first : Executes program revision left (.interrupted reason)) :
      Executes program revision (.choice left right) (.interrupted reason)
  | call {revision key : Nat} {observation : Observation}
      (body : Executes program revision (program revision key) observation) :
      Executes program revision (.call key) observation
  | bindComplete {revision : Nat} {producer : Expr} {next : Nat → Expr}
      {answers : List Nat} {observation : Observation}
      (returned : Executes program revision producer (.complete answers))
      (caller : Executes program revision (continuations next answers) observation) :
      Executes program revision (.bind producer next) observation
  | bindInterrupted {revision : Nat} {producer : Expr} {next : Nat → Expr}
      {reason : Interruption}
      (returned : Executes program revision producer (.interrupted reason)) :
      Executes program revision (.bind producer next) (.interrupted reason)
  | underRevision {outer revision : Nat} {body : Expr} {observation : Observation}
      (executed : Executes program revision body observation) :
      Executes program outer (.underRevision revision body) observation

theorem reference_sound {program : Program} (fuel revision : Nat) (expression : Expr)
    (observation : Observation)
    (completed : reference program fuel revision expression = .terminal observation) :
    Executes program revision expression observation := by
  induction fuel generalizing revision expression observation with
  | zero => simp [reference] at completed
  | succ fuel inductionHypothesis =>
      cases expression with
      | zero =>
          simp only [reference, Verdict.terminal.injEq] at completed
          subst observation
          exact .zero revision
      | answer value =>
          simp only [reference, Verdict.terminal.injEq] at completed
          subst observation
          exact .answer revision value
      | interrupt reason =>
          simp only [reference, Verdict.terminal.injEq] at completed
          subst observation
          exact .interrupt revision reason
      | call key => exact .call (inductionHypothesis _ _ _ completed)
      | underRevision current body =>
          exact .underRevision (inductionHypothesis _ _ _ completed)
      | choice left right =>
          cases first : reference program fuel revision left with
          | exhausted => simp [reference, first] at completed
          | terminal result =>
              cases result with
              | interrupted reason =>
                  simp only [reference, first, Verdict.terminal.injEq] at completed
                  subst observation
                  exact .choiceInterrupted (inductionHypothesis _ _ _ first)
              | complete answers =>
                  cases second : reference program fuel revision right with
                  | exhausted => simp [reference, first, second] at completed
                  | terminal following =>
                      simp only [reference, first, second,
                        Verdict.terminal.injEq] at completed
                      subst observation
                      exact .choiceComplete (inductionHypothesis _ _ _ first)
                        (inductionHypothesis _ _ _ second)
      | bind producer next =>
          cases returned : reference program fuel revision producer with
          | exhausted => simp [reference, returned] at completed
          | terminal result =>
              cases result with
              | interrupted reason =>
                  simp only [reference, returned, Verdict.terminal.injEq] at completed
                  subst observation
                  exact .bindInterrupted (inductionHypothesis _ _ _ returned)
              | complete answers =>
                  simp only [reference, returned] at completed
                  exact .bindComplete (inductionHypothesis _ _ _ returned)
                    (inductionHypothesis _ _ _ completed)

/-- Each finite execution has a sufficient depth, and every greater depth
realizes the same complete observation. -/
theorem Executes.reference_eventually {program : Program} {revision : Nat}
    {expression : Expr} {observation : Observation}
    (executed : Executes program revision expression observation) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      reference program fuel revision expression = .terminal observation := by
  induction executed with
  | zero revision =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel <;> simp_all [reference]
  | answer revision value =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel <;> simp_all [reference]
  | interrupt revision reason =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel <;> simp_all [reference]
  | choiceComplete first second firstIH secondIH =>
      obtain ⟨firstBound, firstExact⟩ := firstIH
      obtain ⟨secondBound, secondExact⟩ := secondIH
      refine ⟨max firstBound secondBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [reference, firstExact fuel (by omega), secondExact fuel (by omega)]
  | choiceInterrupted first firstIH =>
      obtain ⟨bound, exactAt⟩ := firstIH
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [reference, exactAt fuel (by omega)]
  | call body bodyIH =>
      obtain ⟨bound, exactAt⟩ := bodyIH
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => exact exactAt fuel (by omega)
  | bindComplete returned caller returnedIH callerIH =>
      obtain ⟨returnBound, returnExact⟩ := returnedIH
      obtain ⟨callerBound, callerExact⟩ := callerIH
      refine ⟨max returnBound callerBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [reference, returnExact fuel (by omega), callerExact fuel (by omega)]
  | bindInterrupted returned returnedIH =>
      obtain ⟨bound, exactAt⟩ := returnedIH
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [reference, exactAt fuel (by omega)]
  | underRevision executed executedIH =>
      obtain ⟨bound, exactAt⟩ := executedIH
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => exact exactAt fuel (by omega)

theorem Executes.deterministic {program : Program} {revision : Nat}
    {expression : Expr} {first second : Observation}
    (firstExec : Executes program revision expression first)
    (secondExec : Executes program revision expression second) : first = second := by
  obtain ⟨firstBound, firstExact⟩ := firstExec.reference_eventually
  obtain ⟨secondBound, secondExact⟩ := secondExec.reference_eventually
  have equal := (firstExact (max firstBound secondBound) (by omega)).symm.trans
    (secondExact (max firstBound secondBound) (by omega))
  exact Verdict.terminal.inj equal

/-- Newest completed receipts are retained up to capacity.  Hits do not
change their age.  Capacity zero disables retention. -/
def remember (capacity : Nat) (key : Key) (cache : Cache) : Cache :=
  (key :: cache).take capacity

structure MemoRun where
  verdict : Verdict
  cache : Cache
  deriving DecidableEq, Repr

/-- Publication occurs at the callee's own complete return, before any
surrounding `bind` runs its caller continuations. -/
def finishCall (capacity : Nat) (key : Key) (run : MemoRun) : MemoRun :=
  if run.verdict = .terminal (.complete []) then
    { run with cache := remember capacity key run.cache }
  else run

@[simp] theorem finishCall_verdict (capacity : Nat) (key : Key) (run : MemoRun) :
    (finishCall capacity key run).verdict = run.verdict := by
  simp only [finishCall]
  split <;> rfl

/-- Independent memoizing evaluator.  Entries contain only exact keys; an
in-progress call is never inserted or treated as a failed call. -/
def cached (program : Program) (capacity : Nat) :
    Nat → Nat → Expr → Cache → MemoRun
  | 0, _, _, cache => ⟨.exhausted, cache⟩
  | _ + 1, _, .zero, cache => ⟨.terminal (.complete []), cache⟩
  | _ + 1, _, .answer value, cache => ⟨.terminal (.complete [value]), cache⟩
  | _ + 1, _, .interrupt reason, cache =>
      ⟨.terminal (.interrupted reason), cache⟩
  | fuel + 1, revision, .choice left right, cache =>
      let first := cached program capacity fuel revision left cache
      match first.verdict with
      | .exhausted => first
      | .terminal (.interrupted _) => first
      | .terminal (.complete answers) =>
          let second := cached program capacity fuel revision right first.cache
          match second.verdict with
          | .exhausted => second
          | .terminal observation =>
              { second with verdict := .terminal (prepend answers observation) }
  | fuel + 1, revision, .call key, cache =>
      if (revision, key) ∈ cache then ⟨.terminal (.complete []), cache⟩
      else finishCall capacity (revision, key)
        (cached program capacity fuel revision (program revision key) cache)
  | fuel + 1, revision, .bind producer next, cache =>
      let returned := cached program capacity fuel revision producer cache
      match returned.verdict with
      | .exhausted => returned
      | .terminal (.interrupted _) => returned
      | .terminal (.complete answers) =>
          cached program capacity fuel revision (continuations next answers) returned.cache
  | fuel + 1, _, .underRevision revision body, cache =>
      cached program capacity fuel revision body cache

/-- A receipt is a finite authored execution of that exact call body, not
an assumed truth value supplied by a memoization oracle. -/
structure Coherent (program : Program) (capacity : Nat) (cache : Cache) : Prop where
  bounded : cache.length ≤ capacity
  receipts : ∀ key ∈ cache,
    Executes program key.1 (program key.1 key.2) (.complete [])

theorem coherent_empty (program : Program) (capacity : Nat) :
    Coherent program capacity [] := by
  constructor <;> simp

theorem Coherent.evict {program : Program} {capacity : Nat} {cache retained : Cache}
    (coherent : Coherent program capacity cache) (sublist : retained.Sublist cache) :
    Coherent program capacity retained := by
  exact ⟨sublist.length_le.trans coherent.bounded,
    fun key member => coherent.receipts key (sublist.subset member)⟩

theorem Coherent.remember {program : Program} {capacity : Nat} {cache : Cache}
    (coherent : Coherent program capacity cache) (key : Key)
    (completed : Executes program key.1 (program key.1 key.2) (.complete [])) :
    Coherent program capacity (remember capacity key cache) := by
  constructor
  · exact (List.length_take_le capacity (key :: cache))
  · intro entry member
    have origin := List.mem_of_mem_take member
    simp only [List.mem_cons] at origin
    rcases origin with equal | old
    · subst entry
      exact completed
    · exact coherent.receipts entry old

theorem coherent_finishCall {program : Program} {capacity : Nat} {key : Key}
    {run : MemoRun} (coherent : Coherent program capacity run.cache)
    (receipt : run.verdict = .terminal (.complete []) →
      Executes program key.1 (program key.1 key.2) (.complete [])) :
    Coherent program capacity (finishCall capacity key run).cache := by
  unfold finishCall
  split
  · exact coherent.remember key (receipt (by assumption))
  · exact coherent

/-- Every terminal memo execution reflects to actual authored execution.
The cache invariant is preserved even on exhaustion or interruption. -/
theorem cached_sound_and_coherent {program : Program} {capacity : Nat}
    (fuel revision : Nat) (expression : Expr) (cache : Cache)
    (coherent : Coherent program capacity cache) :
    Coherent program capacity (cached program capacity fuel revision expression cache).cache ∧
    ∀ observation,
      (cached program capacity fuel revision expression cache).verdict = .terminal observation →
      Executes program revision expression observation := by
  induction fuel generalizing revision expression cache with
  | zero =>
      refine ⟨coherent, ?_⟩
      intro observation impossible
      simp [cached] at impossible
  | succ fuel inductionHypothesis =>
      cases expression with
      | zero =>
          refine ⟨coherent, ?_⟩
          intro observation completed
          simp only [cached, Verdict.terminal.injEq] at completed
          subst observation
          exact .zero revision
      | answer value =>
          refine ⟨coherent, ?_⟩
          intro observation completed
          simp only [cached, Verdict.terminal.injEq] at completed
          subst observation
          exact .answer revision value
      | interrupt reason =>
          refine ⟨coherent, ?_⟩
          intro observation completed
          simp only [cached, Verdict.terminal.injEq] at completed
          subst observation
          exact .interrupt revision reason
      | underRevision current body =>
          obtain ⟨retained, sound⟩ := inductionHypothesis current body cache coherent
          exact ⟨retained, fun observation completed =>
            .underRevision (sound observation completed)⟩
      | call key =>
          by_cases hit : (revision, key) ∈ cache
          · simp only [cached, hit, ↓reduceIte]
            refine ⟨coherent, ?_⟩
            intro observation completed
            cases completed
            exact .call (coherent.receipts (revision, key) hit)
          · simp only [cached, hit, ↓reduceIte]
            obtain ⟨retained, sound⟩ :=
              inductionHypothesis revision (program revision key) cache coherent
            refine ⟨coherent_finishCall retained (sound (.complete [])), ?_⟩
            intro observation completed
            exact .call (sound observation (by simpa using completed))
      | choice left right =>
          obtain ⟨leftCoherent, leftSound⟩ :=
            inductionHypothesis revision left cache coherent
          cases first : (cached program capacity fuel revision left cache).verdict with
          | exhausted =>
              simp only [cached, first]
              exact ⟨leftCoherent, fun observation impossible => by
                cases impossible⟩
          | terminal result =>
              cases result with
              | interrupted reason =>
                  simp only [cached, first]
                  refine ⟨leftCoherent, ?_⟩
                  intro observation completed
                  cases completed
                  exact .choiceInterrupted (leftSound _ first)
              | complete answers =>
                  obtain ⟨rightCoherent, rightSound⟩ := inductionHypothesis revision right
                    (cached program capacity fuel revision left cache).cache leftCoherent
                  cases second : (cached program capacity fuel revision right
                    (cached program capacity fuel revision left cache).cache).verdict with
                  | exhausted =>
                      simp only [cached, first, second]
                      exact ⟨rightCoherent, fun observation impossible => by
                        cases impossible⟩
                  | terminal following =>
                      simp only [cached, first, second]
                      refine ⟨rightCoherent, ?_⟩
                      intro observation completed
                      cases completed
                      exact .choiceComplete (leftSound _ first) (rightSound _ second)
      | bind producer next =>
          obtain ⟨returnCoherent, returnSound⟩ :=
            inductionHypothesis revision producer cache coherent
          cases returned : (cached program capacity fuel revision producer cache).verdict with
          | exhausted =>
              simp only [cached, returned]
              exact ⟨returnCoherent, fun observation impossible => by
                cases impossible⟩
          | terminal result =>
              cases result with
              | interrupted reason =>
                  simp only [cached, returned]
                  refine ⟨returnCoherent, ?_⟩
                  intro observation completed
                  cases completed
                  exact .bindInterrupted (returnSound _ returned)
              | complete answers =>
                  obtain ⟨callerCoherent, callerSound⟩ := inductionHypothesis revision
                    (continuations next answers)
                    (cached program capacity fuel revision producer cache).cache returnCoherent
                  simp only [cached, returned]
                  exact ⟨callerCoherent, fun observation completed =>
                    .bindComplete (returnSound _ returned) (callerSound _ completed)⟩

/-- Every finite authored execution is realized with sufficient memo fuel,
uniformly over bounded coherent starting caches.  This supplies preservation,
while `cached_sound_and_coherent` supplies reflection. -/
theorem Executes.cached_eventually {program : Program} {capacity revision : Nat}
    {expression : Expr} {observation : Observation}
    (executed : Executes program revision expression observation) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∀ cache,
      Coherent program capacity cache →
      (cached program capacity fuel revision expression cache).verdict =
        .terminal observation := by
  induction executed with
  | zero revision =>
      refine ⟨1, ?_⟩
      intro fuel enough cache coherent
      cases fuel <;> simp_all [cached]
  | answer revision value =>
      refine ⟨1, ?_⟩
      intro fuel enough cache coherent
      cases fuel <;> simp_all [cached]
  | interrupt revision reason =>
      refine ⟨1, ?_⟩
      intro fuel enough cache coherent
      cases fuel <;> simp_all [cached]
  | @choiceComplete revision left right answers observation first second firstIH secondIH =>
      obtain ⟨firstBound, firstExact⟩ := firstIH
      obtain ⟨secondBound, secondExact⟩ := secondIH
      refine ⟨max firstBound secondBound + 1, ?_⟩
      intro fuel enough cache coherent
      cases fuel with
      | zero => omega
      | succ fuel =>
          have firstRun := firstExact fuel (by omega) cache coherent
          have firstCache :=
            (cached_sound_and_coherent fuel revision left cache coherent).1
          have secondRun := secondExact fuel (by omega)
            (cached program capacity fuel revision left cache).cache firstCache
          simp [cached, firstRun, secondRun]
  | choiceInterrupted first firstIH =>
      obtain ⟨bound, exactAt⟩ := firstIH
      refine ⟨bound + 1, ?_⟩
      intro fuel enough cache coherent
      cases fuel with
      | zero => omega
      | succ fuel => simp [cached, exactAt fuel (by omega) cache coherent]
  | @call revision key observation body bodyIH =>
      obtain ⟨bound, exactAt⟩ := bodyIH
      refine ⟨bound + 1, ?_⟩
      intro fuel enough cache coherent
      cases fuel with
      | zero => omega
      | succ fuel =>
          by_cases hit : (revision, key) ∈ cache
          · have same := body.deterministic (coherent.receipts (revision, key) hit)
            simp [cached, hit, same]
          · simpa [cached, hit] using exactAt fuel (by omega) cache coherent
  | @bindComplete revision producer next answers observation returned caller returnedIH callerIH =>
      obtain ⟨returnBound, returnExact⟩ := returnedIH
      obtain ⟨callerBound, callerExact⟩ := callerIH
      refine ⟨max returnBound callerBound + 1, ?_⟩
      intro fuel enough cache coherent
      cases fuel with
      | zero => omega
      | succ fuel =>
          have returnRun := returnExact fuel (by omega) cache coherent
          have returnCache :=
            (cached_sound_and_coherent fuel revision producer cache coherent).1
          have callerRun := callerExact fuel (by omega)
            (cached program capacity fuel revision producer cache).cache returnCache
          simp [cached, returnRun, callerRun]
  | bindInterrupted returned returnedIH =>
      obtain ⟨bound, exactAt⟩ := returnedIH
      refine ⟨bound + 1, ?_⟩
      intro fuel enough cache coherent
      cases fuel with
      | zero => omega
      | succ fuel => simp [cached, exactAt fuel (by omega) cache coherent]
  | underRevision executed executedIH =>
      obtain ⟨bound, exactAt⟩ := executedIH
      refine ⟨bound + 1, ?_⟩
      intro fuel enough cache coherent
      cases fuel with
      | zero => omega
      | succ fuel => exact exactAt fuel (by omega) cache coherent

/-- Closed initial-empty-cache equivalence.  Fuel witnesses may differ;
terminal observations retain duplicate answers and exact interruption reasons. -/
theorem initial_empty_finite_observation_iff (program : Program)
    (capacity revision : Nat) (expression : Expr) (observation : Observation) :
    (∃ fuel, (cached program capacity fuel revision expression []).verdict =
      .terminal observation) ↔
    (∃ fuel, reference program fuel revision expression = .terminal observation) := by
  constructor
  · rintro ⟨fuel, completed⟩
    have executed := (cached_sound_and_coherent fuel revision expression []
      (coherent_empty program capacity)).2 observation completed
    obtain ⟨bound, exactAt⟩ := executed.reference_eventually
    exact ⟨bound, exactAt bound (Nat.le_refl _)⟩
  · rintro ⟨fuel, completed⟩
    have executed := reference_sound fuel revision expression observation completed
    obtain ⟨bound, exactAt⟩ := executed.cached_eventually (capacity := capacity)
    exact ⟨bound, exactAt bound (Nat.le_refl _) [] (coherent_empty program capacity)⟩

/-- Every retained key, even after an incomplete outer execution, has an
actual finite ordinary empty-return witness under its recorded authority. -/
theorem initial_empty_retained_receipt (program : Program)
    (capacity fuel revision : Nat) (expression : Expr) (key : Key)
    (retained : key ∈ (cached program capacity fuel revision expression []).cache) :
    ∃ receiptFuel,
      reference program receiptFuel key.1 (program key.1 key.2) =
        .terminal (.complete []) := by
  have coherent := (cached_sound_and_coherent fuel revision expression []
    (coherent_empty program capacity)).1
  obtain ⟨bound, exactAt⟩ := (coherent.receipts key retained).reference_eventually
  exact ⟨bound, exactAt bound (Nat.le_refl _)⟩

theorem initial_empty_cache_bounded (program : Program)
    (capacity fuel revision : Nat) (expression : Expr) :
    (cached program capacity fuel revision expression []).cache.length ≤ capacity :=
  (cached_sound_and_coherent fuel revision expression []
    (coherent_empty program capacity)).1.bounded

/-- Caller failure cannot authorize a receipt for a successful callee.
This applies to every outer expression, including binds that discard all of
the callee's answers and outer executions that later interrupt or exhaust. -/
theorem successful_callee_never_retained {program : Program}
    (capacity fuel outerRevision : Nat) (outer : Expr) (key : Key)
    (answers : List Nat)
    (returned : Executes program key.1 (program key.1 key.2) (.complete answers))
    (nonempty : answers ≠ []) :
    key ∉ (cached program capacity fuel outerRevision outer []).cache := by
  intro retained
  have coherent := (cached_sound_and_coherent fuel outerRevision outer []
    (coherent_empty program capacity)).1
  have equal := returned.deterministic (coherent.receipts key retained)
  exact nonempty (Observation.complete.inj equal)

theorem interrupted_callee_never_retained {program : Program}
    (capacity fuel outerRevision : Nat) (outer : Expr) (key : Key)
    (reason : Interruption)
    (returned : Executes program key.1 (program key.1 key.2) (.interrupted reason)) :
    key ∉ (cached program capacity fuel outerRevision outer []).cache := by
  intro retained
  have coherent := (cached_sound_and_coherent fuel outerRevision outer []
    (coherent_empty program capacity)).1
  have impossible := returned.deterministic (coherent.receipts key retained)
  cases impossible

/-- Exact list agreement implies the requested occurrence-bag agreement.
No set quotient or deduplication is used by either evaluator. -/
theorem completed_answer_bags_equal {program : Program}
    (capacity referenceFuel cachedFuel revision : Nat) (expression : Expr)
    (ordinary memoized : List Nat)
    (referenceRun : reference program referenceFuel revision expression =
      .terminal (.complete ordinary))
    (memoRun : (cached program capacity cachedFuel revision expression []).verdict =
      .terminal (.complete memoized)) :
    (ordinary : Multiset Nat) = (memoized : Multiset Nat) := by
  have first := reference_sound referenceFuel revision expression _ referenceRun
  have second := (cached_sound_and_coherent cachedFuel revision expression []
    (coherent_empty program capacity)).2 _ memoRun
  have same := Observation.complete.inj (first.deterministic second)
  rw [same]

/-- At the declared answer effect, discarding an empty producer's caller
continuations is exactly the independently established zero-bind law. -/
theorem empty_answers_have_no_caller_occurrences (next : Nat → List Nat) :
    listEffect.bind (listEffect.empty : List Nat) next = listEffect.empty :=
  listEffect.empty_bind next

/-! ## Executable boundary examples -/

private def occurrenceProgram : Program := fun _ key =>
  if key = 0 then .zero
  else if key = 1 then .choice (.answer 7) (.answer 7)
  else .bind (.call 1) (fun _ => .zero)

theorem duplicate_occurrences_survive_empty_reuse :
    (cached occurrenceProgram 2 12 0
      (.choice (.call 0) (.choice (.call 0) (.call 1))) []).verdict =
        .terminal (.complete [7, 7]) ∧
    reference occurrenceProgram 12 0
      (.choice (.call 0) (.choice (.call 0) (.call 1))) =
        .terminal (.complete [7, 7]) := by
  decide

/-- The producer succeeds twice; its caller rejects both.  No producer key
is retained, despite the complete empty observation of the bind. -/
theorem caller_filter_failure_does_not_publish_callee_failure :
    cached occurrenceProgram 2 12 0 (.bind (.call 1) (fun _ => .zero)) [] =
      ⟨.terminal (.complete []), []⟩ := by
  decide

/-- The outer named computation really is empty and may be cached.  Its
successful child remains available, with both of its answer occurrences. -/
theorem empty_parent_does_not_poison_successful_child :
    cached occurrenceProgram 2 16 0 (.choice (.call 2) (.call 1)) [] =
      ⟨.terminal (.complete [7, 7]), [(0, 2)]⟩ := by
  decide

/-- An invented receipt would erase both successes.  Initial emptiness and
derived receipts are necessary, not decorative assumptions. -/
theorem fabricated_failure_receipt_loses_duplicate_answers :
    (cached occurrenceProgram 1 4 0 (.call 1) [(0, 1)]).verdict =
      .terminal (.complete []) ∧
    reference occurrenceProgram 4 0 (.call 1) =
      .terminal (.complete [7, 7]) := by
  decide

private def interruptedProgram (reason : Interruption) : Program := fun _ key =>
  if key = 0 then .zero else .choice (.call 0) (.interrupt reason)

/-- A completed inner failure remains justified, but its interrupted parent
never publishes a receipt.  The four explicit terminal boundaries share this
same operational check. -/
theorem interrupted_parent_retains_only_completed_child (reason : Interruption) :
    cached (interruptedProgram reason) 2 6 0 (.call 1) [] =
      ⟨.terminal (.interrupted reason), [(0, 0)]⟩ := by
  simp [cached, interruptedProgram, finishCall, remember, prepend]

theorem cut_is_not_empty :
    cached (interruptedProgram .cut) 2 6 0 (.call 1) [] =
      ⟨.terminal (.interrupted .cut), [(0, 0)]⟩ :=
  interrupted_parent_retains_only_completed_child .cut

theorem exception_is_not_empty :
    cached (interruptedProgram (.exception 4)) 2 6 0 (.call 1) [] =
      ⟨.terminal (.interrupted (.exception 4)), [(0, 0)]⟩ :=
  interrupted_parent_retains_only_completed_child (.exception 4)

theorem effect_boundary_is_not_empty :
    cached (interruptedProgram (.effect 4)) 2 6 0 (.call 1) [] =
      ⟨.terminal (.interrupted (.effect 4)), [(0, 0)]⟩ :=
  interrupted_parent_retains_only_completed_child (.effect 4)

theorem physical_decline_is_not_empty :
    cached (interruptedProgram .decline) 2 6 0 (.call 1) [] =
      ⟨.terminal (.interrupted .decline), [(0, 0)]⟩ :=
  interrupted_parent_retains_only_completed_child .decline

theorem successful_callee_before_caller_effect_is_not_retained :
    cached occurrenceProgram 2 8 0
      (.bind (.call 1) (fun _ => .interrupt (.effect 3))) [] =
        ⟨.terminal (.interrupted (.effect 3)), []⟩ := by
  decide

private def revisionProgram : Program := fun revision _ =>
  if revision = 0 then .zero else .answer 9

theorem changed_authority_recomputes_the_call :
    cached revisionProgram 1 8 0
      (.choice (.call 0) (.underRevision 1 (.call 0))) [] =
        ⟨.terminal (.complete [9]), [(0, 0)]⟩ := by
  decide

/-- Relabeling a previously valid receipt with a new revision invents
authority and loses a real answer.  The evaluator never performs this map. -/
theorem stale_receipt_relabeling_loses_answer :
    (cached revisionProgram 1 3 1 (.call 0) [(1, 0)]).verdict =
      .terminal (.complete []) ∧
    reference revisionProgram 3 1 (.call 0) = .terminal (.complete [9]) := by
  decide

private def recursiveProgram : Program := fun _ _ => .call 0

theorem recursive_reentry_reference_exhausts (fuel : Nat) :
    reference recursiveProgram fuel 0 (.call 0) = .exhausted := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis => simpa [reference, recursiveProgram] using inductionHypothesis

theorem recursive_reentry_cached_exhausts (capacity fuel : Nat) :
    cached recursiveProgram capacity fuel 0 (.call 0) [] = ⟨.exhausted, []⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp [cached, recursiveProgram, finishCall, inductionHypothesis]

/-- No finite fuel completes this recursive call, while prematurely marking
the active key as failed would manufacture a normal empty return. -/
theorem in_progress_is_not_a_completed_failure :
    (¬ ∃ fuel, reference recursiveProgram fuel 0 (.call 0) =
      .terminal (.complete [])) ∧
    (cached recursiveProgram 1 1 0 (.call 0) [(0, 0)]).verdict =
      .terminal (.complete []) := by
  constructor
  · rintro ⟨fuel, completed⟩
    rw [recursive_reentry_reference_exhausts] at completed
    cases completed
  · decide

private def emptyProgram : Program := fun _ _ => .zero

theorem bounded_eviction_forgets_old_key :
    cached emptyProgram 1 3 0 (.call 1) [(0, 0)] =
      ⟨.terminal (.complete []), [(0, 1)]⟩ := by
  decide

theorem evicted_failure_recomputes_without_new_answers :
    cached emptyProgram 1 8 0
      (.choice (.call 0) (.choice (.call 1) (.call 0))) [] =
        ⟨.terminal (.complete []), [(0, 0)]⟩ := by
  decide

theorem capacity_zero_retains_nothing :
    cached emptyProgram 0 8 0 (.choice (.call 0) (.call 0)) [] =
      ⟨.terminal (.complete []), []⟩ := by
  decide

/-- Eviction changes the work still required, so a fixed insufficient fuel
budget can cease to complete after an otherwise sound eviction. -/
theorem eviction_can_require_more_fuel :
    (cached emptyProgram 1 1 0 (.call 0) [(0, 0)]).verdict =
      .terminal (.complete []) ∧
    (cached emptyProgram 1 1 0 (.call 0) []).verdict = .exhausted := by
  decide

private def depthProgram : Program := fun _ key =>
  if key = 0 then .choice .zero .zero else .call 0

/-- This difference arises from an initially empty cache: the first call
establishes a receipt used by a later, more deeply nested occurrence. -/
theorem initial_empty_reuse_changes_sufficient_fuel :
    reference depthProgram 4 0 (.choice (.call 0) (.call 1)) = .exhausted ∧
    (cached depthProgram 2 4 0 (.choice (.call 0) (.call 1)) []).verdict =
      .terminal (.complete []) ∧
    reference depthProgram 5 0 (.choice (.call 0) (.call 1)) =
      .terminal (.complete []) := by
  decide

/-- Distinct exact call keys may encode distinct authored search budgets.
Failure of one such call provides no receipt for another one. -/
private def boundedQueryProgram : Program := fun _ bound =>
  if bound = 0 then .zero else .answer 11

theorem authored_budget_failure_is_not_global_falsity :
    cached boundedQueryProgram 1 5 0 (.choice (.call 0) (.call 1)) [] =
      ⟨.terminal (.complete [11]), [(0, 0)]⟩ := by
  decide

#print axioms reference_sound
#print axioms Executes.reference_eventually
#print axioms cached_sound_and_coherent
#print axioms Executes.cached_eventually
#print axioms initial_empty_finite_observation_iff
#print axioms initial_empty_retained_receipt
#print axioms successful_callee_never_retained
#print axioms interrupted_callee_never_retained
#print axioms completed_answer_bags_equal
#print axioms interrupted_parent_retains_only_completed_child
#print axioms recursive_reentry_cached_exhausts
#print axioms initial_empty_reuse_changes_sufficient_fuel

end Mettapedia.GSLT.LanguageDef.CompleteObservationFailureReuseCompilation

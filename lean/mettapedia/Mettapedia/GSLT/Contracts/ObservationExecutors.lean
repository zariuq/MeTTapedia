import Mathlib.Data.Seq.Basic
import Mettapedia.GSLT.Contracts.OccurrenceExecution

/-!
# Executors for occurrence observations

An executor reads a trace one batch at a time and may stop before the trace
ends. The executors for `first` and `presence` stop at the first answer, the
executor for `absence` reads the completed trace, and the executor for `count`
keeps only a number. On every completed trace each returns exactly `observe`
at its demand. On a run that may never complete, `first` and `presence` read
only the prefix up to the first answer, while an executor that never stops
early returns exactly on the runs that complete.

A route proved equal to another at one demand may serve every call site whose
demand that one determines, and no other. Collecting every answer and comparing
the collection with the empty one is determined by absence, but answering it
by presence is exact only on completed runs.

When each evaluation of a producer has an effect on a store, stopping early
skips the effects of the evaluations after the stop. With the store included
this is exact exactly when the skipped evaluations leave the reached store
unchanged. Templates that are data have no effect, so for them every executor
is exact, store included.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.ObservationExecutors

open OccurrenceObservers (Demand Result Trace observe Determines covers determines_iff)
open OccurrenceExecution (reports)

/-! ## Executors on completed traces -/

/-- An executor reads a trace one batch at a time. On each batch it either
continues in a new state or stops with its result; when the trace completes
first, it reports from its state. -/
structure Executor (A State R : Type) where
  start : State
  read : State → List A → State ⊕ R
  finish : State → R

namespace Executor

variable {A State R : Type}

/-- The result of reading a completed trace from a state. -/
def runFrom (e : Executor A State R) : State → Trace A → R
  | state, [] => e.finish state
  | state, batch :: rest =>
    match e.read state batch with
    | .inl next => e.runFrom next rest
    | .inr result => result

/-- The result of reading a completed trace from the start. -/
def run (e : Executor A State R) (trace : Trace A) : R := e.runFrom e.start trace

/-- The result, if the executor stops while reading these batches. -/
def stopIn (e : Executor A State R) : State → Trace A → Option R
  | _, [] => none
  | state, batch :: rest =>
    match e.read state batch with
    | .inl next => e.stopIn next rest
    | .inr result => some result

/-- How many batches of a completed trace the executor reads. -/
def readsFrom (e : Executor A State R) : State → Trace A → ℕ
  | _, [] => 0
  | state, batch :: rest =>
    match e.read state batch with
    | .inl next => e.readsFrom next rest + 1
    | .inr _ => 1

/-- An executor that stops within some batches never reads what follows them. -/
theorem runFrom_append_of_stopIn {e : Executor A State R} {state : State} {pre : Trace A}
    {result : R} (stops : e.stopIn state pre = some result) (rest : Trace A) :
    e.runFrom state (pre ++ rest) = result := by
  induction pre generalizing state with
  | nil => simp [stopIn] at stops
  | cons batch pre ih =>
    cases reading : e.read state batch with
    | inl next =>
      simp only [stopIn, reading] at stops
      simp only [List.cons_append, runFrom, reading]
      exact ih stops
    | inr stopped =>
      simp only [stopIn, reading, Option.some.injEq] at stops
      simp [runFrom, reading, stops]

theorem runFrom_cons_inl {e : Executor A State R} {state next : State} {batch : List A}
    (continues : e.read state batch = .inl next) (rest : Trace A) :
    e.runFrom state (batch :: rest) = e.runFrom next rest := by
  simp [runFrom, continues]

theorem runFrom_cons_inr {e : Executor A State R} {state : State} {batch : List A} {result : R}
    (stops : e.read state batch = .inr result) (rest : Trace A) :
    e.runFrom state (batch :: rest) = result := by
  simp [runFrom, stops]

theorem readsFrom_cons_inl {e : Executor A State R} {state next : State} {batch : List A}
    (continues : e.read state batch = .inl next) (rest : Trace A) :
    e.readsFrom state (batch :: rest) = e.readsFrom next rest + 1 := by
  simp [readsFrom, continues]

/-- Post-processing the result of an executor. -/
def map {R' : Type} (f : R → R') (e : Executor A State R) : Executor A State R' where
  start := e.start
  read state batch := (e.read state batch).map id f
  finish state := f (e.finish state)

theorem map_runFrom {R' : Type} (f : R → R') (e : Executor A State R) (state : State)
    (trace : Trace A) : (e.map f).runFrom state trace = f (e.runFrom state trace) := by
  induction trace generalizing state with
  | nil => rfl
  | cons batch rest ih =>
    cases reading : e.read state batch with
    | inl next =>
      simp only [runFrom, map, reading, Sum.map_inl, id]
      exact ih next
    | inr stopped => simp [runFrom, map, reading]

end Executor

open Executor

/-! ## Runs that may not complete -/

/-- A run publishes one batch per tick. It completes after finitely many
ticks, or it publishes a batch at every tick. A completed trace is the run
`Stream'.Seq.ofList trace`. -/
abbrev Run (A : Type) := Stream'.Seq (List A)

variable {A State R : Type}

/-- What an executor returns on a run: a finite reading that stops on a batch
or meets completion. On a run that never completes and on which the executor
never stops, it returns nothing. -/
inductive Yields (e : Executor A State R) : State → Run A → R → Prop
  | complete {state : State} {run : Run A} :
      Stream'.Seq.head run = none → Yields e state run (e.finish state)
  | stop {state : State} {run : Run A} {batch : List A} {result : R} :
      Stream'.Seq.head run = some batch → e.read state batch = .inr result →
      Yields e state run result
  | next {state after : State} {run : Run A} {batch : List A} {result : R} :
      Stream'.Seq.head run = some batch → e.read state batch = .inl after →
      Yields e after (Stream'.Seq.tail run) result → Yields e state run result

/-- An executor returns at most one result on a run. -/
theorem Yields.functional {e : Executor A State R} {state : State} {run : Run A}
    {first second : R} (left : Yields e state run first) (right : Yields e state run second) :
    first = second := by
  induction left generalizing second with
  | complete ended =>
    cases right with
    | complete => rfl
    | stop published _ => rw [ended] at published; cases published
    | next published _ _ => rw [ended] at published; cases published
  | stop published stops =>
    cases right with
    | complete ended => rw [ended] at published; cases published
    | stop published' stops' =>
      rw [published] at published'
      cases published'
      rw [stops] at stops'
      cases stops'
      rfl
    | next published' continues _ =>
      rw [published] at published'
      cases published'
      rw [stops] at continues
      cases continues
  | next published continues _ ih =>
    cases right with
    | complete ended => rw [ended] at published; cases published
    | stop published' stops' =>
      rw [published] at published'
      cases published'
      rw [continues] at stops'
      cases stops'
    | next published' continues' rest =>
      rw [published] at published'
      cases published'
      rw [continues] at continues'
      cases continues'
      exact ih rest

/-- On a completed trace an executor returns exactly its reading of the trace. -/
theorem yields_ofList_iff (e : Executor A State R) (state : State) (trace : Trace A) (result : R) :
    Yields e state (Stream'.Seq.ofList trace) result ↔ result = e.runFrom state trace := by
  induction trace generalizing state result with
  | nil =>
    constructor
    · intro yields
      cases yields with
      | complete => rfl
      | stop published _ => simp at published
      | next published _ _ => simp at published
    · rintro rfl
      exact .complete (by simp)
  | cons batch rest ih =>
    constructor
    · intro yields
      cases yields with
      | complete ended => simp at ended
      | stop published stops =>
        simp only [Stream'.Seq.ofList_cons, Stream'.Seq.head_cons, Option.some.injEq] at published
        subst published
        simp [runFrom, stops]
      | next published continues tail =>
        simp only [Stream'.Seq.ofList_cons, Stream'.Seq.head_cons, Option.some.injEq] at published
        subst published
        simp only [Stream'.Seq.ofList_cons, Stream'.Seq.tail_cons] at tail
        rw [runFrom_cons_inl continues]
        exact (ih _ _).mp tail
    · rintro rfl
      cases reading : e.read state batch with
      | inl next =>
        refine .next (by simp) reading ?_
        simp only [Stream'.Seq.ofList_cons, Stream'.Seq.tail_cons]
        rw [runFrom_cons_inl reading]
        exact (ih next _).mpr rfl
      | inr stopped =>
        rw [runFrom_cons_inr reading]
        exact .stop (by simp) reading

/-- An executor that stops within the first `n` batches of a run returns
that result, whether or not the run ever completes. -/
theorem yields_of_stopIn {e : Executor A State R} {state : State} {run : Run A} {n : ℕ}
    {result : R} (stops : e.stopIn state (run.take n) = some result) : Yields e state run result := by
  induction n generalizing state run with
  | zero => simp [stopIn] at stops
  | succ n ih =>
    cases published : Stream'.Seq.head run with
    | none =>
      rw [Stream'.Seq.head_eq_none published] at stops
      simp [Stream'.Seq.take_nil, stopIn] at stops
    | some batch =>
      have split := Stream'.Seq.head_eq_some published
      rw [split, Stream'.Seq.take_succ_cons] at stops
      cases reading : e.read state batch with
      | inl next =>
        simp only [stopIn, reading] at stops
        exact .next published reading (ih stops)
      | inr stopped =>
        simp only [stopIn, reading, Option.some.injEq] at stops
        exact stops ▸ .stop published reading

/-- Two runs that share a prefix on which the executor stops get the same
result, including runs that never complete. -/
theorem yields_of_shared_prefix {e : Executor A State R} {state : State} {run other : Run A}
    {n : ℕ} {result : R} (shared : run.take n = other.take n)
    (stops : e.stopIn state (run.take n) = some result) (answer : R) :
    Yields e state run answer ↔ Yields e state other answer := by
  have here := yields_of_stopIn stops
  have there := yields_of_stopIn (run := other) (shared ▸ stops)
  exact ⟨fun yields => yields.functional here ▸ there,
    fun yields => yields.functional there ▸ here⟩

/-- A result the executor never stops with is returned only on runs that complete. -/
theorem terminates_of_yields {e : Executor A State R} {state : State} {run : Run A}
    {result : R} (neverStops : ∀ state batch, e.read state batch ≠ .inr result)
    (yields : Yields e state run result) : run.Terminates := by
  induction yields with
  | complete ended => exact ⟨0, ended⟩
  | stop _ stops => exact (neverStops _ _ stops).elim
  | next _ _ _ ih =>
    obtain ⟨n, ended⟩ := ih neverStops
    exact ⟨n + 1, by simpa [Stream'.Seq.TerminatedAt] using ended⟩

/-- Every executor returns on every run that completes. -/
theorem yields_of_terminates (e : Executor A State R) (state : State) {run : Run A}
    (completed : run.Terminates) : ∃ result, Yields e state run result := by
  obtain ⟨n, ended⟩ := completed
  induction n generalizing state run with
  | zero => exact ⟨_, .complete ended⟩
  | succ n ih =>
    cases published : Stream'.Seq.head run with
    | none => exact ⟨_, .complete published⟩
    | some batch =>
      cases reading : e.read state batch with
      | inl next =>
        obtain ⟨result, rest⟩ := ih next (run := Stream'.Seq.tail run)
          (by simpa [Stream'.Seq.TerminatedAt] using ended)
        exact ⟨result, .next published reading rest⟩
      | inr stopped => exact ⟨stopped, .stop published reading⟩

/-- An executor that never stops early returns exactly on the runs that complete. -/
theorem yields_iff_terminates {e : Executor A State R}
    (neverStops : ∀ state batch, ∃ next, e.read state batch = .inl next)
    (state : State) (run : Run A) : (∃ result, Yields e state run result) ↔ run.Terminates := by
  refine ⟨fun ⟨result, yields⟩ => terminates_of_yields ?_ yields, yields_of_terminates e state⟩
  intro state batch stops
  obtain ⟨next, continues⟩ := neverStops state batch
  rw [continues] at stops
  cases stops

theorem yields_map {R' : Type} {e : Executor A State R} (f : R → R') {state : State} {run : Run A}
    {result : R} (yields : Yields e state run result) : Yields (e.map f) state run (f result) := by
  induction yields with
  | complete ended => exact .complete ended
  | stop published stops =>
    exact .stop published (by simp [Executor.map, stops])
  | next published continues _ ih =>
    exact .next published (by simp [Executor.map, continues]) ih

/-! ## The four executors -/

/-- Stops at the first answer and returns it; a trace without answers gives `none`. -/
def firstAnswer : Executor A Unit (Option A) where
  start := ()
  read _ batch := match batch with
    | [] => .inl ()
    | answer :: _ => .inr (some answer)
  finish _ := none

/-- Stops at the first answer with `true`; a trace without answers gives `false`. -/
def presence : Executor A Unit Bool where
  start := ()
  read _ batch := if batch.isEmpty then .inl () else .inr true
  finish _ := false

/-- Reads the completed trace, remembering only whether an answer appeared. -/
def absence : Executor A Bool Bool where
  start := false
  read seen batch := .inl (seen || !batch.isEmpty)
  finish seen := !seen

/-- Folds the batch sizes into a number, never building the list of answers. -/
def count : Executor A ℕ ℕ where
  start := 0
  read counted batch := .inl (counted + batch.length)
  finish counted := counted

theorem firstAnswer_run (trace : Trace A) : firstAnswer.run trace = observe .first trace := by
  change firstAnswer.runFrom () trace = trace.flatten.head?
  induction trace with
  | nil => rfl
  | cons batch rest ih =>
    cases batch with
    | nil => simpa [runFrom, firstAnswer] using ih
    | cons answer _ => simp [runFrom, firstAnswer]

theorem presence_run (trace : Trace A) : presence.run trace = observe .presence trace := by
  change presence.runFrom () trace = !trace.flatten.isEmpty
  induction trace with
  | nil => rfl
  | cons batch rest ih =>
    cases batch with
    | nil => simpa [runFrom, presence] using ih
    | cons answer _ => simp [runFrom, presence]

private theorem absence_runFrom (seen : Bool) (trace : Trace A) :
    absence.runFrom seen trace = (!seen && trace.flatten.isEmpty) := by
  induction trace generalizing seen with
  | nil => simp [runFrom, absence]
  | cons batch rest ih =>
    rw [runFrom_cons_inl (next := seen || !batch.isEmpty) rfl, ih]
    cases seen <;> cases batch <;> simp

theorem absence_run (trace : Trace A) : absence.run trace = observe .absence trace := by
  change absence.runFrom false trace = trace.flatten.isEmpty
  simp [absence_runFrom]

private theorem count_runFrom (counted : ℕ) (trace : Trace A) :
    count.runFrom counted trace = counted + trace.flatten.length := by
  induction trace generalizing counted with
  | nil => rfl
  | cons batch rest ih =>
    rw [runFrom_cons_inl (next := counted + batch.length) rfl, ih]
    simp [Nat.add_assoc]

theorem count_run (trace : Trace A) : count.run trace = observe .count trace := by
  change count.runFrom 0 trace = trace.flatten.length
  simp [count_runFrom]

/-- `first` stops on exactly the batches containing an answer. -/
theorem firstAnswer_stopIn (trace : Trace A) :
    firstAnswer.stopIn () trace = trace.flatten.head?.map some := by
  induction trace with
  | nil => rfl
  | cons batch rest ih =>
    cases batch with
    | nil => simpa [stopIn, firstAnswer] using ih
    | cons answer _ => simp [stopIn, firstAnswer]

/-- `presence` stops with `true` on every prefix containing an answer. -/
theorem presence_stopIn {trace : Trace A} (answered : trace.flatten ≠ []) :
    presence.stopIn () trace = some true := by
  induction trace with
  | nil => simp at answered
  | cons batch rest ih =>
    cases batch with
    | nil => simpa [stopIn, presence] using ih (by simpa using answered)
    | cons answer _ => simp [stopIn, presence]

/-- On a completed trace, `first` ignores everything after a prefix containing an answer. -/
theorem firstAnswer_run_append {pre : Trace A} (answered : pre.flatten ≠ []) (rest rest' : Trace A) :
    firstAnswer.run (pre ++ rest) = firstAnswer.run (pre ++ rest') := by
  obtain ⟨answer, others, split⟩ := List.exists_cons_of_ne_nil answered
  have stops : firstAnswer.stopIn () pre = some (some answer) := by
    simp [firstAnswer_stopIn, split]
  exact (runFrom_append_of_stopIn stops rest).trans (runFrom_append_of_stopIn stops rest').symm

/-- On a completed trace, `presence` ignores everything after a prefix containing an answer. -/
theorem presence_run_append {pre : Trace A} (answered : pre.flatten ≠ []) (rest rest' : Trace A) :
    presence.run (pre ++ rest) = presence.run (pre ++ rest') :=
  (runFrom_append_of_stopIn (presence_stopIn answered) rest).trans
    (runFrom_append_of_stopIn (presence_stopIn answered) rest').symm

/-- `first` reads only the prefix up to the first answer: two runs sharing a
prefix that contains an answer get the same result, which is that answer,
even when a run never completes. -/
theorem firstAnswer_reads_prefix {run other : Run A} {n : ℕ} (shared : run.take n = other.take n)
    (answered : (run.take n).flatten ≠ []) (answer : Option A) :
    Yields firstAnswer () run answer ↔ Yields firstAnswer () other answer := by
  obtain ⟨found, others, split⟩ := List.exists_cons_of_ne_nil answered
  exact yields_of_shared_prefix shared (result := some found) (by simp [firstAnswer_stopIn, split]) answer

theorem firstAnswer_yields_prefix {run : Run A} {n : ℕ} (answered : (run.take n).flatten ≠ []) :
    Yields firstAnswer () run (run.take n).flatten.head? := by
  obtain ⟨found, others, split⟩ := List.exists_cons_of_ne_nil answered
  have stops : firstAnswer.stopIn () (run.take n) = some (some found) := by
    simp [firstAnswer_stopIn, split]
  rw [split]
  exact yields_of_stopIn stops

/-- `presence` reads only the prefix up to the first answer. -/
theorem presence_reads_prefix {run other : Run A} {n : ℕ} (shared : run.take n = other.take n)
    (answered : (run.take n).flatten ≠ []) (answer : Bool) :
    Yields presence () run answer ↔ Yields presence () other answer :=
  yields_of_shared_prefix shared (presence_stopIn answered) answer

theorem presence_yields_prefix {run : Run A} {n : ℕ} (answered : (run.take n).flatten ≠ []) :
    Yields presence () run true :=
  yields_of_stopIn (presence_stopIn answered)

/-- A negative answer of `first` or `presence` needs a completed run. -/
theorem terminates_of_no_first {run : Run A} (yields : Yields firstAnswer () run none) :
    run.Terminates := by
  refine terminates_of_yields (fun _ batch stops => ?_) yields
  cases batch <;> simp [firstAnswer] at stops

theorem terminates_of_no_presence {run : Run A} (yields : Yields presence () run false) :
    run.Terminates := by
  refine terminates_of_yields (fun _ batch stops => ?_) yields
  by_cases empty : batch = [] <;> simp [presence, empty] at stops

/-- `absence` and `count` never stop early, so they return exactly on completed runs. -/
theorem absence_yields_iff (run : Run A) :
    (∃ answer, Yields absence false run answer) ↔ run.Terminates :=
  yields_iff_terminates (fun _ _ => ⟨_, rfl⟩) false run

theorem count_yields_iff (run : Run A) :
    (∃ answer, Yields count 0 run answer) ↔ run.Terminates :=
  yields_iff_terminates (fun _ _ => ⟨_, rfl⟩) 0 run

/-! ## Replacement licensed by an observation -/

/-- Two routes, each a set of completed traces, agree at a demand when they
report the same answers at it. -/
def AgreeAt (d : Demand) (first second : Trace A → Prop) : Prop :=
  ∀ answer, reports first d answer ↔ reports second d answer

/-- Replacement weakened to an observation: a fast route proved equal to a
slow one at `a` may serve every call site whose demand `b` is determined by `a`. -/
theorem licence {a b : Demand} (determined : Determines a b) {fast slow : Trace A → Prop}
    (proved : AgreeAt a fast slow) : AgreeAt b fast slow := by
  intro answer
  constructor
  · rintro ⟨trace, member, rfl⟩
    obtain ⟨other, otherMember, same⟩ := (proved (observe a trace)).mp ⟨trace, member, rfl⟩
    exact ⟨other, otherMember, determined other trace same⟩
  · rintro ⟨trace, member, rfl⟩
    obtain ⟨other, otherMember, same⟩ := (proved (observe a trace)).mpr ⟨trace, member, rfl⟩
    exact ⟨other, otherMember, determined other trace same⟩

/-- The licence is exact: agreement at `a` transfers to `b` for all routes
precisely for the demands that `a` covers. -/
theorem licence_iff (a b : Demand) :
    (∀ {T : Type} (fast slow : Trace T → Prop), AgreeAt a fast slow → AgreeAt b fast slow) ↔
      covers a b = true := by
  rw [← determines_iff]
  refine ⟨fun transfers => ?_, fun determined {_} _ _ => licence determined⟩
  intro T x y same
  have agree : AgreeAt a (fun trace => trace = x) (fun trace => trace = y) := by
    intro answer
    constructor
    · rintro ⟨_, rfl, rfl⟩
      exact ⟨y, rfl, same.symm⟩
    · rintro ⟨_, rfl, rfl⟩
      exact ⟨x, rfl, same⟩
  obtain ⟨_, rfl, observed⟩ :=
    (transfers (fun trace => trace = x) (fun trace => trace = y) agree (observe b x)).mp ⟨x, rfl, rfl⟩
  exact observed.symm

/-- `(== (collapse X) ())`: collect every answer, and at completion compare the
collection with the empty one. -/
def collectThenCompare : Executor A (List A) Bool where
  start := []
  read collected batch := .inl (collected ++ batch)
  finish collected := collected.isEmpty

private theorem collectThenCompare_runFrom (collected : List A) (trace : Trace A) :
    collectThenCompare.runFrom collected trace = (collected ++ trace.flatten).isEmpty := by
  induction trace generalizing collected with
  | nil => simp [runFrom, collectThenCompare]
  | cons batch rest ih =>
    rw [runFrom_cons_inl (next := collected ++ batch) rfl, ih]
    simp

/-- On a completed trace the comparison is the absence observation. -/
theorem collectThenCompare_run (trace : Trace A) :
    collectThenCompare.run trace = observe .absence trace := by
  change collectThenCompare.runFrom [] trace = trace.flatten.isEmpty
  simp [collectThenCompare_runFrom]

/-- On completed traces the comparison is served by a route proved equal at
any demand, since every demand determines absence. -/
theorem collectThenCompare_licensed {a : Demand} {fast slow : Trace A → Prop}
    (proved : AgreeAt a fast slow) (answer : Bool) :
    (∃ trace, fast trace ∧ collectThenCompare.run trace = answer) ↔
      ∃ trace, slow trace ∧ collectThenCompare.run trace = answer := by
  simp only [collectThenCompare_run]
  exact licence ((determines_iff a .absence).mpr (by cases a <;> rfl)) proved answer

/-- The comparison returns exactly on the runs that complete. -/
theorem collectThenCompare_yields_iff (run : Run A) :
    (∃ answer, Yields collectThenCompare [] run answer) ↔ run.Terminates :=
  yields_iff_terminates (fun _ _ => ⟨_, rfl⟩) [] run

/-- With completion, answering the comparison by presence is exact. -/
theorem presence_serves_comparison {run : Run A} (completed : run.Terminates) (answer : Bool) :
    Yields collectThenCompare [] run answer ↔ Yields (presence.map not) () run answer := by
  rw [← Stream'.Seq.ofList_toList run completed, yields_ofList_iff, yields_ofList_iff, map_runFrom]
  have collected : collectThenCompare.runFrom [] (Stream'.Seq.toList run completed) =
      observe .absence (Stream'.Seq.toList run completed) :=
    collectThenCompare_run _
  have present : presence.runFrom () (Stream'.Seq.toList run completed) =
      observe .presence (Stream'.Seq.toList run completed) :=
    presence_run _
  rw [collected, present]
  simp [observe]

/-- A run with a batch at every tick never completes. -/
theorem ofStream_never_completes (batches : Stream' (List A)) :
    ¬(Stream'.Seq.ofStream batches).Terminates := by
  rintro ⟨n, ended⟩
  change some (batches n) = none at ended
  cases ended

/-- One answer, then silence at every later tick: a run that never completes. -/
def answerThenSilence : Run Bool :=
  Stream'.Seq.cons [true] (Stream'.Seq.ofStream fun _ => [])

/-- Completion cannot be dropped: on a run that publishes an answer and never
completes, the comparison returns nothing, while presence answers. -/
theorem completion_needed :
    ¬answerThenSilence.Terminates ∧
      (∀ answer, ¬Yields collectThenCompare [] answerThenSilence answer) ∧
      Yields presence () answerThenSilence true ∧
      Yields (presence.map not) () answerThenSilence false := by
  have silent : ¬answerThenSilence.Terminates := fun completed =>
    ofStream_never_completes _ (Stream'.Seq.terminates_cons_iff.mp completed)
  have answered : Yields presence () answerThenSilence true :=
    .stop (batch := [true]) (by simp [answerThenSilence]) (by simp [presence])
  refine ⟨silent, fun answer yields => silent ?_, answered, yields_map not answered⟩
  exact (collectThenCompare_yields_iff _).mp ⟨answer, yields⟩

/-! ## Effects -/

variable {S : Type}

/-- One evaluation of a producer: the batch of answers it publishes and its
effect on the store, for example a list of store changes. -/
structure Evaluation (A S : Type) where
  answers : List A
  effect : S → S

/-- The trace an effectful producer publishes. -/
def published (producer : List (Evaluation A S)) : Trace A := producer.map Evaluation.answers

/-- The store after performing evaluations in order. -/
def perform (evaluations : List (Evaluation A S)) (store : S) : S :=
  evaluations.foldl (fun store evaluation => evaluation.effect store) store

theorem perform_append (first second : List (Evaluation A S)) (store : S) :
    perform (first ++ second) store = perform second (perform first store) := by
  simp [perform, List.foldl_append]

/-- On an effectful producer an executor evaluates a batch, performing its
effect, only when it reads that batch; the evaluations after it stops are
skipped. -/
def Executor.runWith (e : Executor A State R) : State → List (Evaluation A S) → S → R × S
  | state, [], store => (e.finish state, store)
  | state, evaluation :: rest, store =>
    match e.read state evaluation.answers with
    | .inl next => e.runWith next rest (evaluation.effect store)
    | .inr result => (result, evaluation.effect store)

/-- The evaluations an executor performs: up to the batch on which it stops. -/
def Executor.performed (e : Executor A State R) (producer : List (Evaluation A S)) :
    List (Evaluation A S) :=
  producer.take (e.readsFrom e.start (published producer))

/-- The evaluations an executor skips. -/
def Executor.skipped (e : Executor A State R) (producer : List (Evaluation A S)) :
    List (Evaluation A S) :=
  producer.drop (e.readsFrom e.start (published producer))

/-- The result is the reading of the published trace; the store has the
effects of exactly the evaluations read. -/
theorem runWith_eq (e : Executor A State R) (state : State) (producer : List (Evaluation A S))
    (store : S) :
    e.runWith state producer store =
      (e.runFrom state (published producer),
        perform (producer.take (e.readsFrom state (published producer))) store) := by
  induction producer generalizing state store with
  | nil => rfl
  | cons evaluation rest ih =>
    cases reading : e.read state evaluation.answers with
    | inl next =>
      simp only [runWith, published, List.map_cons, runFrom, readsFrom, reading,
        List.take_succ_cons]
      rw [ih]
      rfl
    | inr stopped =>
      simp [runWith, published, runFrom, readsFrom, reading, perform]

/-- With the store included, an executor correct for an observation is exact
exactly when the evaluations it skips leave the store it reached unchanged. -/
theorem exact_with_store_iff {e : Executor A State R} {observation : Trace A → R}
    (correct : ∀ trace, e.run trace = observation trace) (producer : List (Evaluation A S))
    (store : S) :
    e.runWith e.start producer store = (observation (published producer), perform producer store) ↔
      perform (e.skipped producer) (perform (e.performed producer) store) =
        perform (e.performed producer) store := by
  have whole : perform producer store =
      perform (e.skipped producer) (perform (e.performed producer) store) := by
    rw [← perform_append, performed, skipped, List.take_append_drop]
  rw [runWith_eq, ← correct, whole]
  change (e.run (published producer), perform (e.performed producer) store) = _ ↔ _
  simp only [Prod.mk.injEq, true_and]
  exact eq_comm

private theorem silent_published {pre : List (Evaluation A S)} (silent : ∀ e ∈ pre, e.answers = []) :
    ∀ batch ∈ published pre, batch = [] := by
  intro batch member
  obtain ⟨evaluation, inPre, rfl⟩ := List.mem_map.mp member
  exact silent evaluation inPre

/-- `first` reads exactly the batches up to and including the first answer. -/
theorem firstAnswer_readsFrom {pre rest : Trace A} {batch : List A}
    (silent : ∀ b ∈ pre, b = []) (answers : batch ≠ []) :
    firstAnswer.readsFrom () (pre ++ batch :: rest) = pre.length + 1 := by
  induction pre with
  | nil =>
    obtain ⟨answer, others, rfl⟩ := List.exists_cons_of_ne_nil answers
    rfl
  | cons empty pre ih =>
    rw [silent empty (by simp), List.cons_append, readsFrom_cons_inl (next := ()) rfl,
      ih (fun b member => silent b (by simp [member])), List.length_cons]

/-- `presence` reads exactly the batches up to and including the first answer. -/
theorem presence_readsFrom {pre rest : Trace A} {batch : List A}
    (silent : ∀ b ∈ pre, b = []) (answers : batch ≠ []) :
    presence.readsFrom () (pre ++ batch :: rest) = pre.length + 1 := by
  induction pre with
  | nil => simp [readsFrom, presence, answers]
  | cons empty pre ih =>
    rw [silent empty (by simp), List.cons_append, readsFrom_cons_inl (next := ()) rfl,
      ih (fun b member => silent b (by simp [member])), List.length_cons]

/-- `first` performs the evaluations up to the first answer and skips the rest. -/
theorem firstAnswer_skips {pre post : List (Evaluation A S)} {answered : Evaluation A S}
    (silent : ∀ e ∈ pre, e.answers = []) (answers : answered.answers ≠ []) :
    firstAnswer.performed (pre ++ answered :: post) = pre ++ [answered] ∧
      firstAnswer.skipped (pre ++ answered :: post) = post := by
  have reads : firstAnswer.readsFrom () (published (pre ++ answered :: post)) = pre.length + 1 := by
    simpa [published] using firstAnswer_readsFrom (rest := published post) (silent_published silent) answers
  refine ⟨?_, ?_⟩
  · change (pre ++ answered :: post).take (firstAnswer.readsFrom () _) = _
    rw [reads, List.take_length_add_append]
    rfl
  · change (pre ++ answered :: post).drop (firstAnswer.readsFrom () _) = _
    rw [reads, List.drop_length_add_append]
    rfl

theorem presence_skips {pre post : List (Evaluation A S)} {answered : Evaluation A S}
    (silent : ∀ e ∈ pre, e.answers = []) (answers : answered.answers ≠ []) :
    presence.performed (pre ++ answered :: post) = pre ++ [answered] ∧
      presence.skipped (pre ++ answered :: post) = post := by
  have reads : presence.readsFrom () (published (pre ++ answered :: post)) = pre.length + 1 := by
    simpa [published] using presence_readsFrom (rest := published post) (silent_published silent) answers
  refine ⟨?_, ?_⟩
  · change (pre ++ answered :: post).take (presence.readsFrom () _) = _
    rw [reads, List.take_length_add_append]
    rfl
  · change (pre ++ answered :: post).drop (presence.readsFrom () _) = _
    rw [reads, List.drop_length_add_append]
    rfl

/-- Skipping the evaluations after the first answer is exact for `first`
together with the store exactly when those evaluations leave the reached
store unchanged. -/
theorem firstAnswer_exact_iff {pre post : List (Evaluation A S)} {answered : Evaluation A S}
    (silent : ∀ e ∈ pre, e.answers = []) (answers : answered.answers ≠ []) (store : S) :
    firstAnswer.runWith () (pre ++ answered :: post) store =
        (observe .first (published (pre ++ answered :: post)), perform (pre ++ answered :: post) store) ↔
      perform post (perform (pre ++ [answered]) store) = perform (pre ++ [answered]) store := by
  have exact := exact_with_store_iff (e := firstAnswer) firstAnswer_run (pre ++ answered :: post) store
  rwa [(firstAnswer_skips silent answers).1, (firstAnswer_skips silent answers).2] at exact

theorem presence_exact_iff {pre post : List (Evaluation A S)} {answered : Evaluation A S}
    (silent : ∀ e ∈ pre, e.answers = []) (answers : answered.answers ≠ []) (store : S) :
    presence.runWith () (pre ++ answered :: post) store =
        (observe .presence (published (pre ++ answered :: post)), perform (pre ++ answered :: post) store) ↔
      perform post (perform (pre ++ [answered]) store) = perform (pre ++ [answered]) store := by
  have exact := exact_with_store_iff (e := presence) presence_run (pre ++ answered :: post) store
  rwa [(presence_skips silent answers).1, (presence_skips silent answers).2] at exact

theorem perform_of_effectless {evaluations : List (Evaluation A S)}
    (effectless : ∀ e ∈ evaluations, e.effect = id) (store : S) : perform evaluations store = store := by
  induction evaluations generalizing store with
  | nil => rfl
  | cons evaluation rest ih =>
    simp only [perform, List.foldl_cons]
    rw [effectless evaluation (by simp)]
    exact ih (fun e member => effectless e (by simp [member])) store

/-- When the evaluations after the first answer have no effect, stopping there is exact. -/
theorem firstAnswer_exact {pre post : List (Evaluation A S)} {answered : Evaluation A S}
    (silent : ∀ e ∈ pre, e.answers = []) (answers : answered.answers ≠ [])
    (unchanged : ∀ e ∈ post, e.effect = id) (store : S) :
    firstAnswer.runWith () (pre ++ answered :: post) store =
      (observe .first (published (pre ++ answered :: post)), perform (pre ++ answered :: post) store) :=
  (firstAnswer_exact_iff silent answers store).mpr (perform_of_effectless unchanged _)

theorem presence_exact {pre post : List (Evaluation A S)} {answered : Evaluation A S}
    (silent : ∀ e ∈ pre, e.answers = []) (answers : answered.answers ≠ [])
    (unchanged : ∀ e ∈ post, e.effect = id) (store : S) :
    presence.runWith () (pre ++ answered :: post) store =
      (observe .presence (published (pre ++ answered :: post)), perform (pre ++ answered :: post) store) :=
  (presence_exact_iff silent answers store).mpr (perform_of_effectless unchanged _)

/-- The first evaluation answers with no effect; the second answers and adds an atom. -/
def secondAddsAtom : List (Evaluation String (Multiset String)) :=
  [⟨["first"], id⟩, ⟨["second"], fun store => "added" ::ₘ store⟩]

/-- Negative control: stopping at the first answer returns the right answer
but leaves a store without the atom the second evaluation adds. -/
theorem stopping_early_changes_store :
    (firstAnswer.runWith () secondAddsAtom 0).1 = observe .first (published secondAddsAtom) ∧
      (firstAnswer.runWith () secondAddsAtom 0).2 = 0 ∧
      perform secondAddsAtom 0 = {"added"} ∧
      firstAnswer.runWith () secondAddsAtom 0 ≠
        (observe .first (published secondAddsAtom), perform secondAddsAtom 0) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro same
  have stores := congrArg Prod.snd same
  change (0 : Multiset String) = {"added"} at stores
  exact Multiset.singleton_ne_zero "added" stores.symm

/-- Without effects, every executor returns its reading and leaves the store unchanged. -/
theorem runWith_of_effectless (e : Executor A State R) (state : State)
    {producer : List (Evaluation A S)} (effectless : ∀ ev ∈ producer, ev.effect = id) (store : S) :
    e.runWith state producer store = (e.runFrom state (published producer), store) := by
  rw [runWith_eq, perform_of_effectless (fun ev member => effectless ev (List.mem_of_mem_take member))]

/-- Evaluating a template that is data at each solution of a query: a single
value, with no effect. -/
def dataTemplate {M : Type} (template : M → A) (solutions : List M) : List (Evaluation A S) :=
  solutions.map fun found => ⟨[template found], id⟩

/-- For templates that are data every executor, early-stopping or not, is
exact for its observation together with the store. -/
theorem dataTemplate_exact {M : Type} {e : Executor A State R} {observation : Trace A → R}
    (correct : ∀ trace, e.run trace = observation trace) (template : M → A) (solutions : List M)
    (store : S) :
    e.runWith e.start (dataTemplate template solutions) store =
      (observation (published (dataTemplate (S := S) template solutions)),
        perform (dataTemplate template solutions) store) := by
  have effectless : ∀ ev ∈ (dataTemplate template solutions : List (Evaluation A S)), ev.effect = id := by
    intro ev member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    rfl
  rw [runWith_of_effectless e e.start effectless, perform_of_effectless effectless]
  exact congrArg (·, store) (correct _)

/-! ## Inhabited instances -/

section Instances

private def sharedThenComplete : Run Bool := Stream'.Seq.ofList [[], [true], [false]]
private def sharedThenSilent : Run Bool :=
  Stream'.Seq.cons [] (Stream'.Seq.cons [true] (Stream'.Seq.ofStream fun _ => []))

/-- A run that completes and one that never does share the prefix up to the
first answer; `first` and `presence` answer the same on both. -/
example : Yields firstAnswer () sharedThenSilent (some true) ∧
    Yields presence () sharedThenSilent true ∧ ¬sharedThenSilent.Terminates := by
  have shared : sharedThenComplete.take 2 = sharedThenSilent.take 2 := rfl
  have answered : (sharedThenComplete.take 2).flatten ≠ [] := by decide
  refine ⟨(firstAnswer_reads_prefix shared answered _).mp
      (firstAnswer_yields_prefix (n := 2) answered),
    (presence_reads_prefix shared answered _).mp (presence_yields_prefix answered), ?_⟩
  intro completed
  exact ofStream_never_completes _
    (Stream'.Seq.terminates_cons_iff.mp (Stream'.Seq.terminates_cons_iff.mp completed))

example : firstAnswer.run [[], [true]] = some true ∧ presence.run [[], [true]] = true ∧
    absence.run ([[], []] : Trace Bool) = true ∧ count.run [[true], [false, true]] = 3 :=
  ⟨by rw [firstAnswer_run]; rfl, by rw [presence_run]; rfl, by rw [absence_run]; rfl,
    by rw [count_run]; rfl⟩

example : firstAnswer.run ([[true]] ++ [[false]]) = firstAnswer.run ([[true]] ++ []) :=
  firstAnswer_run_append (by decide) _ _

example : presence.run ([[true]] ++ [[false]]) = presence.run ([[true]] ++ []) :=
  presence_run_append (by decide) _ _

example : Stream'.Seq.Terminates (Stream'.Seq.ofList ([[], []] : Trace Bool)) ∧
    Yields firstAnswer () (Stream'.Seq.ofList ([[], []] : Trace Bool)) none :=
  ⟨Stream'.Seq.terminates_ofList _, (yields_ofList_iff _ _ _ _).mpr rfl⟩

example : (Stream'.Seq.ofList ([[], []] : Trace Bool)).Terminates :=
  terminates_of_no_first ((yields_ofList_iff _ _ _ _).mpr rfl)

example : (Stream'.Seq.ofList ([[], []] : Trace Bool)).Terminates :=
  terminates_of_no_presence ((yields_ofList_iff _ _ _ _).mpr rfl)

/-- On the run that answers and then never completes, `absence` and `count`
return nothing, while `first` returns the answer. -/
example : (∀ answer, ¬Yields absence false answerThenSilence answer) ∧
    (∀ answer, ¬Yields count 0 answerThenSilence answer) ∧
    Yields firstAnswer () answerThenSilence (some true) :=
  ⟨fun answer yields => completion_needed.1 ((absence_yields_iff _).mp ⟨answer, yields⟩),
    fun answer yields => completion_needed.1 ((count_yields_iff _).mp ⟨answer, yields⟩),
    .stop (batch := [true]) (by simp [answerThenSilence]) rfl⟩

example : firstAnswer.readsFrom () [[], [], [true], [false]] = 3 ∧
    presence.readsFrom () [[], [true, false], []] = 2 :=
  ⟨firstAnswer_readsFrom (pre := [[], []]) (by simp) (by simp),
    presence_readsFrom (pre := [[]]) (by simp) (by simp)⟩

example : Yields absence false (Stream'.Seq.ofList ([[], []] : Trace Bool)) true ∧
    Yields count 0 (Stream'.Seq.ofList ([[true], [false]] : Trace Bool)) 2 :=
  ⟨(yields_ofList_iff _ _ _ _).mpr rfl, (yields_ofList_iff _ _ _ _).mpr rfl⟩

/-- Two routes that agree at presence but not at count: the licence carries
the agreement to absence and to the comparison with the empty collection. -/
private def oneAnswer : Trace Bool → Prop := fun trace => trace = [[true]]
private def twoAnswers : Trace Bool → Prop := fun trace => trace = [[], [true, true]]

private theorem agree_at_presence : AgreeAt .presence oneAnswer twoAnswers := by
  intro answer
  constructor
  · rintro ⟨_, rfl, rfl⟩
    exact ⟨[[], [true, true]], rfl, rfl⟩
  · rintro ⟨_, rfl, rfl⟩
    exact ⟨[[true]], rfl, rfl⟩

example : AgreeAt .absence oneAnswer twoAnswers ∧ ¬AgreeAt .count oneAnswer twoAnswers := by
  refine ⟨licence ((determines_iff _ _).mpr rfl) agree_at_presence, fun agree => ?_⟩
  obtain ⟨_, rfl, wrong⟩ := (agree (1 : ℕ)).mp ⟨[[true]], rfl, rfl⟩
  cases wrong

example (answer : Bool) :
    (∃ trace, oneAnswer trace ∧ collectThenCompare.run trace = answer) ↔
      ∃ trace, twoAnswers trace ∧ collectThenCompare.run trace = answer :=
  collectThenCompare_licensed agree_at_presence answer

example : ¬(∀ {T : Type} (fast slow : Trace T → Prop),
    AgreeAt .presence fast slow → AgreeAt .count fast slow) :=
  fun transfers => absurd ((licence_iff _ _).mp transfers) (by decide)

example (answer : Bool) :
    Yields collectThenCompare [] (Stream'.Seq.ofList [[], [true]]) answer ↔
      Yields (presence.map not) () (Stream'.Seq.ofList [[], [true]]) answer :=
  presence_serves_comparison (Stream'.Seq.terminates_ofList _) answer

private def effectFree : List (Evaluation String (Multiset String)) :=
  [⟨[], fun store => "before" ::ₘ store⟩, ⟨["first"], id⟩, ⟨["second"], id⟩]

/-- The positive statement: the evaluation before the answer still has its
effect, and the skipped evaluation has none. -/
example : firstAnswer.runWith () effectFree 0 =
      (observe .first (published effectFree), perform effectFree 0) ∧
    presence.runWith () effectFree 0 =
      (observe .presence (published effectFree), perform effectFree 0) := by
  have silent : ∀ e ∈ [(⟨[], fun store => "before" ::ₘ store⟩ : Evaluation String (Multiset String))],
      e.answers = [] := by simp
  have answers : (⟨["first"], id⟩ : Evaluation String (Multiset String)).answers ≠ [] := by simp
  have unchanged : ∀ e ∈ [(⟨["second"], id⟩ : Evaluation String (Multiset String))],
      e.effect = id := by simp
  exact ⟨firstAnswer_exact silent answers unchanged 0, presence_exact silent answers unchanged 0⟩

example : ¬(perform [(⟨["second"], fun store => "added" ::ₘ store⟩ : Evaluation String (Multiset String))]
      (perform [(⟨["first"], id⟩ : Evaluation String (Multiset String))] 0) =
    perform [(⟨["first"], id⟩ : Evaluation String (Multiset String))] 0) := by
  intro same
  change ("added" ::ₘ 0 : Multiset String) = 0 at same
  exact Multiset.cons_ne_zero same

example (store : Multiset String) :
    count.runWith 0 (dataTemplate (S := Multiset String) (fun n : ℕ => n) [1, 2, 3]) store =
      (observe .count (published (dataTemplate (S := Multiset String) (fun n : ℕ => n) [1, 2, 3])),
        perform (dataTemplate (S := Multiset String) (fun n : ℕ => n) [1, 2, 3]) store) :=
  dataTemplate_exact count_run _ _ store

example (store : Multiset String) :
    firstAnswer.runWith () (dataTemplate (S := Multiset String) (fun n : ℕ => n) [1, 2]) store =
      (some 1, store) := by
  rw [show () = (firstAnswer (A := ℕ)).start from rfl, dataTemplate_exact firstAnswer_run,
    perform_of_effectless (by simp [dataTemplate])]
  rfl

end Instances

end Mettapedia.GSLT.Contracts.ObservationExecutors

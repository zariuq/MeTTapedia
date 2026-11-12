import Mettapedia.Languages.MeTTa.PeTTa.LibTransform
import Mettapedia.Machines.ScopedCommitCursor

/-!
# The authored transform trace under bounded cursor demand

The independent library model's trace records each answer, its reached store
and the actual residual search. Its source selector below stops at an answer
quota, including the store changes encountered before the next answer. The
target executes the existing bounded cursor and reversed answer accumulator.

The connection preserves and reflects answers, the reached store and the
residual as a function of the consumer's next store. It is therefore stronger
than comparing completed answer bags. One cursor pull can still perform the
work needed to find an answer; this is not a bound on internal matching fuel.

The library model's declared scope remains: finite first-order matching,
one source store and its defined routes. Named spaces, evaluated let conjuncts,
arbitrary PeTTa unification, errors and native execution require their own
source interpretations; this adapter does not supply them implicitly.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaTransformDemand

open Mettapedia.Machines
open Mettapedia.Languages.MeTTa.PeTTa (Answers)
open Mettapedia.Languages.MeTTa.PeTTa.LibTransform
open Mettapedia.GSLT.LanguageDef.NativeControlBoundedCursor (readout)
open Mettapedia.GSLT.LanguageDef

variable {S A : Type}

def encode : Trace S A → ScopedCommit.Answers A S
  | .done store => .stop store
  | .answer value store later => .more value store (fun next => encode (later next))

def decode : ScopedCommit.Answers A S → Trace S A
  | .stop store => .done store
  | .more value store later => .answer value store (fun next => decode (later next))

theorem decode_encode (trace : Trace S A) : decode (encode trace) = trace := by
  induction trace with
  | done store => rfl
  | answer value store later ih =>
      simp only [encode, decode]
      congr 1
      funext next
      exact ih next

theorem encode_decode (trace : ScopedCommit.Answers A S) : encode (decode trace) = trace := by
  induction trace with
  | stop store => rfl
  | more value store later ih =>
      simp only [encode, decode]
      congr 1
      funext next
      exact ih next

theorem observe_encode (trace : Trace S A) : (encode trace).observe = trace.drain := by
  induction trace with
  | done store => rfl
  | answer value store later ih => simp [encode, ScopedCommit.Answers.observe, ih]

def search (source : Search S A) : S → ScopedCommit.Answers A S := fun store => encode (source store)

/-- Independent source demand: one answer may follow several answerless
firings. No residual is entered once the answer quota is reached. -/
def select : Nat → Search S A → S → List A × S × Search S A
  | 0, source, store => ([], store, source)
  | amount + 1, source, store =>
      match source store with
      | .done final => ([], final, Trace.done)
      | .answer value here residual =>
          let later := select amount residual here
          (value :: later.1, later.2.1, later.2.2)

def encodedSelection (selected : List A × S × Search S A) :
    List A × S × (S → ScopedCommit.Answers A S) :=
  (selected.1, selected.2.1, search selected.2.2)

theorem selection_exact (demand : Nat) (source : Search S A) (store : S) :
    ScopedCommit.selectFrom demand (search source) store = encodedSelection (select demand source store) := by
  induction demand generalizing source store with
  | zero => rfl
  | succ demand ih =>
      cases produced : source store with
      | done final =>
          simp only [ScopedCommit.selectFrom, search, encode, produced, select, encodedSelection]
          rfl
      | answer value here residual =>
          simp only [ScopedCommit.selectFrom, search, encode, produced, select, encodedSelection]
          change (value :: (ScopedCommit.selectFrom demand (search residual) here).1,
            (ScopedCommit.selectFrom demand (search residual) here).2) =
              (value :: (select demand residual here).1,
                (select demand residual here).2.1, search (select demand residual here).2.2)
          rw [ih]
          rfl

theorem execute_exact (demand : Nat) (source : Search S A) (store : S) :
    ScopedCommitCursor.sourceView
      (readout ScopedCommitCursor.pull (ScopedCommitCursor.execute demand (search source) store).2) =
        encodedSelection (select demand source store) := by
  rw [ScopedCommitCursor.execution_selection, selection_exact]

/-- Reflect target claims back into the independently selected source trace.
The residual can be observed in every later consumer-supplied store. -/
theorem execute_iff (demand : Nat) (source : Search S A) (store : S)
    (answers : List A) (here : S) (later : Search S A) :
    ScopedCommitCursor.sourceView
      (readout ScopedCommitCursor.pull (ScopedCommitCursor.execute demand (search source) store).2) =
        encodedSelection (answers, here, later) ↔ select demand source store = (answers, here, later) := by
  rw [execute_exact]
  constructor
  · intro same
    have first := congrArg (fun result => result.1) same
    have world := congrArg (fun result => result.2.1) same
    have tail := congrArg (fun result => result.2.2) same
    have residual : (select demand source store).2.2 = later := by
      funext next
      have encoded := congrFun tail next
      exact (decode_encode ((select demand source store).2.2 next)).symm.trans
        ((congrArg decode encoded).trans (decode_encode (later next)))
    exact Prod.ext first (Prod.ext world residual)
  · intro same
    exact congrArg encodedSelection same

theorem zero_demand (source : Search S A) (store : S) : select 0 source store = ([], store, source) := rfl

theorem first_is_once (source : Search S A) (store : S) :
    ((select 1 source store).1, (select 1 source store).2.1) = (Search.once source store).drain := by
  cases produced : source store <;> simp [select, Search.once, produced, Trace.drain]

theorem resumed_drain (demand : Nat) (source : Search S A) (store : S) :
    let earlier := select demand source store
    (earlier.1 ++ (earlier.2.2 earlier.2.1).drain.1, (earlier.2.2 earlier.2.1).drain.2) =
      (source store).drain := by
  have same := ScopedCommit.selectFrom_resume demand (search source) store
  rw [selection_exact] at same
  simpa only [encodedSelection, ScopedCommit.resume, search, observe_encode] using same

theorem selection_add (first second : Nat) (source : Search S A) (store : S) :
    select (first + second) source store =
      let earlier := select first source store
      let later := select second earlier.2.2 earlier.2.1
      (earlier.1 ++ later.1, later.2.1, later.2.2) := by
  induction first generalizing source store with
  | zero => simp [select]
  | succ first ih =>
      cases produced : source store with
      | done final => cases second <;> simp [select, produced]
      | answer value here residual => simp [Nat.succ_add, select, produced, ih]

/-- The actual consumer's first-answer observation agrees with the source
once, including effects of branches that produce no answer. -/
theorem execute_once (source : Search S A) (store : S) :
    let observed := readout ScopedCommitCursor.pull
      (ScopedCommitCursor.execute 1 (search source) store).2
    (observed.answers, observed.world) = (Search.once source store).drain := by
  have same := congrArg (fun selected => (selected.1, selected.2.1)) (execute_exact 1 source store)
  exact same.trans (first_is_once source store)

/-- The reference collector independently separates scheduler budget from
answer allowance. A pull either yields one answer or observes exhaustion. -/
theorem collector_budget_exact (budget allowance : Nat) (source : Search S A) (store : S) :
    ScopedCommitCursor.sourceView
      (NativeControlBoundedCursor.collectBounded ScopedCommitCursor.pull budget allowance
        (search source) store).2 =
      encodedSelection (select (min budget allowance) source store) := by
  induction budget generalizing allowance source store with
  | zero => cases allowance <;> rfl
  | succ budget ih =>
      cases allowance with
      | zero => rfl
      | succ allowance =>
          cases produced : source store with
          | done final =>
              simp only [NativeControlBoundedCursor.collectBounded, ScopedCommitCursor.pull, search,
                produced, encode, ScopedCommitCursor.sourceView, Nat.succ_min_succ, select,
                encodedSelection]
              rfl
          | answer value here residual =>
              simp only [NativeControlBoundedCursor.collectBounded, ScopedCommitCursor.pull, search,
                produced, encode, ScopedCommitCursor.sourceView_prefix, Nat.succ_min_succ, select,
                encodedSelection]
              change (value :: (ScopedCommitCursor.sourceView
                (NativeControlBoundedCursor.collectBounded ScopedCommitCursor.pull budget allowance
                  (search residual) here).2).1,
                (ScopedCommitCursor.sourceView
                  (NativeControlBoundedCursor.collectBounded ScopedCommitCursor.pull budget allowance
                    (search residual) here).2).2) = _
              rw [ih]
              rfl

def budgeted (budget allowance : Nat) (source : Search S A) (store : S) :=
  Cursor.advance (NativeControlEffectCursor.provider ScopedCommitCursor.pull)
    (NativeControlBoundedCursor.client A) (fun _ _ => 1) budget
    (NativeControlBoundedCursor.packet ScopedCommitCursor.pull allowance (search source) store [])

theorem budgeted_exact (budget allowance : Nat) (source : Search S A) (store : S) :
    ScopedCommitCursor.sourceView (readout ScopedCommitCursor.pull (budgeted budget allowance source store).2) =
      encodedSelection (select (min budget allowance) source store) := by
  have actual := NativeControlBoundedCursor.readout_exact ScopedCommitCursor.pull budget allowance
    (search source) store []
  have view := congrArg (fun result => ScopedCommitCursor.sourceView result.2) actual
  simpa [budgeted, NativeControlBoundedCursor.Snapshot.prefix] using
    view.trans (collector_budget_exact budget allowance source store)

/-- Actual cursor resumption keeps the remaining allowance and accumulated
poll account, rather than opening a new transform or regenerating proposals. -/
theorem budgeted_split (first second allowance : Nat) (source : Search S A) (store : S) :
    budgeted (first + second) allowance source store =
      Cursor.resume (NativeControlEffectCursor.provider ScopedCommitCursor.pull)
        (NativeControlBoundedCursor.client A) (fun _ _ => 1) second
        (budgeted first allowance source store) :=
  Cursor.advance_add _ _ _ first second _

theorem residual_at_any_store (demand : Nat) (source : Search S A) (store nextStore : S) :
    let snapshot := readout ScopedCommitCursor.pull
      (ScopedCommitCursor.execute demand (search source) store).2
    ScopedCommit.resume (ScopedCommitCursor.sourceView snapshot).2.2 nextStore =
      ((select demand source store).2.2 nextStore).drain := by
  have residual := congrArg (fun selected => selected.2.2) (execute_exact demand source store)
  have atNext := congrFun residual nextStore
  exact (congrArg ScopedCommit.Answers.observe atNext).trans
    (observe_encode ((select demand source store).2.2 nextStore))

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

def transformCursor {B : Type} (route : Answers → Search Store B) (sources : Sources)
    (emit : Subst → Answers) (demand : Nat) (store : Store) :=
  readout ScopedCommitCursor.pull
    (ScopedCommitCursor.execute demand (search (transformWith route sources emit)) store).2

theorem transform_prefix (route : Answers → Search Store A) (sources : Sources)
    (emit : Subst → Answers) (demand : Nat) (store : Store) :
    ScopedCommitCursor.sourceView (transformCursor route sources emit demand store) =
      encodedSelection (select demand (transformWith route sources emit) store) :=
  execute_exact demand (transformWith route sources emit) store

theorem transform_once (route : Answers → Search Store A) (sources : Sources)
    (emit : Subst → Answers) (store : Store) :
    ((transformCursor route sources emit 1 store).answers,
      (transformCursor route sources emit 1 store).world) =
      (Search.once (transformWith route sources emit) store).drain :=
  execute_once (transformWith route sources emit) store

theorem transform_resume_drain (route : Answers → Search Store A) (sources : Sources)
    (emit : Subst → Answers) (demand : Nat) (store : Store) :
    let selected := ScopedCommitCursor.sourceView (transformCursor route sources emit demand store)
    (selected.1 ++ (ScopedCommit.resume selected.2.2 selected.2.1).1,
      (ScopedCommit.resume selected.2.2 selected.2.1).2) =
      (proposals store sources).foldl (branchStep route sources emit) ([], store) := by
  rw [transform_prefix]
  simp only [encodedSelection, ScopedCommit.resume, search, observe_encode]
  rw [resumed_drain, transformWith_drain]

namespace Controls

def source : Sources := ⟨[.pat .take (.var "x")], [], none⟩
def emit (bindings : Subst) : Answers := [Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings (.var "x")]
def start : Store := [.symbol "a", .symbol "b", .symbol "c"]

/-- A successfully consumed a is intentionally answerless. Outer first
demand must continue from its changed store, rather than undoing or replaying it. -/
def route (out : Answers) : Search Store Atom :=
  if out = [.symbol "a"] then Trace.done else toCaller out

def job := transformWith route source emit
def one := transformCursor route source emit 1 start
def zero := transformCursor route source emit 0 start
def firstSource := select 1 job start

theorem zero_does_not_start_candidate_work :
    zero.answers = [] ∧ zero.world = start := by decide +kernel

theorem source_first_passes_an_answerless_firing :
    firstSource.1 = [.symbol "b"] ∧ firstSource.2.1 = [.symbol "c"] := by decide +kernel

/-- The target claim is derived from the source result and generic cursor
law; it does not separately assume a completed evaluator equivalence. -/
theorem target_first_retains_the_answerless_take :
    one.answers = [.symbol "b"] ∧ one.world = [.symbol "c"] := by
  have exact := congrArg (fun selected => (selected.1, selected.2.1))
    (transform_prefix route source emit 1 start)
  change (one.answers, one.world) = (firstSource.1, firstSource.2.1) at exact
  exact ⟨(congrArg Prod.fst exact).trans source_first_passes_an_answerless_firing.1,
    (congrArg Prod.snd exact).trans source_first_passes_an_answerless_firing.2⟩

theorem source_resume_uses_the_consumers_store :
    (firstSource.2.2 [.symbol "outside", .symbol "c"]).drain =
      ([.symbol "c"], [.symbol "outside"]) := by decide +kernel

theorem restarting_revisits_candidates_instead_of_resuming :
    (job [.symbol "a", .symbol "c"]).drain = ([.symbol "c"], []) ∧
      (firstSource.2.2 [.symbol "a", .symbol "c"]).drain = ([.symbol "c"], [.symbol "a"]) := by decide +kernel

def pair (tag name : String) : Atom := .expression [.symbol tag, .symbol name]
def contention : Sources :=
  ⟨[.pat .take (.expression [.symbol "job", .var "j"]),
    .pat .take (.expression [.symbol "receiver", .var "r"])], [], none⟩
def pairs : Store := [pair "job" "a", pair "job" "b", pair "receiver" "alice", pair "receiver" "bob"]
def result : Atom := .expression [.symbol "done", .var "j", .var "r"]

theorem contention_preserves_the_source_firing_order :
    (transform contention result pairs).drain =
      ([.expression [.symbol "done", .symbol "a", .symbol "alice"],
        .expression [.symbol "done", .symbol "b", .symbol "bob"]], []) := by decide +kernel

def limited := readout ScopedCommitCursor.pull (budgeted 1 2 job start).2
def resumed := readout ScopedCommitCursor.pull
  (Cursor.resume (NativeControlEffectCursor.provider ScopedCommitCursor.pull)
    (NativeControlBoundedCursor.client Atom) (fun _ _ => 1) 1 (budgeted 1 2 job start)).2

theorem poll_cutoff_is_not_exhaustion :
    limited.answers = [.symbol "b"] ∧ limited.world = [.symbol "c"] ∧ limited.stop = .budget := by
  decide +kernel

theorem resume_retains_the_original_answer_quota :
    resumed.answers = [.symbol "b", .symbol "c"] ∧ resumed.world = [] ∧ resumed.stop = .limit := by
  have same := congrArg (fun result => readout ScopedCommitCursor.pull result.2)
    (budgeted_split 1 1 2 job start)
  change readout ScopedCommitCursor.pull (budgeted 2 2 job start).2 = resumed at same
  rw [← same]
  decide +kernel

theorem caller_change_reaches_the_actual_target_residual :
    ScopedCommit.resume (ScopedCommitCursor.sourceView one).2.2 [.symbol "outside", .symbol "c"] =
      ([.symbol "c"], [.symbol "outside"]) := by
  exact (residual_at_any_store 1 job start [.symbol "outside", .symbol "c"]).trans
    source_resume_uses_the_consumers_store

theorem empty_instance_is_an_effect_without_an_answer :
    (select 1 (transform source (.expression [.symbol ","])) start).1 = [] ∧
      (select 1 (transform source (.expression [.symbol ","])) start).2.1 = [] := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaTransformDemand

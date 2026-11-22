import Mettapedia.Languages.FiniteChoice.FrontierAlgebra
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.NullKinds

/-!
# Scoped observations of finite producers

An observation keeps ordered occurrences, coverage and negative dependencies
together. Its index is a captured subject/query identity, not a proof. The
finite producer below consumes actual candidates; completion is derived from
its remaining work. Point lookup checks keys, including misses in nonempty
stores. The model is independent of the C representation and does not assert
that native coordinates alone authenticate a report.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.FiniteChoice.ScopedObservation

open Mettapedia.Languages.FiniteChoice

inductive Event (Value : Type) where
  | witness (identity : List Nat) (value : Value)
  | fault (identity : List Nat) (reason : String)
  deriving DecidableEq, Repr

def values {Value : Type} (events : List (Event Value)) : List Value :=
  events.filterMap fun e => match e with
    | .witness _ value => some value
    | .fault _ _ => none

structure Report (Index Value : Type) (Dependency : Type := Index) where
  index : Index
  events : List (Event Value)
  completion : Frontier.Completion
  negativeDependencies : List Dependency

def Report.Empty {Index Value Dependency : Type} (r : Report Index Value Dependency) : Prop :=
  r.completion = .exhausted ∧ r.events = []

inductive Work (Value : Type) where
  | skip
  | emit (event : Event Value)

def Work.output {Value : Type} : Work Value → List (Event Value)
  | .skip => []
  | .emit event => [event]

structure Cursor (Index Value : Type) where
  index : Index
  seen : List (Event Value)
  remaining : List (Work Value)

def Cursor.meaning {Index Value : Type} (c : Cursor Index Value) : List (Event Value) :=
  c.seen ++ c.remaining.flatMap Work.output

def advance {Index Value : Type} (c : Cursor Index Value) : Cursor Index Value :=
  match c.remaining with
  | [] => c
  | work :: rest => ⟨c.index, c.seen ++ work.output, rest⟩

def run {Index Value : Type} : Nat → Cursor Index Value → Cursor Index Value
  | 0, c => c
  | fuel + 1, c => run fuel (advance c)

def observe {Index Value : Type} (c : Cursor Index Value) : Report Index Value :=
  ⟨c.index, c.seen, if c.remaining.isEmpty then .exhausted else .pending,
    if c.remaining.isEmpty && c.seen.isEmpty then [c.index] else []⟩

theorem advance_preserves {Index Value : Type} (c : Cursor Index Value) :
    (advance c).meaning = c.meaning := by
  cases c with
  | mk index seen remaining =>
    cases remaining <;> simp [advance, Cursor.meaning, List.append_assoc]

theorem run_preserves {Index Value : Type} (fuel : Nat) (c : Cursor Index Value) :
    (run fuel c).meaning = c.meaning := by
  induction fuel generalizing c with
  | zero => rfl
  | succ n ih => exact (ih (advance c)).trans (advance_preserves c)

theorem run_keeps_index {Index Value : Type} (fuel : Nat) (c : Cursor Index Value) :
    (run fuel c).index = c.index := by
  induction fuel generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [run, ih]
    cases h : c.remaining <;> simp [advance, h]

theorem run_add {Index Value : Type} (first second : Nat) (c : Cursor Index Value) :
    run (first + second) c = run second (run first c) := by
  induction first generalizing c with
  | zero => simp [run]
  | succ n ih => simpa [Nat.succ_add, run] using ih (advance c)

theorem seen_prefix_advance {Index Value : Type} (c : Cursor Index Value) :
    ∃ suffix, (advance c).seen = c.seen ++ suffix := by
  cases h : c.remaining with
  | nil => exact ⟨[], by simp [advance, h]⟩
  | cons work rest => exact ⟨work.output, by simp [advance, h]⟩

theorem seen_prefix_run {Index Value : Type} (fuel : Nat) (c : Cursor Index Value) :
    ∃ suffix, (run fuel c).seen = c.seen ++ suffix := by
  induction fuel generalizing c with
  | zero => exact ⟨[], (List.append_nil _).symm⟩
  | succ n ih =>
    obtain ⟨tail, ht⟩ := ih (advance c)
    obtain ⟨head, hh⟩ := seen_prefix_advance c
    exact ⟨head ++ tail, by simp [run, ht, hh, List.append_assoc]⟩

theorem empty_observation_sound {Index Value : Type} (c : Cursor Index Value)
    (h : (observe c).Empty) : c.meaning = [] := by
  have rest : c.remaining = [] := by
    by_contra hn
    simp [observe, Report.Empty, hn] at h
  simpa [Cursor.meaning, rest, observe, Report.Empty] using h.2

theorem finite_run_empty_sound {Index Value : Type} (fuel : Nat) (c : Cursor Index Value)
    (h : (observe (run fuel c)).Empty) : c.meaning = [] := by
  rw [← run_preserves fuel c]
  exact empty_observation_sound _ h

theorem all_work_finishes {Index Value : Type} (index : Index)
    (seen : List (Event Value)) (work : List (Work Value)) :
    (run work.length (⟨index, seen, work⟩ : Cursor Index Value)).remaining = [] := by
  induction work generalizing seen with
  | nil => rfl
  | cons head tail ih => simpa [run, advance] using ih (seen ++ head.output)

def qualify {Value : Type} (side : Nat) : Event Value → Event Value
  | .witness id value => .witness (side :: id) value
  | .fault id reason => .fault (side :: id) reason

def choice {Index Value : Type} (left right : Report Index Value) : Report (Index × Index) Value Index :=
  ⟨(left.index, right.index),
    left.events.map (qualify 0) ++ right.events.map (qualify 1),
    left.completion.merge right.completion,
    left.negativeDependencies ++ right.negativeDependencies⟩

theorem values_qualify {Value : Type} (side : Nat) (events : List (Event Value)) :
    values (events.map (qualify side)) = values events := by
  induction events with
  | nil => rfl
  | cons event rest ih => cases event <;> simp_all [values, qualify]

theorem values_append {Value : Type} (left right : List (Event Value)) :
    values (left ++ right) = values left ++ values right := by
  simp [values]

theorem choice_values {Index Value : Type} (left right : Report Index Value) :
    values (choice left right).events = values left.events ++ values right.events := by
  simp [choice, values_append, values_qualify]

theorem choice_keeps_negative_dependencies {Index Value : Type} (left right : Report Index Value) :
    (choice left right).negativeDependencies =
      left.negativeDependencies ++ right.negativeDependencies := rfl

theorem unfinished_choice_stays_unfinished {Index Value : Type} (left right : Report Index Value)
    (pending : right.completion = .pending) :
    (choice left right).completion = .pending := by
  simp [choice, pending]

def lookup {Key Value : Type} [DecidableEq Key] (key : Key) : List (Key × Value) → Option Value
  | [] => none
  | (other, value) :: rest => if key = other then some value else lookup key rest

theorem lookup_none_iff {Key Value : Type} [DecidableEq Key] (key : Key)
    (rows : List (Key × Value)) :
    lookup key rows = none ↔ ∀ row ∈ rows, row.1 ≠ key := by
  induction rows with
  | nil => simp [lookup]
  | cons head rest ih =>
    obtain ⟨other, value⟩ := head
    by_cases h : key = other
    · subst other; simp [lookup]
    · simp [lookup, h, ih, Ne.symm h]

def point {Key Value : Type} [DecidableEq Key] (index : Key)
    (rows : List (Key × Value)) : Report (List (Key × Value) × Key) Value :=
  match lookup index rows with
  | none => ⟨(rows, index), [], .exhausted, [(rows, index)]⟩
  | some value => ⟨(rows, index), [.witness [0] value], .exhausted, []⟩

theorem point_empty_iff {Key Value : Type} [DecidableEq Key] (index : Key)
    (rows : List (Key × Value)) :
    (point index rows).Empty ↔ ∀ row ∈ rows, row.1 ≠ index := by
  rw [← lookup_none_iff]
  cases h : lookup index rows <;> simp [point, h, Report.Empty]

-- A checker tests every actual key, not whether the container happens to be empty.
def excludes {Key Value : Type} [DecidableEq Key] (key : Key) (rows : List (Key × Value)) : Bool :=
  rows.all fun row => decide (row.1 ≠ key)

theorem exclusion_checker_sound {Key Value : Type} [DecidableEq Key] (key : Key)
    (rows : List (Key × Value)) (checked : excludes key rows = true) :
    (point key rows).Empty := by
  rw [point_empty_iff]
  simpa [excludes, List.all_eq_true] using checked

theorem unrelated_insert_preserves_absence {Key Value : Type} [DecidableEq Key]
    (query other : Key) (value : Value) (rows : List (Key × Value))
    (different : query ≠ other) :
    (point query ((other, value) :: rows)).Empty ↔ (point query rows).Empty := by
  simp only [point_empty_iff, List.mem_cons, forall_eq_or_imp]
  simp [Ne.symm different]

-- Both reports arise by running the SAME finite producer at different budgets.
-- A values-only reconstruction cannot distinguish pending from exhausted.
theorem no_completion_from_values :
    ¬ ∃ reconstruct : List Nat → Frontier.Completion,
        ∀ (fuel : Nat) (cursor : Cursor Nat Nat),
          reconstruct (values (observe (run fuel cursor)).events) =
            (observe (run fuel cursor)).completion := by
  rintro ⟨reconstruct, correct⟩
  let cursor : Cursor Nat Nat := ⟨0, [], [.skip]⟩
  have pending := correct 0 cursor
  have finished := correct 1 cursor
  simp [cursor, run, advance, observe, values, Work.output] at pending finished
  rw [pending] at finished
  cases finished

theorem stopped_producer_stays_stopped {Index Value : Type} (fuel : Nat)
    (index : Index) (seen : List (Event Value)) :
    run fuel (⟨index, seen, []⟩ : Cursor Index Value) = ⟨index, seen, []⟩ := by
  induction fuel with
  | zero => rfl
  | succ n ih => simpa [run, advance] using ih

theorem nonempty_miss_and_later_witness :
    (point 2 [(1, "other")]).Empty ∧ ¬ (point 2 [(2, "new"), (1, "other")]).Empty := by
  simp [point, lookup, Report.Empty]

def twoEdgePath (edges : List (Fin 3 × Fin 3)) : Prop :=
  ∃ middle : Fin 3, ((0 : Fin 3), middle) ∈ edges ∧ (middle, (2 : Fin 3)) ∈ edges

theorem graph_join_creates_witness :
    ¬ twoEdgePath [(0, 1)] ∧ ¬ twoEdgePath [(1, 2)] ∧
      twoEdgePath ([(0, 1)] ++ [(1, 2)]) := by
  unfold twoEdgePath
  decide

theorem empty_left_pending_three_right :
    let left : Report Nat Nat := ⟨0, [], .exhausted, [0]⟩
    let right : Report Nat Nat := ⟨1,
      [.witness [0] 7, .witness [1] 7, .witness [2] 9], .pending, []⟩
    values (choice left right).events = [7, 7, 9] ∧
      (choice left right).completion = .pending ∧ ¬ (choice left right).Empty := by
  simp [choice, values, qualify, Frontier.Completion.merge, Report.Empty]

-- Existing step theory's refusal is candidate-local, rather than global absence.
theorem empty_answer_is_not_no_successor
    {Obj : Type} {Tm : Obj → Type} {Hom : Obj → Obj → Type}
    {X : Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Frames Tm Hom}
    {O State : Type} [DecidableEq O] {Firing : State → Type}
    (P : Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step X O State Firing)
    {s : State}
    (h : Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.EmptyAnswer P s) :
    ¬ Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.NoSuccessor P s :=
  Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.emptyAnswer_not_noSuccessor h

#print axioms finite_run_empty_sound
#print axioms point_empty_iff
#print axioms exclusion_checker_sound
#print axioms run_add
#print axioms choice_values
#print axioms graph_join_creates_witness

end Mettapedia.Languages.FiniteChoice.ScopedObservation

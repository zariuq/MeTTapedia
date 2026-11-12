import Mettapedia.Languages.FiniteChoice.ScopedObservation
import Mathlib.Logic.Relation

/-!
# Producer and interface correspondence for scoped observations

Finite scans inspect actual rows. Negative grades keep exact point premises,
checked at their subject of use. Parser consumption and type-level emptiness
remain separate from result cardinality. No runtime representation is assumed.
-/
set_option autoImplicit false
namespace Mettapedia.Languages.FiniteChoice.ScopedObservation

/-- Actual row inspection; each position is a distinct occurrence. -/
def scanWork {Key Value : Type} [DecidableEq Key] (query : Key) :
    Nat → List (Key × Value) → List (Work Value)
  | _, [] => []
  | ordinal, (key, value) :: rest =>
      (if key = query then .emit (.witness [ordinal] value) else .skip) ::
        scanWork query (ordinal + 1) rest

theorem scanWork_length {Key Value : Type} [DecidableEq Key] (query : Key)
    (ordinal : Nat) (rows : List (Key × Value)) :
    (scanWork query ordinal rows).length = rows.length := by
  induction rows generalizing ordinal with
  | nil => rfl
  | cons row rest ih => simp [scanWork, ih]

theorem scanWork_empty_iff {Key Value : Type} [DecidableEq Key] (query : Key)
    (ordinal : Nat) (rows : List (Key × Value)) :
    (scanWork query ordinal rows).flatMap Work.output = [] ↔
      ∀ row ∈ rows, row.1 ≠ query := by
  induction rows generalizing ordinal with
  | nil => simp [scanWork]
  | cons row rest ih =>
    obtain ⟨key, value⟩ := row
    by_cases h : key = query <;> simp [scanWork, h, Work.output, ih]

/-- Completion plus absence comes from all consumed candidates. -/
theorem scan_completed_absence {Key Value : Type} [DecidableEq Key] (query : Key)
    (rows : List (Key × Value)) (fuel : Nat)
    (h : (observe (run fuel
      (⟨(rows, query), [], scanWork query 0 rows⟩ : Cursor _ Value))).Empty) :
    lookup query rows = none := by
  apply (lookup_none_iff query rows).mpr
  apply (scanWork_empty_iff query 0 rows).mp
  simpa [Cursor.meaning] using finite_run_empty_sound fuel _ h

theorem scan_coverage_finishes {Key Value : Type} [DecidableEq Key] (query : Key)
    (rows : List (Key × Value)) :
    (run rows.length
      (⟨(rows, query), [], scanWork query 0 rows⟩ : Cursor _ Value)).remaining = [] := by
  simpa [scanWork_length] using all_work_finishes (rows, query) [] (scanWork query 0 rows)

def GradeHolds {Key Value : Type} [DecidableEq Key]
    (rows : List (Key × Value)) (premises : List Key) : Prop :=
  ∀ key ∈ premises, lookup key rows = none

def checkGrade {Key Value : Type} [DecidableEq Key]
    (rows : List (Key × Value)) (premises : List Key) : Bool :=
  premises.all fun key => (lookup key rows).isNone

theorem checkGrade_sound {Key Value : Type} [DecidableEq Key]
    (rows : List (Key × Value)) (premises : List Key)
    (checked : checkGrade rows premises = true) : GradeHolds rows premises := by
  simpa [checkGrade, GradeHolds, List.all_eq_true] using checked

theorem grade_conjunction {Key Value : Type} [DecidableEq Key]
    (rows : List (Key × Value)) (left right : List Key) :
    GradeHolds rows (left ++ right) ↔ GradeHolds rows left ∧ GradeHolds rows right := by
  simp [GradeHolds, List.mem_append, or_imp, forall_and]

theorem grade_requires_subject_revalidation :
    GradeHolds [(1, "other")] [2] ∧
      ¬ GradeHolds [(2, "new"), (1, "other")] [2] := by
  simp [GradeHolds, lookup]

structure ParseOccurrence (Value : Type) where
  consumed : Nat
  value : Value

theorem epsilon_is_not_no_parse {Value : Type} (value : Value) :
    ([⟨0, value⟩] : List (ParseOccurrence Value)) ≠ [] := List.cons_ne_nil _ _

theorem empty_type_eliminates {claim : Prop} (impossible : PEmpty) : claim :=
  impossible.elim

/-- A report spelling alone cannot discharge a negative premise. -/
theorem unscoped_tag_cannot_establish_grade :
    ¬ (∀ rows : List (Nat × Nat), GradeHolds rows [2]) := by
  intro claimed
  have bad := claimed [(2, 7)]
  simp [GradeHolds, lookup] at bad

/-- Event identity is separate from its payload, including for faults. -/
def eventIdentity {Value : Type} : Event Value → List Nat
  | .witness id _ => id
  | .fault id _ => id

/-- An executable finite checker for an ordered overlap reconciliation.
The two sublist tests use the standard library's decidable subsequence check;
identity uniqueness rules out keeping conflicting records under one identity. -/
def checkOverlap {Value : Type} [DecidableEq Value]
    (left right candidate : List (Event Value)) : Bool :=
  decide (left.Sublist candidate) && decide (right.Sublist candidate) &&
    decide ((candidate.map eventIdentity).Nodup) &&
    candidate.all fun event => decide (event ∈ left ∨ event ∈ right)

theorem checked_overlap_sound {Value : Type} [DecidableEq Value]
    (left right candidate : List (Event Value))
    (checked : checkOverlap left right candidate = true) :
    ((left.Sublist candidate ∧ right.Sublist candidate) ∧
       (candidate.map eventIdentity).Nodup) ∧
       ∀ event ∈ candidate, event ∈ left ∨ event ∈ right := by
  simpa [checkOverlap, List.all_eq_true, and_assoc] using checked

/-- Equal payloads at different identities cannot be compressed to one occurrence. -/
theorem payload_deduplication_fails_overlap_check :
    checkOverlap ([.witness [0] 7, .witness [1] 7] : List (Event Nat))
      [.witness [1] 7] [.witness [0] 7] = false := by decide

/-- Only witnessed branches demand a continuation. Faults are retained separately. -/
def demandedReports {Index A B : Type} (next : A → Report Index B) :
    List (Event A) → List (Report Index B)
  | [] => []
  | .witness _ value :: rest => next value :: demandedReports next rest
  | .fault _ _ :: rest => demandedReports next rest

def qualifyPath {Value : Type} (path : List Nat) : Event Value → Event Value
  | .witness id value => .witness (path ++ id) value
  | .fault id reason => .fault (path ++ id) reason

def boundEvents {Index A B : Type} (next : A → Report Index B) :
    List (Event A) → List (Event B)
  | [] => []
  | .witness id value :: rest =>
      (next value).events.map (qualifyPath id) ++ boundEvents next rest
  | .fault id reason :: rest => .fault id reason :: boundEvents next rest

def bindReports {Index A B : Type} (parent : Report Index A)
    (next : A → Report Index B) : Report (Index × List Index) B Index :=
  let demanded := demandedReports next parent.events
  ⟨(parent.index, demanded.map Report.index), boundEvents next parent.events,
    demanded.foldl (fun status child => status.merge child.completion) parent.completion,
    parent.negativeDependencies ++ demanded.flatMap Report.negativeDependencies⟩

theorem values_qualifyPath {Value : Type} (path : List Nat) (events : List (Event Value)) :
    values (events.map (qualifyPath path)) = values events := by
  induction events with
  | nil => rfl
  | cons event rest ih => cases event <;> simp_all [values, qualifyPath]

theorem bind_preserves_order_and_multiplicity {Index A B : Type}
    (parent : Report Index A) (next : A → Report Index B) :
    values (bindReports parent next).events =
      (values parent.events).flatMap (fun value => values (next value).events) := by
  suffices ∀ events : List (Event A),
      values (boundEvents next events) =
        (values events).flatMap (fun value => values (next value).events) by
    exact this parent.events
  intro events
  induction events with
  | nil => rfl
  | cons event rest ih =>
    cases event with
    | witness id value =>
      rw [boundEvents, values_append, values_qualifyPath, ih]
      rfl
    | fault id reason => exact ih

/-- An empty producer does not inherit the status or dependencies of unused code. -/
theorem empty_bind_has_no_extra_demands {Index A B : Type}
    (parent : Report Index A) (next : A → Report Index B) (empty : parent.events = []) :
    (bindReports parent next).completion = parent.completion ∧
    (bindReports parent next).events = [] ∧
    (bindReports parent next).negativeDependencies = parent.negativeDependencies := by
  simp [bindReports, demandedReports, boundEvents, empty]

/-- Closed-set invariants control paths of every finite length. -/
theorem reachability_preserves_closed {Node : Type} {step : Node → Node → Prop}
    (property : Node → Prop) (closed : ∀ a b, property a → step a b → property b)
    {start finish : Node} (initial : property start)
    (reachable : Relation.ReflTransGen step start finish) : property finish := by
  induction reachable with
  | refl => exact initial
  | tail _ edge ih => exact closed _ _ ih edge

def graphReachable (edges : List (Fin 3 × Fin 3)) (start finish : Fin 3) : Prop :=
  Relation.ReflTransGen (fun a b => (a, b) ∈ edges) start finish

/-- Neither captured graph has ANY path from 0 to 2. Their union does. -/
theorem full_reachability_changes_under_graph_join :
    ¬ graphReachable [(0, 1)] 0 2 ∧ ¬ graphReachable [(1, 2)] 0 2 ∧
      graphReachable ([(0, 1)] ++ [(1, 2)]) 0 2 := by
  have left : ¬ graphReachable [(0, 1)] 0 2 := by
    intro path
    have closed : ∀ a b : Fin 3, a ≠ 2 → (a, b) ∈ [(0, 1)] → b ≠ 2 := by decide
    have impossible := reachability_preserves_closed (fun a : Fin 3 => a ≠ 2)
      closed (by decide : (0 : Fin 3) ≠ 2) path
    exact impossible rfl
  have right : ¬ graphReachable [(1, 2)] 0 2 := by
    intro path
    have closed : ∀ a b : Fin 3, a = 0 → (a, b) ∈ [(1, 2)] → b = 0 := by decide
    have impossible := reachability_preserves_closed (fun a : Fin 3 => a = 0)
      closed (rfl : (0 : Fin 3) = 0) path
    exact (by decide : (2 : Fin 3) ≠ 0) impossible
  refine ⟨left, right, ?_⟩
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single (by simp : ((0 : Fin 3), (1 : Fin 3)) ∈ ([(0, 1)] ++ [(1, 2)])))
    (Relation.ReflTransGen.single (by simp : ((1 : Fin 3), (2 : Fin 3)) ∈ ([(0, 1)] ++ [(1, 2)])))

#print axioms scan_completed_absence
#print axioms scan_coverage_finishes
#print axioms checkGrade_sound
#print axioms grade_conjunction
#print axioms grade_requires_subject_revalidation
#print axioms empty_type_eliminates
#print axioms checked_overlap_sound
#print axioms bind_preserves_order_and_multiplicity
#print axioms empty_bind_has_no_extra_demands
#print axioms full_reachability_changes_under_graph_join
end Mettapedia.Languages.FiniteChoice.ScopedObservation

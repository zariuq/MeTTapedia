import Mettapedia.Machines.ConjunctionOrder
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Planning a conjunction without constructing candidate lists

`ConjunctionOrder` supplies the fixed-row, commuting-extension semantics.
Here an executable minimum-score selector depends on the current binding state.
Its scores need not be exact cardinalities: they select a leg, never remove a
leg or a row. Thus an estimate needs no materialized candidate list for semantic
correctness. This does not make arbitrary estimates equally efficient.
The observation is the complete finite answer bag. First-witness choice, timing,
allocation failure and interruption traces are not covered by this theorem.

The counted model below separates pattern-cell writes, candidate tests, and
candidate-array writes. A concrete flat-pattern interpretation proves that
substitution followed by candidate collection and direct binding-view counting
give the same score. Both scan the rows in this model; eliminating output arrays
does not eliminate discrimination or matching work. An indexed estimate is
allowed by the semantic theorem, but its lookup cost and index maintenance are
not established here. Actual exact enumeration remains a separate operation.

The C correspondence targets are `petta_machine_choose_conjunction_leg` and
`native_candidates`: the former substitutes each remaining pattern and obtains
an array only to retain its length; the latter sorts/deduplicates occurrence IDs,
not equal fact values. This module is not a proof of that C implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ConjunctionPlanning

open ConjunctionOrder

variable {S R : Type*}

/-- First index attaining the minimum score in a nonempty finite family. -/
def minimumIndex : (n : Nat) → (Fin (n + 1) → Nat) → Fin (n + 1)
  | 0, _ => 0
  | n + 1, score =>
      let tail := minimumIndex n (fun i => score i.succ)
      if score 0 ≤ score tail.succ then 0 else tail.succ

theorem minimumIndex_le (n : Nat) (score : Fin (n + 1) → Nat)
    (i : Fin (n + 1)) : score (minimumIndex n score) ≤ score i := by
  induction n with
  | zero => have h : i = 0 := by apply Fin.ext; omega
            subst i; exact le_rfl
  | succ n ih =>
      simp only [minimumIndex]
      split_ifs with h
      · refine Fin.cases le_rfl (fun j => ?_) i
        exact h.trans (ih (fun k => score k.succ) j)
      · refine Fin.cases (Nat.le_of_lt (Nat.lt_of_not_ge h)) (fun j => ?_) i
        exact ih (fun k => score k.succ) j

/-- The score may inspect the current state and the chosen leg's descriptor. -/
def estimateStrategy (estimate : S → Leg S R → Nat) : Strategy S R
  | _, [], h => False.elim (h rfl)
  | s, leg :: rest, _ => minimumIndex rest.length (fun i => estimate s ((leg :: rest)[i]))

/-- Score accuracy is not needed when the score only chooses the next leg. -/
theorem estimate_eq_conj (estimate : S → Leg S R → Nat)
    (legs : List (Leg S R)) (h : legs.Pairwise Commute) (s : S) :
    dynamic (estimateStrategy estimate) legs s = conj legs s :=
  dynamic_eq_conj _ legs h s

/-- Two different state-dependent scoring methods give the same complete bag. -/
theorem estimates_equivalent (a b : S → Leg S R → Nat)
    (legs : List (Leg S R)) (h : legs.Pairwise Commute) (s : S) :
    dynamic (estimateStrategy a) legs s = dynamic (estimateStrategy b) legs s := by
  rw [estimate_eq_conj _ _ h, estimate_eq_conj _ _ h]

namespace FlatPattern

/-- A small admitted pattern fragment: constants and single-cell variables.
Repeated unbound variables are candidate wildcards here; exact unification must
still check their correlation when the chosen leg is enumerated. -/
inductive Cell where
  | value : Nat → Cell
  | var : Nat → Cell
  deriving DecidableEq, Repr

abbrev Environment := Nat → Option Nat
abbrev Pattern := List Cell
abbrev Row := List Nat

/-- Occurrence identity is separate from the value stored at that occurrence. -/
structure Occurrence where
  id : Nat
  row : Row
  deriving DecidableEq, Repr

/-- The logical occurrence sequence enumerates each identity once. Discrimination
paths may repeat an identity, but that is not a second stored occurrence. -/
def UniqueOccurrences (rows : List Occurrence) : Prop := (rows.map Occurrence.id).Nodup

def resolve (env : Environment) : Cell → Cell
  | .value n => .value n
  | .var v => match env v with
    | none => .var v
    | some n => .value n

def testCell (env : Environment) : Cell → Nat → Bool
  | .value n, x => n == x
  | .var v, x => match env v with
    | none => true
    | some n => n == x

/-- Reads the original pattern and current environment, without a new pattern. -/
def testView (env : Environment) : Pattern → Row → Bool
  | [], [] => true
  | c :: cs, n :: ns => testCell env c n && testView env cs ns
  | _, _ => false

def emptyEnvironment : Environment := fun _ => none

theorem resolved_cell_test (env : Environment) (c : Cell) (n : Nat) :
    testCell emptyEnvironment (resolve env c) n = testCell env c n := by
  cases c with
  | value v => rfl
  | var v => simp only [resolve, testCell]; cases env v <;> rfl

/-- One output pattern cell is charged exactly where it is constructed. -/
def materialize (env : Environment) : Pattern → Pattern × Nat
  | [] => ([], 0)
  | c :: cs =>
      let tail := materialize env cs
      (resolve env c :: tail.1, tail.2 + 1)

theorem materialize_writes (env : Environment) (p : Pattern) :
    (materialize env p).2 = p.length := by
  induction p with
  | nil => rfl
  | cons c cs ih => simp [materialize, ih]

theorem materialize_test (env : Environment) (p : Pattern) (row : Row) :
    testView emptyEnvironment (materialize env p).1 row = testView env p row := by
  induction p generalizing row with
  | nil => cases row <;> rfl
  | cons c cs ih =>
      cases row with
      | nil => rfl
      | cons n ns => simp [materialize, testView, resolved_cell_test, ih]

/-- Operational counters: `tests` counts row-predicate invocations, not their
internal pattern comparisons, binding reads, elapsed time, or instructions. -/
structure CandidateWork where
  tests : Nat
  writes : Nat
  deriving DecidableEq, Repr

/-- Construct an array/list of occurrence IDs, charging one write per element. -/
def collectCandidates (test : Row → Bool) : List Occurrence → List Nat × CandidateWork
  | [] => ([], ⟨0, 0⟩)
  | o :: os =>
      let tail := collectCandidates test os
      if test o.row then
        (o.id :: tail.1, ⟨tail.2.tests + 1, tail.2.writes + 1⟩)
      else
        (tail.1, ⟨tail.2.tests + 1, tail.2.writes⟩)

/-- Count directly without constructing any candidate-array elements. -/
def countCandidates (test : Row → Bool) : List Occurrence → Nat × CandidateWork
  | [] => (0, ⟨0, 0⟩)
  | o :: os =>
      let tail := countCandidates test os
      (tail.1 + if test o.row then 1 else 0, ⟨tail.2.tests + 1, tail.2.writes⟩)

theorem collectCandidates_tests (test : Row → Bool) (rows : List Occurrence) :
    (collectCandidates test rows).2.tests = rows.length := by
  induction rows with
  | nil => rfl
  | cons o os ih => simp only [collectCandidates]; split <;> simp [ih]

theorem collectCandidates_writes (test : Row → Bool) (rows : List Occurrence) :
    (collectCandidates test rows).2.writes = (collectCandidates test rows).1.length := by
  induction rows with
  | nil => rfl
  | cons o os ih => simp only [collectCandidates]; split <;> simp [ih]

theorem countCandidates_tests (test : Row → Bool) (rows : List Occurrence) :
    (countCandidates test rows).2.tests = rows.length := by
  induction rows with
  | nil => rfl
  | cons o os ih => simp [countCandidates, ih]

theorem countCandidates_writes (test : Row → Bool) (rows : List Occurrence) :
    (countCandidates test rows).2.writes = 0 := by
  induction rows with
  | nil => rfl
  | cons o os ih => exact ih

theorem countCandidates_eq_collect (test : Row → Bool) (rows : List Occurrence) :
    (countCandidates test rows).1 = (collectCandidates test rows).1.length := by
  induction rows with
  | nil => rfl
  | cons o os ih =>
      simp only [collectCandidates, countCandidates]
      split <;> simp_all

def referenceScore (env : Environment) (p : Pattern) (rows : List Occurrence) : Nat :=
  (collectCandidates (testView emptyEnvironment (materialize env p).1) rows).1.length

def viewScore (env : Environment) (p : Pattern) (rows : List Occurrence) : Nat :=
  (countCandidates (testView env p) rows).1

/-- The two independent operational paths compute identical ranking scores. -/
theorem viewScore_eq_reference (env : Environment) (p : Pattern)
    (rows : List Occurrence) : viewScore env p rows = referenceScore env p rows := by
  have h : testView emptyEnvironment (materialize env p).1 = testView env p :=
    funext (materialize_test env p)
  simp only [viewScore, referenceScore, h]
  exact countCandidates_eq_collect _ _

/-- Exact saved allocations for one probe in this scan model. Both paths still
test every row; replacing arrays by counters alone gives no sublinear scan. -/
theorem probe_operations (env : Environment) (p : Pattern) (rows : List Occurrence) :
    (materialize env p).2 = p.length ∧
    (collectCandidates (testView emptyEnvironment (materialize env p).1) rows).2.writes =
      viewScore env p rows ∧
    (countCandidates (testView env p) rows).2.writes = 0 ∧
    (collectCandidates (testView emptyEnvironment (materialize env p).1) rows).2.tests =
      rows.length ∧
    (countCandidates (testView env p) rows).2.tests = rows.length := by
  refine ⟨materialize_writes _ _, ?_, countCandidates_writes _ _,
    collectCandidates_tests _ _, countCandidates_tests _ _⟩
  rw [collectCandidates_writes]
  exact (viewScore_eq_reference _ _ _).symm

/-- Costs of scoring every remaining leg. Score cells themselves are common to
both models and are not included in these three counters. -/
structure PlanningWork where
  patternWrites : Nat
  candidateTests : Nat
  candidateWrites : Nat
  deriving DecidableEq, Repr

def PlanningWork.add (a b : PlanningWork) : PlanningWork :=
  ⟨a.patternWrites + b.patternWrites, a.candidateTests + b.candidateTests,
    a.candidateWrites + b.candidateWrites⟩

def referenceProbe (env : Environment) (rows : List Occurrence) (p : Pattern) :
    Nat × PlanningWork :=
  let prepared := materialize env p
  let candidates := collectCandidates (testView emptyEnvironment prepared.1) rows
  (candidates.1.length, ⟨prepared.2, candidates.2.tests, candidates.2.writes⟩)

def viewProbe (env : Environment) (rows : List Occurrence) (p : Pattern) :
    Nat × PlanningWork :=
  let counted := countCandidates (testView env p) rows
  (counted.1, ⟨0, counted.2.tests, counted.2.writes⟩)

/-- The all-leg scoring traversal, before choosing an index. The current C loop
can stop once it sees zero; the formulas here describe a complete scoring pass,
not the number of legs visited by that early-exit implementation. -/
def scanProbes (probe : Pattern → Nat × PlanningWork) :
    List Pattern → List Nat × PlanningWork
  | [] => ([], ⟨0, 0, 0⟩)
  | p :: ps =>
      let here := probe p
      let tail := scanProbes probe ps
      (here.1 :: tail.1, here.2.add tail.2)

theorem scan_scores_eq (env : Environment) (rows : List Occurrence) (ps : List Pattern) :
    (scanProbes (referenceProbe env rows) ps).1 =
      (scanProbes (viewProbe env rows) ps).1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [scanProbes, List.cons.injEq]
      exact ⟨(viewScore_eq_reference env p rows).symm, ih⟩

/-- Pattern construction scales with all remaining pattern cells. -/
theorem scan_reference_pattern_writes (env : Environment) (rows : List Occurrence)
    (ps : List Pattern) :
    (scanProbes (referenceProbe env rows) ps).2.patternWrites =
      (ps.map List.length).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [scanProbes, referenceProbe, PlanningWork.add,
      materialize_writes, ih]

/-- Every selected candidate occurrence is written once during score collection. -/
theorem scan_reference_candidate_writes (env : Environment) (rows : List Occurrence)
    (ps : List Pattern) :
    (scanProbes (referenceProbe env rows) ps).2.candidateWrites =
      ((scanProbes (viewProbe env rows) ps).1).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [scanProbes, referenceProbe, viewProbe, PlanningWork.add,
        collectCandidates_writes, List.sum_cons]
      rw [ih]
      have h := viewScore_eq_reference env p rows
      exact congrArg (fun n => n + ((scanProbes (viewProbe env rows) ps).1).sum) h.symm

theorem scan_view_no_materialization (env : Environment) (rows : List Occurrence)
    (ps : List Pattern) :
    (scanProbes (viewProbe env rows) ps).2.patternWrites = 0 ∧
    (scanProbes (viewProbe env rows) ps).2.candidateWrites = 0 := by
  induction ps with
  | nil => exact ⟨rfl, rfl⟩
  | cons p ps ih => simp [scanProbes, viewProbe, PlanningWork.add,
      countCandidates_writes, ih]

/-- In a scan backend, counting saves allocation but still examines every row
for every scored leg. No constant-time index estimate is being assumed. -/
theorem scan_candidate_tests (env : Environment) (rows : List Occurrence)
    (ps : List Pattern) :
    (scanProbes (referenceProbe env rows) ps).2.candidateTests = ps.length * rows.length ∧
    (scanProbes (viewProbe env rows) ps).2.candidateTests = ps.length * rows.length := by
  induction ps with
  | nil => simp [scanProbes]
  | cons p ps ih =>
      simp [scanProbes, referenceProbe, viewProbe, PlanningWork.add,
        collectCandidates_tests, countCandidates_tests, ih, Nat.add_mul, Nat.add_comm]

/-! ## Prefix-summary estimates

The metadata below is merely a ranking hint. It is deliberately not certified
as an exact answer count or used to prune candidates. A suitable backend can
expose a stored total and a first-column histogram. No such index is constructed
by this model, and no update-maintenance cost is hidden in the read counter.
-/

structure CardinalitySummary where
  total : Nat
  head : Nat → Nat

inductive EstimateRead where
  | patternHead
  | binding : Nat → EstimateRead
  | total
  | histogram : Nat → EstimateRead
  deriving DecidableEq, Repr

/-- An estimate reads one pattern position and at most one binding and one
summary entry. The tail of the pattern and the stored candidate rows are absent
from this execution. Metadata/binding lookup latency is representation-dependent. -/
def prefixEstimate (env : Environment) (summary : CardinalitySummary) :
    Pattern → Nat × List EstimateRead
  | [] => (summary.total, [.patternHead, .total])
  | .value n :: _ => (summary.head n, [.patternHead, .histogram n])
  | .var v :: _ => match env v with
    | none => (summary.total, [.patternHead, .binding v, .total])
    | some n => (summary.head n, [.patternHead, .binding v, .histogram n])

/-- Three abstract metadata reads suffice for this estimator, regardless of
candidate cardinality. This is not a bound on machine instructions. -/
theorem prefixEstimate_reads (env : Environment) (summary : CardinalitySummary)
    (p : Pattern) : (prefixEstimate env summary p).2.length ≤ 3 := by
  cases p with
  | nil => simp [prefixEstimate]
  | cons c cs =>
      cases c with
      | value n => simp [prefixEstimate]
      | var v => simp only [prefixEstimate]; cases env v <;> simp

/-- A scoring pass which invokes the estimator once per leg. This bound does not
include the representation-dependent cost of selecting the minimum index. -/
theorem prefixEstimate_pass_reads (env : Environment) (summary : CardinalitySummary)
    (ps : List Pattern) :
    (ps.map (fun p => (prefixEstimate env summary p).2.length)).sum ≤ 3 * ps.length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have bound := prefixEstimate_reads env summary p
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- Lift a supplied pattern descriptor into an actual conjunction strategy.
No hypothesis certifies the histogram: it is used solely for ordering. -/
def prefixStrategy (pattern : Leg S R → Pattern) (environment : S → Environment)
    (summary : S → CardinalitySummary) : Strategy S R :=
  estimateStrategy fun s leg => (prefixEstimate (environment s) (summary s) (pattern leg)).1

theorem prefixStrategy_eq_conj (pattern : Leg S R → Pattern) (environment : S → Environment)
    (summary : S → CardinalitySummary) (legs : List (Leg S R))
    (h : legs.Pairwise Commute) (s : S) :
    dynamic (prefixStrategy pattern environment summary) legs s = conj legs s :=
  dynamic_eq_conj _ _ h _

end FlatPattern

namespace Controls

open FlatPattern

def duplicates : List Occurrence := [⟨0, [7]⟩, ⟨1, [7]⟩]

/-- Equal stored values at distinct occurrences both count. -/
theorem duplicate_occurrences_preserved :
    (collectCandidates (testView emptyEnvironment [.var 0]) duplicates).1 = [0, 1] ∧
    viewScore emptyEnvironment [.var 0] duplicates = 2 := by decide

theorem duplicate_values_have_distinct_identities : UniqueOccurrences duplicates := by
  unfold UniqueOccurrences duplicates
  decide

/-- Replacing duplicate fact values with a single representative loses an answer. -/
theorem value_deduplication_changes_count :
    viewScore emptyEnvironment [.var 0] duplicates ≠
      viewScore emptyEnvironment [.var 0] [⟨0, [7]⟩] := by decide

/-- One score pass on two one-cell patterns saves two pattern writes and three
candidate writes, but still performs four row tests. -/
theorem counted_probe_example :
    (scanProbes (referenceProbe emptyEnvironment [⟨0, [7]⟩, ⟨1, [8]⟩])
      [[.var 0], [.value 7]]) = ([2, 1], ⟨2, 4, 3⟩) ∧
    (scanProbes (viewProbe emptyEnvironment [⟨0, [7]⟩, ⟨1, [8]⟩])
      [[.var 0], [.value 7]]) = ([2, 1], ⟨0, 4, 0⟩) := by decide

theorem summary_avoids_candidate_scan :
    prefixEstimate (fun _ => some 7) ⟨1000000, fun _ => 400⟩ [.var 0, .value 8] =
      (400, [.patternHead, .binding 0, .histogram 7]) := by rfl

/-- A zero ranking hint is not a certificate that a leg has no answers. -/
theorem zero_estimate_does_not_certify_empty :
    dynamic (estimateStrategy (fun _ _ => 0))
      [ConjunctionOrder.Controls.left] (0, 0) ≠ 0 := by
  rw [estimate_eq_conj _ _ (by simp)]
  intro h
  have member : (1, 0) ∈ conj [ConjunctionOrder.Controls.left] (0, 0) := by
    simp [conj, Leg.run, ConjunctionOrder.Controls.left, optionMs, Multiset.mem_bind]
  simp [h] at member

def bindingDependentScore (s : Nat × Nat) (leg : Leg (Nat × Nat) Nat) : Nat :=
  if leg.rows == [1, 2] then s.2 else 1

theorem binding_changes_choice :
    (estimateStrategy bindingDependentScore (0, 0)
      [ConjunctionOrder.Controls.left, ConjunctionOrder.Controls.right] (by simp)).val = 0 ∧
    (estimateStrategy bindingDependentScore (0, 3)
      [ConjunctionOrder.Controls.left, ConjunctionOrder.Controls.right] (by simp)).val = 1 := by
  exact ⟨rfl, rfl⟩

/-- Even intentionally obsolete ranking information preserves the complete bag. -/
theorem stale_ranking_is_safe :
    dynamic (estimateStrategy bindingDependentScore)
        [ConjunctionOrder.Controls.left, ConjunctionOrder.Controls.right] (0, 3) =
      dynamic (estimateStrategy (fun _ leg => bindingDependentScore (0, 0) leg))
        [ConjunctionOrder.Controls.left, ConjunctionOrder.Controls.right] (0, 3) := by
  apply estimates_equivalent
  exact List.pairwise_pair.mpr ConjunctionOrder.Controls.independent_commute

/-- In contrast, reusing the candidate rows from an old binding loses a match. -/
theorem stale_binding_candidates_lose_match :
    (collectCandidates (testView (fun _ => some 9) [.var 0]) [⟨0, [7]⟩]).1 = [] ∧
    (collectCandidates (testView (fun _ => some 7) [.var 0]) [⟨0, [7]⟩]).1 = [0] := by
  decide

/-- Reusing a candidate snapshot after insertion likewise loses an occurrence. -/
theorem stale_space_candidates_lose_match :
    (collectCandidates (testView emptyEnvironment [.value 7]) []).1 = [] ∧
    (collectCandidates (testView emptyEnvironment [.value 7]) [⟨0, [7]⟩]).1 = [0] := by
  decide

/-- The view is a discriminator, not a proof that repeated variables unify. -/
theorem repeated_variable_requires_exact_matching :
    testView emptyEnvironment [.var 0, .var 0] [7, 8] = true ∧ (7 : Nat) ≠ 8 := by
  decide

/-- Ordering effects remain outside conjunction reordering, regardless of scores. -/
theorem effect_order_remains_observable :
    conj [ConjunctionOrder.Controls.first, ConjunctionOrder.Controls.second] [] ≠
      conj [ConjunctionOrder.Controls.second, ConjunctionOrder.Controls.first] [] :=
  ConjunctionOrder.Controls.order_matters_without_commuting

end Controls

end Mettapedia.Machines.ConjunctionPlanning

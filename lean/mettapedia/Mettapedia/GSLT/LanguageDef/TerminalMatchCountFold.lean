import Mettapedia.GSLT.Dynamics.CollapseObservationContract

/-!
# Terminal match count folds

A `match` step of the compiled open equation tier runs the code after it once
for every row of a snapshot of the space that unifies with its pattern.  When
the consumer observes only the multiplicity of the answer bag, when the
activation has no caller continuation, and when the step after the match is the
return of a data template, every unifying row publishes exactly one answer.
The tier then publishes a single answer weighted by the number of unifying
rows, and fails when no row unifies.

**Model.**  A snapshot is a list of rows; `unifies` decides whether a row
unifies with the pattern.  The code after the match, run for a row that
unified, produces a completed answer stream `after row` in the collapse
observation algebra (`Obs`: answer, multiplicity, receipt).  The unfolded
execution publishes `perRow unifies after rows`, the continuations' streams in
row order.  A terminal continuation publishes one answer of one occurrence
(`terminal`).  The fold publishes `folded`: nothing when no row unifies, and
otherwise one witness answer whose multiplicity is the number of unifying rows.

**Results.**

* `count_folded_eq_perRow`: under the count algebra the fold and the per-row
  stream agree, for every snapshot, every decidable unification predicate,
  every witness and every template instance.  `countFold` packages the count as
  a `DirectFold` of the per-row producer, the admission interface of the
  collapse observation contract.
* `folded_eq_nil_iff_perRow_eq_nil`: the fold publishes nothing exactly when
  the per-row execution publishes nothing, and `folded_multiplicity_pos`: a
  published fold never carries weight zero.
* `countP_filter_of_sound`: the structural prefilter applied to candidates
  before unification changes no count, since it never rejects a row that
  unifies; the per-row and counting paths therefore see the same rows.
* `count_perRow`: in general the count is the sum of the continuations'
  counts, so the fold is exact only for terminal continuations.

**Negative witnesses.**  A continuation that answers twice for one row, or
fails for one row, makes the number of unifying rows wrong
(`Canary.nonterminal_miscounts`, `Canary.failing_continuation_miscounts`).  A
weight-zero answer has the count of the empty stream but is still one
published answer (`Canary.zero_weight_is_published`).  A bag observer
distinguishes the fold from the per-row answers
(`Canary.bag_distinguishes_fold`), so the fold is licensed by the count
observation alone.

**Correspondence with the C tier.**  The match step instantiates its pattern
and resolves the space.  When the cursor observes only answer counts, the
activation has no caller continuation, and the next step returns, the step
counts the rows that unify instead of pushing a match frame: by the space's own
flat count when the space admits the pattern, otherwise by unifying a fresh
copy of each candidate the index offers, after a structural test that rejects
only a row that differs from the pattern at a position both fix, and undoing
each unification before the next.  Because each trial is undone, a row's
outcome depends on that row alone, which is why the model takes unification as
a predicate on rows.  A zero count fails the step; otherwise the cursor
publishes the return's answer once and reports the count as its weight.  The
per-row path snapshots the same prefiltered candidates, pushes a match frame,
and publishes one answer per unifying row.

**Not covered.**  Exactness of the space's own flat count, which the tier
trusts to count exactly the rows that unify; the construction of fresh row
copies and the unifier itself; and the host's use of the weight.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TerminalMatchCountFold

open Mettapedia.GSLT.Dynamics.Collapse
open Mettapedia.GSLT.Dynamics.CollapseObservationContract

universe uRow

section Streams

variable {Row : Type uRow} {Answer Receipt : Type}

/-- The answers of the code after a match, run once per unifying row, in row
order. -/
def perRow (unifies : Row → Bool) (after : Row → List (Obs Answer Receipt))
    (rows : List Row) : List (Obs Answer Receipt) :=
  (rows.filter unifies).flatMap after

/-- The continuation of a terminal match: the return of a data template
publishes one answer of one occurrence. -/
def terminal (answer : Row → Answer) (receipt : Receipt) :
    Row → List (Obs Answer Receipt) :=
  fun row => [⟨answer row, 1, receipt⟩]

/-- The fold: nothing when no row unifies, otherwise one witness answer whose
weight is the number of unifying rows. -/
def folded (unifies : Row → Bool) (witness : Answer) (receipt : Receipt)
    (rows : List Row) : List (Obs Answer Receipt) :=
  if rows.countP unifies = 0 then [] else [⟨witness, rows.countP unifies, receipt⟩]

/-- The count algebra adds multiplicities. -/
theorem collapseCount_eq_sum (observations : List (Obs Answer Receipt)) :
    collapseWith (CountAlg Answer Receipt) observations =
      (observations.map Obs.multiplicity).sum := by
  change foldStream (CountAlg Answer Receipt) observations = _
  induction observations with
  | nil => rfl
  | cons observation rest inductionHypothesis =>
      rw [foldStream_cons, inductionHypothesis]
      simp [CountAlg]

/-- The count of a per-row execution is the sum of its continuations'
counts. -/
theorem count_perRow (unifies : Row → Bool)
    (after : Row → List (Obs Answer Receipt)) (rows : List Row) :
    collapseWith (CountAlg Answer Receipt) (perRow unifies after rows) =
      ((rows.filter unifies).map fun row =>
        collapseWith (CountAlg Answer Receipt) (after row)).sum := by
  unfold perRow
  induction rows.filter unifies with
  | nil => rfl
  | cons row rest inductionHypothesis =>
      rw [List.flatMap_cons, collapseWith,
        foldStream_append _ count_monoid, List.map_cons, List.sum_cons,
        ← inductionHypothesis]
      rfl

/-- A terminal continuation counts one for each unifying row. -/
theorem count_perRow_terminal (unifies : Row → Bool) (answer : Row → Answer)
    (receipt : Receipt) (rows : List Row) :
    collapseWith (CountAlg Answer Receipt)
        (perRow unifies (terminal answer receipt) rows) =
      rows.countP unifies := by
  rw [count_perRow, List.countP_eq_length_filter]
  induction rows.filter unifies with
  | nil => rfl
  | cons row rest inductionHypothesis =>
      rw [List.map_cons, List.sum_cons, inductionHypothesis, List.length_cons,
        collapseCount_eq_sum]
      simp [terminal, Nat.add_comm]

/-- The fold's count is the number of unifying rows. -/
theorem count_folded (unifies : Row → Bool) (witness : Answer)
    (receipt : Receipt) (rows : List Row) :
    collapseWith (CountAlg Answer Receipt) (folded unifies witness receipt rows) =
      rows.countP unifies := by
  unfold folded
  split
  · next zero => rw [zero]; rfl
  · rw [collapseCount_eq_sum]
    simp

/-- **Count fold.**  Under the count observation, the single weighted answer
means the per-row answer stream of a terminal match, for every snapshot,
unification predicate, witness and template instance. -/
theorem count_folded_eq_perRow (unifies : Row → Bool) (witness : Answer)
    (answer : Row → Answer) (receipt : Receipt) (rows : List Row) :
    collapseWith (CountAlg Answer Receipt) (folded unifies witness receipt rows) =
      collapseWith (CountAlg Answer Receipt)
        (perRow unifies (terminal answer receipt) rows) := by
  rw [count_folded, count_perRow_terminal]

/-- The fold is the collapse observation contract's single weighted witness of
the per-row stream, whenever it publishes. -/
theorem folded_eq_weighted_witness (unifies : Row → Bool) (witness : Answer)
    (answer : Row → Answer) (receipt : Receipt) (rows : List Row)
    (some_row : rows.countP unifies ≠ 0) :
    folded unifies witness receipt rows =
      [⟨witness,
        collapseWith (CountAlg Answer Receipt)
          (perRow unifies (terminal answer receipt) rows),
        receipt⟩] := by
  rw [count_perRow_terminal]
  simp [folded, some_row]

/-- The fold publishes nothing exactly when no row unifies. -/
theorem folded_eq_nil_iff (unifies : Row → Bool) (witness : Answer)
    (receipt : Receipt) (rows : List Row) :
    folded unifies witness receipt rows = [] ↔
      ∀ row ∈ rows, unifies row = false := by
  have zero_iff : rows.countP unifies = 0 ↔ ∀ row ∈ rows, unifies row = false := by
    simp [List.countP_eq_zero]
  unfold folded
  split
  · next zero => exact ⟨fun _ => zero_iff.mp zero, fun _ => rfl⟩
  · next nonzero =>
      exact ⟨fun published => by simp at published,
        fun none_unify => (nonzero (zero_iff.mpr none_unify)).elim⟩

/-- The per-row execution publishes nothing exactly when no row unifies. -/
theorem perRow_terminal_eq_nil_iff (unifies : Row → Bool) (answer : Row → Answer)
    (receipt : Receipt) (rows : List Row) :
    perRow unifies (terminal answer receipt) rows = [] ↔
      ∀ row ∈ rows, unifies row = false := by
  simp [perRow, terminal]

/-- The fold fails exactly when the per-row execution has no answer. -/
theorem folded_eq_nil_iff_perRow_eq_nil (unifies : Row → Bool)
    (witness : Answer) (answer : Row → Answer) (receipt : Receipt)
    (rows : List Row) :
    folded unifies witness receipt rows = [] ↔
      perRow unifies (terminal answer receipt) rows = [] := by
  rw [folded_eq_nil_iff, perRow_terminal_eq_nil_iff]

/-- A published fold never carries weight zero. -/
theorem folded_multiplicity_pos (unifies : Row → Bool) (witness : Answer)
    (receipt : Receipt) (rows : List Row) :
    ∀ observation ∈ folded unifies witness receipt rows,
      0 < observation.multiplicity := by
  intro observation member
  unfold folded at member
  split at member
  · simp at member
  · next nonzero =>
      rw [List.mem_singleton] at member
      subst member
      exact Nat.pos_of_ne_zero nonzero

end Streams

/-! ## The structural prefilter -/

section Prefilter

variable {Row : Type uRow}

/-- A prefilter that never rejects a row that unifies leaves the unifying rows
unchanged. -/
theorem filter_filter_of_sound (mayUnify unifies : Row → Bool)
    (sound : ∀ row, unifies row = true → mayUnify row = true)
    (rows : List Row) :
    (rows.filter mayUnify).filter unifies = rows.filter unifies := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro row _
  cases unified : unifies row with
  | false => simp
  | true => simp [sound row unified]

/-- Counting after such a prefilter counts every unifying row. -/
theorem countP_filter_of_sound (mayUnify unifies : Row → Bool)
    (sound : ∀ row, unifies row = true → mayUnify row = true)
    (rows : List Row) :
    (rows.filter mayUnify).countP unifies = rows.countP unifies := by
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter,
    filter_filter_of_sound mayUnify unifies sound]

/-- The per-row execution over the prefiltered snapshot publishes the answers
of the per-row execution over all candidates. -/
theorem perRow_filter_of_sound {Answer Receipt : Type}
    (mayUnify unifies : Row → Bool)
    (sound : ∀ row, unifies row = true → mayUnify row = true)
    (after : Row → List (Obs Answer Receipt)) (rows : List Row) :
    perRow unifies after (rows.filter mayUnify) = perRow unifies after rows := by
  unfold perRow
  rw [filter_filter_of_sound mayUnify unifies sound]

end Prefilter

/-! ## The fold as a direct fold of the per-row producer -/

section DirectFold

variable {Row : Type uRow} {Answer Receipt : Type}

/-- The per-row execution of a terminal match as a producer of completed
observation streams, indexed by the snapshot. -/
def terminalProducer (unifies : Row → Bool) (answer : Row → Answer)
    (receipt : Receipt) : Producer (List Row) (Obs Answer Receipt) where
  materialize := perRow unifies (terminal answer receipt)

/-- The row count is a direct implementation of the count algebra over the
per-row producer: the admission obligation of the observation contract,
discharged. -/
def countFold (unifies : Row → Bool) (answer : Row → Answer)
    (receipt : Receipt) :
    DirectFold (terminalProducer unifies answer receipt)
      (CountAlg Answer Receipt) where
  run rows := rows.countP unifies
  refines rows := (count_perRow_terminal unifies answer receipt rows).symm

/-- The published fold realizes the direct fold's result. -/
theorem count_folded_eq_countFold (unifies : Row → Bool) (witness : Answer)
    (answer : Row → Answer) (receipt : Receipt) (rows : List Row) :
    collapseWith (CountAlg Answer Receipt) (folded unifies witness receipt rows) =
      (countFold unifies answer receipt).run rows :=
  count_folded unifies witness receipt rows

end DirectFold

/-! ## Positive and negative witnesses -/

namespace Canary

/-- Rows are numbers; a row unifies when it is even. -/
def evenRow (row : Nat) : Bool := row % 2 == 0

/-- Positive: three candidates, two unify; the fold publishes one answer of
weight two, and the per-row execution two answers of weight one. -/
example :
    folded evenRow (0 : Nat) () [2, 3, 4] = [⟨0, 2, ()⟩] ∧
      perRow evenRow (terminal id ()) [2, 3, 4] =
        [⟨2, 1, ()⟩, ⟨4, 1, ()⟩] :=
  ⟨rfl, rfl⟩

/-- Positive: no candidate unifies; both publish nothing. -/
example :
    folded evenRow (0 : Nat) () [1, 3] = [] ∧
      perRow evenRow (terminal id ()) [1, 3] = [] :=
  ⟨rfl, rfl⟩

/-- A continuation that answers twice for the row `0`: not the return of a data
template. -/
def twiceAtZero (row : Nat) : List (Obs Nat Unit) :=
  if row = 0 then [⟨row, 1, ()⟩, ⟨row, 1, ()⟩] else [⟨row, 1, ()⟩]

/-- Negative: with a nonterminal continuation the number of unifying rows is
not the count of the per-row execution. -/
theorem nonterminal_miscounts :
    collapseWith (CountAlg Nat Unit) (folded evenRow (0 : Nat) () [0, 2]) ≠
      collapseWith (CountAlg Nat Unit) (perRow evenRow twiceAtZero [0, 2]) := by
  decide

/-- A continuation that fails for the row `2`. -/
def failsAtTwo (row : Nat) : List (Obs Nat Unit) :=
  if row = 2 then [] else [⟨row, 1, ()⟩]

/-- Negative: a continuation that can fail makes the fold overcount. -/
theorem failing_continuation_miscounts :
    collapseWith (CountAlg Nat Unit) (folded evenRow (0 : Nat) () [0, 2]) ≠
      collapseWith (CountAlg Nat Unit) (perRow evenRow failsAtTwo [0, 2]) := by
  decide

/-- Negative: a weight-zero answer has the count of the empty stream, yet it is
one published answer where the per-row execution publishes none. -/
theorem zero_weight_is_published :
    collapseWith (CountAlg Nat Unit) [⟨0, 0, ()⟩] =
        collapseWith (CountAlg Nat Unit)
          (perRow evenRow (terminal id ()) [1, 3]) ∧
      ([⟨0, 0, ()⟩] : List (Obs Nat Unit)).length ≠
        (perRow evenRow (terminal id ()) [1, 3]).length := by
  decide

/-- Negative: an observer of the answer bag distinguishes the fold from the
per-row answers, so the fold is licensed by the count observation only. -/
theorem bag_distinguishes_fold :
    collapseWith (BagAlg Nat Unit) (folded evenRow (0 : Nat) () [0, 2]) ≠
      collapseWith (BagAlg Nat Unit) (perRow evenRow (terminal id ()) [0, 2]) := by
  intro same
  have counted := congrArg (Multiset.count (2 : Nat)) same
  simp [collapseWith, foldStream, BagAlg, folded, perRow, terminal, evenRow]
    at counted

/-- A prefilter that admits only rows below ten. -/
def lowPrefilter (row : Nat) : Bool := row < 10

/-- Positive: on candidates below ten the prefilter rejects no unifying row
and changes no count. -/
example :
    ([2, 4, 7].filter lowPrefilter).countP evenRow = [2, 4, 7].countP evenRow := by
  decide

/-- Negative: an unsound prefilter, which rejects the unifying row `12`,
undercounts. -/
theorem unsound_prefilter_undercounts :
    ([2, 12].filter lowPrefilter).countP evenRow ≠ [2, 12].countP evenRow := by
  decide

end Canary

end Mettapedia.GSLT.LanguageDef.TerminalMatchCountFold

import Mettapedia.Machines.CapturedRowReaders
import Mettapedia.Machines.MatchIndexProjection

/-! Captured rows can be projected after a source declaration becomes known.
Selection preserves occurrence order and the decoder's first error. Index
candidates may be conservative; the exact head predicate remains authoritative. -/

set_option autoImplicit false

namespace Mettapedia.Machines.SelectiveRowCapture

variable {Row Error Fact : Type}

def collect (decode : Row → Except Error (List Fact)) (rows : List Row) : Except Error (List Fact) :=
  (rows.mapM decode).map List.flatten

theorem collect_append (decode : Row → Except Error (List Fact)) (first second : List Row) :
    collect decode (first ++ second) = (do
      let left ← collect decode first
      let right ← collect decode second
      pure (left ++ right)) := by
  simp only [collect, List.mapM_append]
  cases first.mapM decode <;> cases second.mapM decode
  all_goals try rfl
  rename_i left right
  change Except.ok ((left ++ right).flatten) =
    (Except.ok (left.flatten ++ right.flatten) : Except Error (List Fact))
  rw [List.flatten_append]

theorem collect_singleton (decode : Row → Except Error (List Fact)) (row : Row) :
    collect decode [row] = decode row := by
  cases result : decode row <;> simp [collect, result, Except.map]

theorem collect_cons (decode : Row → Except Error (List Fact)) (row : Row) (rest : List Row) :
    collect decode (row :: rest) = (do
      let first ← decode row
      let later ← collect decode rest
      pure (first ++ later)) := by
  simpa only [List.singleton_append, collect_singleton] using collect_append decode [row] rest

/-- Removing irrelevant occurrences preserves both successful results and
the same first error. This is stronger than equality of successful fact sets. -/
theorem collect_filter (decode : Row → Except Error (List Fact)) (selected : Row → Bool)
    (irrelevant : ∀ row, selected row = false → decode row = .ok []) (rows : List Row) :
    collect decode (rows.filter selected) = collect decode rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    cases choice : selected row with
    | false =>
      simp only [List.filter_cons, choice, Bool.false_eq_true, if_false, ih, collect_cons,
        irrelevant row choice]
      cases collect decode rest <;> rfl
    | true => simp only [List.filter_cons, choice, if_true, collect_cons, ih]

/-- A complete index frontier followed by exact selection gives the same
capture as the full stored occurrence list. -/
theorem collect_candidates (decode : Row → Except Error (List Fact))
    (possible selected : Row → Bool)
    (complete : ∀ row, selected row = true → possible row = true)
    (irrelevant : ∀ row, selected row = false → decode row = .ok []) (rows : List Row) :
    collect decode ((rows.filter possible).filter selected) = collect decode rows := by
  rw [MatchIndexProjection.filter_candidates possible selected complete, collect_filter decode selected irrelevant]

/-- Later appends, removals and rewrites cannot change a projection of an
already detached input view. No equality of the later store is required. -/
theorem detached_selection (before after : CapturedRowReaders.Store Row)
    (cursor : CapturedRowReaders.Cursor Row) (saved : List Row)
    (current : CapturedRowReaders.rows before cursor = some saved) (selected : Row → Bool) :
    (CapturedRowReaders.remaining after {cursor with owned := some saved}).map (List.filter selected) =
      (CapturedRowReaders.remaining before cursor).map (List.filter selected) := by
  rw [CapturedRowReaders.detached_remaining before after cursor saved current]

private def decodePositive (row : Nat) : Except Nat (List Nat) :=
  if row == 0 then .ok [] else if row == 3 then .error row else .ok [row]

example : collect decodePositive [1,0,1,2] = .ok [1,1,2] := by decide +kernel
example : collect decodePositive [1,3,2,3] = .error 3 := by decide +kernel
example : collect decodePositive [3,2] ≠ collect decodePositive [2] := by decide +kernel

end Mettapedia.Machines.SelectiveRowCapture

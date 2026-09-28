import Mettapedia.Machines.Cursor.Sequence

/-!
# Preparing structural summaries for retained tails

An immutable sequence can prepare every suffix summary in one right-to-left
pass. Each subsequent tail uses an array lookup instead of rescanning its
children. The construction works for any right fold: associativity, inverse
operations, and commutativity are not required.

The cache belongs to the sequence and its fixed logical end. It does not
answer arbitrary bounded-window queries. Nor does it justify caching facts
that depend on mutable bindings without checking their dependencies.

The work meter counts summary-combiner calls and later lookups. Array
construction, allocation, ownership, and the cost inside a combiner remain
implementation obligations; the theorem does not predict wall time.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.SuffixSummary

variable {Item Summary : Type}

structure Prepared (Summary : Type) where
  current : Summary
  tails : List Summary
  combines : Nat
  deriving Repr

def prepare (combine : Item → Summary → Summary) (empty : Summary) :
    List Item → Prepared Summary
  | [] => ⟨empty, [], 0⟩
  | item :: rest =>
      let suffix := prepare combine empty rest
      ⟨combine item suffix.current, suffix.current :: suffix.tails, suffix.combines + 1⟩

def entries (prepared : Prepared Summary) : List Summary :=
  prepared.current :: prepared.tails

theorem prepare_current (combine : Item → Summary → Summary) (empty : Summary)
    (items : List Item) :
    (prepare combine empty items).current = items.foldr combine empty := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [prepare, ih]

theorem prepare_combines (combine : Item → Summary → Summary) (empty : Summary)
    (items : List Item) :
    (prepare combine empty items).combines = items.length := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [prepare, ih]

theorem entries_length (combine : Item → Summary → Summary) (empty : Summary)
    (items : List Item) :
    (entries (prepare combine empty items)).length = items.length + 1 := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      change ((prepare combine empty rest).tails.length + 1) + 1 = rest.length + 1 + 1
      exact congrArg (· + 1) ih

theorem entries_at (combine : Item → Summary → Summary) (empty : Summary)
    (items : List Item) (offset : Nat) (within : offset ≤ items.length) :
    (entries (prepare combine empty items))[offset]? =
      some ((items.drop offset).foldr combine empty) := by
  induction items generalizing offset with
  | nil =>
      have zero : offset = 0 := by simpa using within
      subst offset
      rfl
  | cons item rest ih =>
      cases offset with
      | zero => simp [entries, prepare_current]
      | succ offset =>
          change (entries (prepare combine empty rest))[offset]? =
            some ((rest.drop offset).foldr combine empty)
          exact ih offset (by simpa using within)

/-- A single array stores all suffix summaries, including the empty suffix. -/
def cache (combine : Item → Summary → Summary) (empty : Summary)
    (items : List Item) : Array Summary :=
  (entries (prepare combine empty items)).toArray

theorem cache_size (combine : Item → Summary → Summary) (empty : Summary)
    (items : List Item) :
    (cache combine empty items).size = items.length + 1 := by
  simpa [cache] using entries_length combine empty items

theorem cache_at (combine : Item → Summary → Summary) (empty : Summary)
    (items : List Item) (offset : Nat) (within : offset ≤ items.length) :
    (cache combine empty items)[offset]? =
      some ((items.drop offset).foldr combine empty) := by
  simpa [cache] using entries_at combine empty items offset within

theorem cache_past_end (combine : Item → Summary → Summary) (empty : Summary)
    (items : List Item) (offset : Nat) (past : items.length < offset) :
    (cache combine empty items)[offset]? = none := by
  apply Array.getElem?_eq_none_iff.mpr
  rw [cache_size]
  omega

/-- Offset views whose logical end is the end used to build the cache. -/
def tailView (storage : Array Item) (offset : Nat) : Sequence.Slice Item :=
  ⟨storage, offset, storage.size - offset⟩

theorem cached_tail_summary (combine : Item → Summary → Summary) (empty : Summary)
    (storage : Array Item) (offset : Nat) (within : offset ≤ storage.size) :
    (cache combine empty storage.toList)[offset]? =
      some (((Sequence.sliceHom Item).map (base := ()) (index := ())
        (tailView storage offset)).foldr combine empty) := by
  rw [cache_at combine empty storage.toList offset (by simpa using within)]
  have whole : (storage.toList.drop offset).take (storage.size - offset) =
      storage.toList.drop offset := by
    simp only [← Array.length_toList, ← List.length_drop, List.take_length]
  simp [Sequence.sliceHom, tailView, whole]

/-- One preparation plus one lookup per selected tail, including early stops. -/
theorem preparation_and_queries (combine : Item → Summary → Summary) (empty : Summary)
    (items : List Item) (queries : Nat) :
    (prepare combine empty items).combines + queries = items.length + queries := by
  rw [prepare_combines]

theorem one_pass_queries_bound (combine : Item → Summary → Summary) (empty : Summary)
    (items : List Item) (queries : Nat) (within : queries ≤ items.length + 1) :
    (prepare combine empty items).combines + queries ≤ 2 * items.length + 1 := by
  rw [prepare_combines]
  omega

namespace Controls

theorem cached_flags_remove_the_departed_child :
    (cache (fun item rest => item || rest) false [true, false])[1]? = some false := by decide

theorem empty_suffix_has_the_identity_summary :
    (cache (· + ·) 0 [3, 3, 5])[3]? = some 0 := by decide

/-- A suffix cache cannot answer a window ending before the cached sequence ends. -/
theorem bounded_window_needs_its_own_end :
    (cache (fun item rest => item || rest) false [false, true])[0]? ≠
      some (([false, true].take 1).foldr (fun item rest => item || rest) false) := by decide

/-- Equality of syntax does not license reusing a binding-dependent summary. -/
theorem changed_classifier_can_change_summary :
    (cache (fun (item : Nat) rest => (item == 7) || rest) false [7])[0]? ≠
      (cache (fun (item : Nat) rest => (item == 8) || rest) false [7])[0]? := by decide

end Controls

#print axioms entries_at
#print axioms cache_at
#print axioms cached_tail_summary
#print axioms one_pass_queries_bound

end Mettapedia.Machines.Cursor.SuffixSummary

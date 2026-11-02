import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# Linear grouping of adjacent equal-key occurrences

Grouping retains every input occurrence and its order. A bucket has a first
occurrence, so its key never requires a default value. On a key-sorted input,
the bucket keys are strictly increasing. The construction compares adjacent
keys once and builds shared list spines; it does not filter the input again
for each distinct key.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ContiguousKeyRuns

variable {Row Key : Type*}

structure Bucket (Row : Type*) where
  first : Row
  rest : List Row
  deriving Repr, DecidableEq

def Bucket.rows (bucket : Bucket Row) : List Row := bucket.first :: bucket.rest

structure Result (Row : Type*) where
  buckets : List (Bucket Row)
  comparisons : Nat
  deriving Repr, DecidableEq

def prepend [DecidableEq Key] (key : Row → Key) (row : Row) (result : Result Row) : Result Row :=
  match result.buckets with
  | [] => ⟨[⟨row, []⟩], result.comparisons⟩
  | bucket :: rest =>
      if key row = key bucket.first then
        ⟨⟨row, bucket.rows⟩ :: rest, result.comparisons + 1⟩
      else ⟨⟨row, []⟩ :: bucket :: rest, result.comparisons + 1⟩

def group [DecidableEq Key] (key : Row → Key) : List Row → Result Row
  | [] => ⟨[], 0⟩
  | row :: rest => prepend key row (group key rest)

def flatten (buckets : List (Bucket Row)) : List Row := buckets.flatMap Bucket.rows

theorem flatten_prepend [DecidableEq Key] (key : Row → Key) (row : Row) (result : Result Row) :
    flatten (prepend key row result).buckets = row :: flatten result.buckets := by
  unfold prepend
  split
  · simp_all [flatten, Bucket.rows]
  · split <;> simp_all [flatten, Bucket.rows]

theorem flatten_group [DecidableEq Key] (key : Row → Key) (rows : List Row) :
    flatten (group key rows).buckets = rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih => rw [group, flatten_prepend, ih]

theorem group_empty_iff [DecidableEq Key] (key : Row → Key) (rows : List Row) :
    (group key rows).buckets = [] ↔ rows = [] := by
  constructor
  · intro empty
    have exactRows := flatten_group key rows
    simpa [empty, flatten] using exactRows.symm
  · rintro rfl
    rfl

theorem group_comparisons [DecidableEq Key] (key : Row → Key) (rows : List Row) :
    (group key rows).comparisons = rows.length - 1 := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      rw [group, prepend]
      split
      next empty =>
        have emptyRows := (group_empty_iff key rest).mp empty
        subst rest
        rfl
      next bucket later shape =>
        have nonemptyRows : rest ≠ [] := by
          intro empty
          subst rest
          cases shape
        have positive := List.length_pos_iff.mpr nonemptyRows
        split <;> simp only [List.length_cons] <;> omega

def Homogeneous (key : Row → Key) (bucket : Bucket Row) : Prop :=
  ∀ row ∈ bucket.rows, key row = key bucket.first

theorem group_homogeneous [DecidableEq Key] (key : Row → Key) (rows : List Row) :
    ∀ bucket ∈ (group key rows).buckets, Homogeneous key bucket := by
  induction rows with
  | nil => simp [group]
  | cons row rest ih =>
      intro bucket member
      rw [group, prepend] at member
      split at member
      next empty =>
        have same := List.mem_singleton.mp member
        subst bucket
        simp [Homogeneous, Bucket.rows]
      next first later shape =>
        split at member
        next equal =>
          rcases List.mem_cons.mp member with same | member
          · subst bucket
            intro item inRows
            rcases List.mem_cons.mp inRows with same | inRows
            · subst item; rfl
            · exact (ih first (by simp [shape]) item inRows).trans equal.symm
          · exact ih bucket (by simp [shape, member])
        next different =>
          rcases List.mem_cons.mp member with same | member
          · subst bucket
            simp [Homogeneous, Bucket.rows]
          · exact ih bucket (by simpa [shape] using member)

theorem bucket_first_mem {buckets : List (Bucket Row)} {bucket : Bucket Row}
    (member : bucket ∈ buckets) : bucket.first ∈ flatten buckets := by
  exact List.mem_flatMap.mpr ⟨bucket, member, by simp [Bucket.rows]⟩

theorem group_keys_sorted [LinearOrder Key] (key : Row → Key) (rows : List Row)
    (sorted : rows.Pairwise (fun left right => key left ≤ key right)) :
    (group key rows).buckets.Pairwise (fun left right => key left.first < key right.first) := by
  induction rows with
  | nil => simp [group]
  | cons row rest ih =>
      have ordered := List.pairwise_cons.mp sorted
      have tailSorted := ih ordered.2
      rw [group, prepend]
      split
      next empty => simp
      next bucket later shape =>
        have headMem : bucket.first ∈ rest := by
          rw [← flatten_group key rest]
          exact bucket_first_mem (by simp [shape])
        have lower := ordered.1 bucket.first headMem
        have tailOrder : (bucket :: later).Pairwise
            (fun left right => key left.first < key right.first) := by simpa [shape] using tailSorted
        split
        next equal =>
          apply List.pairwise_cons.mpr
          refine ⟨?_, (List.pairwise_cons.mp tailOrder).2⟩
          intro other member
          simpa only [equal] using (List.pairwise_cons.mp tailOrder).1 other member
        next different =>
          apply List.pairwise_cons.mpr
          refine ⟨?_, tailOrder⟩
          intro other member
          have strict := lt_of_le_of_ne lower different
          rcases List.mem_cons.mp member with same | member
          · subst other; exact strict
          · exact strict.trans ((List.pairwise_cons.mp tailOrder).1 other member)

theorem group_rows_count [DecidableEq Key] (key : Row → Key) (rows : List Row) :
    ((group key rows).buckets.map (fun bucket => bucket.rows.length)).sum = rows.length := by
  have same := congrArg List.length (flatten_group key rows)
  simpa [flatten, List.length_flatMap] using same

theorem group_bucket_count [DecidableEq Key] (key : Row → Key) (rows : List Row) :
    (group key rows).buckets.length ≤ rows.length := by
  have summed := List.sum_le_sum (l := (group key rows).buckets)
    (f := fun _ => 1) (g := fun bucket => bucket.rows.length)
    (fun bucket _ => by simp [Bucket.rows])
  simpa [group_rows_count, List.map_const', List.sum_replicate] using summed

/-- All occurrences in a homogeneous bucket agree on the selected key. -/
theorem filter_bucket [DecidableEq Key] (key : Row → Key) (target : Key) (bucket : Bucket Row)
    (homogeneous : Homogeneous key bucket) :
    bucket.rows.filter (fun row => decide (key row = target)) =
      if key bucket.first = target then bucket.rows else [] := by
  by_cases same : key bucket.first = target
  · rw [if_pos same]
    apply List.filter_eq_self.mpr
    intro row member
    exact decide_eq_true (homogeneous row member |>.trans same)
  · rw [if_neg same]
    apply List.filter_eq_nil_iff.mpr
    intro row member
    simpa only [decide_eq_true_eq] using
      (show key row ≠ target from fun equal => same ((homogeneous row member).symm.trans equal))

theorem filter_flatten_empty [DecidableEq Key] (key : Row → Key) (target : Key)
    (buckets : List (Bucket Row))
    (homogeneous : ∀ bucket ∈ buckets, Homogeneous key bucket)
    (missing : ∀ bucket ∈ buckets, key bucket.first ≠ target) :
    (flatten buckets).filter (fun row => decide (key row = target)) = [] := by
  induction buckets with
  | nil => rfl
  | cons bucket rest ih =>
      change (bucket.rows ++ flatten rest).filter _ = _
      rw [List.filter_append, filter_bucket key target bucket (homogeneous bucket (by simp)),
        if_neg (missing bucket (by simp)), List.nil_append]
      exact ih (fun other member => homogeneous other (by simp [member]))
        (fun other member => missing other (by simp [member]))

theorem find_bucket_exact [LinearOrder Key] (key : Row → Key) (target : Key)
    (buckets : List (Bucket Row))
    (sorted : buckets.Pairwise (fun left right => key left.first < key right.first))
    (homogeneous : ∀ bucket ∈ buckets, Homogeneous key bucket) :
    ((buckets.find? (fun bucket => decide (key bucket.first = target))).map Bucket.rows).getD [] =
      (flatten buckets).filter (fun row => decide (key row = target)) := by
  induction buckets with
  | nil => rfl
  | cons bucket rest ih =>
      have ordered := List.pairwise_cons.mp sorted
      have restHomogeneous : ∀ other ∈ rest, Homogeneous key other :=
        fun other member => homogeneous other (by simp [member])
      change (((bucket :: rest).find? _).map Bucket.rows).getD [] =
        (bucket.rows ++ flatten rest).filter _
      rw [List.filter_append, filter_bucket key target bucket (homogeneous bucket (by simp))]
      by_cases same : key bucket.first = target
      · have empty := filter_flatten_empty key target rest restHomogeneous (by
          intro other member equal
          have strict := ordered.1 other member
          simp [same, equal] at strict)
        simp [same, empty]
      · simpa [same] using ih ordered.2 restHomogeneous

theorem find_group_exact [LinearOrder Key] (key : Row → Key) (target : Key) (rows : List Row)
    (sorted : rows.Pairwise (fun left right => key left ≤ key right)) :
    (((group key rows).buckets.find? (fun bucket => decide (key bucket.first = target))).map
      Bucket.rows).getD [] = rows.filter (fun row => decide (key row = target)) := by
  rw [find_bucket_exact key target _ (group_keys_sorted key rows sorted) (group_homogeneous key rows),
    flatten_group]

namespace Controls

def occurrences : List (Nat × Nat) := [(1, 10), (1, 11), (2, 12), (4, 13), (4, 14)]

theorem duplicate_occurrences_retained :
    ((group Prod.fst occurrences).buckets.map Bucket.rows) =
      [[(1, 10), (1, 11)], [(2, 12)], [(4, 13), (4, 14)]] := by decide +kernel

theorem one_comparison_per_boundary :
    (group Prod.fst occurrences).comparisons = 4 := by decide +kernel

theorem unsorted_repeated_key_stays_separate :
    ((group (id : Nat → Nat) [1, 2, 1]).buckets.map Bucket.first) = [1, 2, 1] := by decide +kernel

theorem unsorted_keys_fail_navigation_admission :
    ¬((group (id : Nat → Nat) [1, 2, 1]).buckets.map Bucket.first).Pairwise (· < ·) := by decide +kernel

end Controls

end Mettapedia.Machines.Cursor.ContiguousKeyRuns

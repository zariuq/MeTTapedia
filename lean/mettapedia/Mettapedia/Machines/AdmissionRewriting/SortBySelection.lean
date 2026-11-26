import Mettapedia.Machines.AdmissionRewriting.MinMaxSelection

/-!
# Sorting with CeTTa's `min` and `max`, and the term orders the rule leaves open

CeTTa's `min` and `max` select an operand (`MinMaxSelection`): by exact value, the first NaN
operand if any, `min` answering its first operand on a tie and `max` its second, so
`(min a b, max a b)` is the stable sort of `(a, b)`. This file asks what sorts built from the
rule compute, and what the rule says about an order of terms.

**Sorts made of the rule.** Selection sort by the rule (`selSort`: the `selMin`-fold of the
list, which is its leftmost minimum (`foldl_selMin_split`), then the sort of the list with that
occurrence removed) and insertion sort by compare-exchange (`ceSort`: `(selMin, selMax)` on
neighbours) are the stable sort by value on every input without NaN (`selSort_eq`,
`ceSort_eq`), which is both `List.insertionSort` and `List.mergeSort` by value
(`selSort_eq_mergeSort`, `mergeSort_eq_insertionSort_byKey`): the order of values, then input
position (`selSort_eq_zipIdx`). NaN propagates through the rule. Selection sort puts the NaN
operands first, in input order, and permutes its input (`selSort_nan`, `selSort_perm`).
Selection sort from the top (`selSortTop`: the `selMax`-fold, the rightmost maximum
(`foldl_selMax_split`), placed last) is the stable sort too (`selSortTop_eq`), but puts NaN last
(`selSortTop_nan`): where NaN goes is the algorithm's choice
(`Controls.nan_place_by_algorithm`). Insertion sort by compare-exchange answers NaN at every
place, so beside a number it is no permutation (`ceSort_nan`, `ceSort_not_perm`).

**Comparator networks** (`Comparator`, `runNet`) permute every input without NaN
(`runNet_perm`). A network of neighbouring comparators is stable (`runNet_blocks`), so one
whose output is sorted is the stable sort (`runNet_eq_insertionSort`); the insertion network is
one, and it is insertion sort by compare-exchange (`runNet_insertionNet`, `insertionNet_eq`).
Every network whose output is sorted has the stable sort's value at every place
(`runNet_values`), but which of two tied operands comes first depends on the network: the
3-wire network `[(0,2), (0,1), (1,2)]` sorts every input (`net3_sorts`), yet answers
`[0, 1.0, 1]` on `[1, 1.0, 0]`, where the insertion network and the stable sort answer
`[0, 1, 1.0]` (`Controls.networks_differ`). A sort built from `min` and `max` does not fix the
order of ties by itself.

**No term order comes out of the rule.** Selection sort, insertion sort by compare-exchange,
and every comparator network leave both `[1, 1.0]` and `[1.0, 1]` as they are, so no
antisymmetric relation sorts all their outputs (`no_order_from_rule`,
`Controls.tie_fixed_points`): the rule gives the order of values and input position, and input
position is no order of terms.

**What the rule asks of an order.** The sort by a relation answers the rule's `(min, max)` on
every two numbers of different values exactly when the relation puts the lower value first and
not the higher one (`pairsByRule_iff`); nothing is asked about numbers of one value, nor about
NaN. A term order on numbers as the spec states it (`IsNumberOrder`: total, equal only on
identical numbers, transitive, value-consistent, NaN at one fixed place) answers the rule's
pairs (`IsNumberOrder.pairs`); its sort has the stable sort's values at every place, and is the
stable sort exactly when each block of one value of the input is already in its order
(`IsNumberOrder.sort_values`, `IsNumberOrder.sort_blocks`, `IsNumberOrder.sort_eq_stable_iff`).
SWI-Prolog's standard order of numbers (`swiLE`: NaN first, then by value, then among numbers of
one value `-0.0`, the other doubles, the integer), the integer-first order (`intFirstLE`) and
SWI's tie-break with NaN last (`NaNLastLE`) are all such orders (`swi_isNumberOrder`,
`intFirst_isNumberOrder`, `nanLast_isNumberOrder`), and they differ
(`Controls.tie_break_free`): the tie-break among numbers of one value, and the place of NaN, are
the implementation's choice. On `[1, 1.0]` SWI's sort answers `[1.0, 1]` and the stable sort
`[1, 1.0]`; on `[1.0, 1]` they agree (`Controls.swi_vs_stable`).

**ISO's order** (`isoLE`, as in GNU Prolog and SICStus: every double before every integer,
each by value) is not value-consistent, putting `-1.0` before `-9`
(`iso_not_value_consistent`), so no sort that answers the rule's pairs is ISO's sort
(`iso_disagrees`, `iso_not_pairsByRule`).

**SWI's tie-break is ISO's order used as the second key.** SWI's strict order is the order by
value, then by ISO's order, with `-0.0` before `0.0`, the one pair those two leave tied
(`swiLT_iff`, `valueThenIso_total`). A double below an integer in value, ISO and value agree; an
integer below a double, they conflict and SWI follows value; at one value, value leaves the pair
free and ISO puts the double first, as SWI does (`iso_against_value`). On numbers that are not
NaN, SWI's is the only total, antisymmetric, value-consistent order that follows ISO wherever ISO
does not contradict value, on every pair but the zeros (`swi_unique`), and with `-0.0` first, as
IEEE 754's `totalOrder` puts it, on every pair (`swi_unique_of_zeros`, `swi_zeros`); it meets
each of these conditions (`swi_satisfies`). Any other tie-break breaks ISO on a pair that value leaves free
(`tie_break_breaks_iso`): the integer-first order puts `1` before `1.0`
(`Controls.intFirst_breaks_iso`).

`Binary64Order` reads binary64 patterns as numbers, proves that SourceTermOrder's comparison of
the Prolog heap's number constants is `swiLE`, and compares SWI's order of floats with IEEE
754's `totalOrder`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting.SortBySelection

open MinMaxSWI (XR ofQ Dbl Num isNaN)
open MinMaxSWI.Controls (dq)
open MinMaxSelection (valOf selMin selMax)

theorem ofQ_injective : Function.Injective ofQ := fun _ _ h =>
  WithTop.coe_injective (WithBot.coe_injective h)

theorem isNaN_eq_true {x : Num} (h : isNaN x = true) : x = .flt .nan := by
  rcases x with _ | (_ | _ | _) <;> first | rfl | simp [isNaN] at h

/-! ## Stable sorting by a key -/

section Key

variable {α β : Type*} [LinearOrder β] (key : α → β)

/-- **Two sorted lists with the same blocks are one list**: lists sorted by a key, in which the
elements of each key come in the same order, are equal. -/
theorem eq_of_sorted_of_blocks {s t : List α} (hs : s.Pairwise (fun a b => key a ≤ key b))
    (ht : t.Pairwise (fun a b => key a ≤ key b))
    (h : ∀ k, s.filter (fun a => key a = k) = t.filter (fun a => key a = k)) : s = t := by
  induction s generalizing t with
  | nil =>
    cases t with
    | nil => rfl
    | cons y t => simpa using h (key y)
  | cons x s ih =>
    cases t with
    | nil => simpa using h (key x)
    | cons y t =>
      rw [List.pairwise_cons] at hs ht
      have below {u : List α} {z w : α} (hu : ∀ c ∈ u, key z ≤ key c)
          (hw : w ∈ (z :: u).filter (fun a => key a = key w)) : key z ≤ key w := by
        rw [List.mem_filter, List.mem_cons] at hw
        rcases hw.1 with rfl | hw
        · exact le_rfl
        · exact hu w hw
      have hyx : key y ≤ key x := below ht.1 (by rw [← h]; simp)
      have hxy : key x ≤ key y := below hs.1 (by rw [h]; simp)
      have hk : key y = key x := le_antisymm hyx hxy
      have hx := h (key x)
      simp only [List.filter_cons, hk, decide_true, if_true, List.cons.injEq] at hx
      obtain ⟨rfl, hx⟩ := hx
      refine congrArg _ (ih hs.2 ht.2 fun k => ?_)
      by_cases hkx : key x = k
      · subst hkx
        exact hx
      · simpa [List.filter_cons, hkx] using h k

theorem sorted_insertionSort (l : List α) :
    (l.insertionSort (fun a b => key a ≤ key b)).Pairwise (fun a b => key a ≤ key b) := by
  have : Std.Total (fun a b : α => key a ≤ key b) := ⟨fun a b => le_total (key a) (key b)⟩
  have : IsTrans α (fun a b : α => key a ≤ key b) := ⟨fun _ _ _ => le_trans⟩
  exact List.pairwise_insertionSort _ l

theorem sorted_mergeSort (l : List α) :
    (l.mergeSort (fun a b => decide (key a ≤ key b))).Pairwise (fun a b => key a ≤ key b) := by
  simpa using List.pairwise_mergeSort (le := fun a b => decide (key a ≤ key b))
    (fun _ _ _ hab hbc => by simpa using le_trans (by simpa using hab) (by simpa using hbc))
    (fun a b => by simpa using le_total (key a) (key b)) l

/-- The elements of one key, in input order, are in every list sorted by the key. -/
theorem block_pairwise (l : List α) (k : β) :
    (l.filter (fun a => key a = k)).Pairwise (fun a b => key a ≤ key b) :=
  List.pairwise_of_forall_mem_list fun a ha b hb => by
    rw [List.mem_filter, decide_eq_true_eq] at ha hb
    rw [ha.2, hb.2]

/-- A sublist of a list with one block length, holding that block, is that block. -/
theorem blocks_of_sublist {l s : List α} (hp : s.Perm l) (k : β)
    (hsub : List.Sublist (l.filter (fun a => key a = k)) s) :
    s.filter (fun a => key a = k) = l.filter (fun a => key a = k) := by
  have h1 := hsub.filter (fun a => decide (key a = k))
  simp only [List.filter_filter, Bool.and_self] at h1
  exact (h1.eq_of_length ((hp.filter _).length_eq).symm).symm

/-- **Insertion sort by a key is stable**: it keeps the elements of each key in input order. -/
theorem insertionSort_blocks (l : List α) (k : β) :
    (l.insertionSort (fun a b => key a ≤ key b)).filter (fun a => key a = k) =
      l.filter (fun a => key a = k) :=
  blocks_of_sublist key (List.perm_insertionSort _ l) k
    (List.sublist_insertionSort (block_pairwise key l k) List.filter_sublist)

/-- **Merge sort by a key is stable.** -/
theorem mergeSort_blocks (l : List α) (k : β) :
    (l.mergeSort (fun a b => decide (key a ≤ key b))).filter (fun a => key a = k) =
      l.filter (fun a => key a = k) :=
  blocks_of_sublist key (List.mergeSort_perm l _) k
    (List.sublist_mergeSort
      (fun _ _ _ hab hbc => by simpa using le_trans (by simpa using hab) (by simpa using hbc))
      (fun a b => by simpa using le_total (key a) (key b))
      (by simpa using block_pairwise key l k) List.filter_sublist)

/-- **The stable sort by a key is the one sorted list with the input's blocks.** -/
theorem eq_insertionSort_of_sorted {s l : List α} (hs : s.Pairwise (fun a b => key a ≤ key b))
    (hb : ∀ k, s.filter (fun a => key a = k) = l.filter (fun a => key a = k)) :
    s = l.insertionSort (fun a b => key a ≤ key b) :=
  eq_of_sorted_of_blocks key hs (sorted_insertionSort key l)
    fun k => (hb k).trans (insertionSort_blocks key l k).symm

/-- Merge sort and insertion sort by a key agree, ties included. -/
theorem mergeSort_eq_insertionSort_byKey (l : List α) :
    l.mergeSort (fun a b => decide (key a ≤ key b)) =
      l.insertionSort (fun a b => key a ≤ key b) :=
  eq_insertionSort_of_sorted key (sorted_mergeSort key l) (mergeSort_blocks key l)

/-- Insertion sort by a key puts an element last when nothing before it is above it and
everything after it is below it. -/
theorem insertionSort_extract_last {s t : List α} {m : α} (hs : ∀ x ∈ s, key x ≤ key m)
    (ht : ∀ x ∈ t, key x < key m) :
    (s ++ m :: t).insertionSort (fun a b => key a ≤ key b) =
      (s ++ t).insertionSort (fun a b => key a ≤ key b) ++ [m] := by
  have hle : ∀ x ∈ (s ++ t).insertionSort (fun a b => key a ≤ key b), key x ≤ key m := by
    intro x hx
    rcases List.mem_append.mp ((List.perm_insertionSort _ _).mem_iff.mp hx) with hx | hx
    · exact hs x hx
    · exact (ht x hx).le
  refine (eq_insertionSort_of_sorted key ?_ fun k => ?_).symm
  · exact List.pairwise_append.mpr ⟨sorted_insertionSort key _, List.pairwise_singleton _ _,
      fun x hx y hy => by rw [List.mem_singleton.mp hy]; exact hle x hx⟩
  · rw [List.filter_append, insertionSort_blocks]
    by_cases hk : key m = k
    · have htk : t.filter (fun a => key a = k) = [] := List.filter_eq_nil_iff.mpr fun x hx => by
        simpa [← hk] using (ht x hx).ne
      simp [List.filter_append, hk, htk]
    · simp [List.filter_append, hk]

end Key

/-- Insertion sort takes an element out in front of a list when everything before it is not
below it and it is below everything after it. -/
theorem insertionSort_extract {α : Type*} {r : α → α → Prop} [DecidableRel r]
    {s t : List α} {m : α} (hs : ∀ x ∈ s, ¬ r x m) (ht : ∀ x ∈ t, r m x) :
    (s ++ m :: t).insertionSort r = m :: (s ++ t).insertionSort r := by
  induction s with
  | nil => exact List.insertionSort_cons_of_forall_rel r ht
  | cons x s ih =>
    simp only [List.cons_append, List.insertionSort_cons]
    rw [ih fun y hy => hs y (List.mem_cons_of_mem _ hy)]
    exact List.orderedInsert_of_not_le r _ (hs x List.mem_cons_self)

/-! ## Sorts made of the rule -/

section Rule

variable {α : Type} (num : α → Num)

/-- The `selMin`-fold regroups: `selMin` is associative. -/
theorem foldl_selMin_cons (a b : α) (l : List α) :
    (b :: l).foldl (selMin num) a = selMin num a (l.foldl (selMin num) b) :=
  @List.foldl_assoc _ _ ⟨MinMaxSelection.selMin_assoc num⟩ l a b

theorem foldl_selMin_mem (a : α) (l : List α) : l.foldl (selMin num) a ∈ a :: l := by
  induction l generalizing a with
  | nil => exact List.mem_cons_self
  | cons b l ih =>
    rw [foldl_selMin_cons]
    rcases MinMaxSelection.selMin_mem num a (l.foldl (selMin num) b) with h | h <;> rw [h]
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih b)

/-- **The `selMin`-fold is the leftmost minimum**: on operands that are not NaN it answers an
occurrence strictly below everything before it and at most everything after it. -/
theorem foldl_selMin_split (a : α) (l : List α) (h : ∀ x ∈ a :: l, isNaN (num x) = false) :
    ∃ s t, a :: l = s ++ l.foldl (selMin num) a :: t ∧
      (∀ x ∈ s, valOf (num (l.foldl (selMin num) a)) < valOf (num x)) ∧
      ∀ x ∈ t, valOf (num (l.foldl (selMin num) a)) ≤ valOf (num x) := by
  induction l generalizing a with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons b l ih =>
    obtain ⟨s, t, hst, hs, ht⟩ := ih b fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hle : ∀ x ∈ b :: l, valOf (num (l.foldl (selMin num) b)) ≤ valOf (num x) := by
      intro x hx
      rw [hst, List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact (hs x hx).le
      · exact le_rfl
      · exact ht x hx
    have hm := h _ (List.mem_cons_of_mem _ (foldl_selMin_mem num b l))
    rw [foldl_selMin_cons, MinMaxSelection.selMin_eq_le_test num (h a List.mem_cons_self) hm]
    split_ifs with ham
    · exact ⟨[], b :: l, rfl, by simp, fun x hx => ham.trans (hle x hx)⟩
    · refine ⟨a :: s, t, by rw [hst]; rfl, ?_, ht⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact not_le.mp ham
      · exact hs x hx

/-- A NaN accumulator absorbs the `selMin`-fold. -/
theorem foldl_selMin_of_nan_acc {acc : α} (hacc : isNaN (num acc) = true) (l : List α) :
    l.foldl (selMin num) acc = acc := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have : selMin num acc b = acc := by simp [selMin, hacc]
    rw [List.foldl_cons, this, ih]

/-- **The `selMin`-fold answers the first NaN**, when there is one. -/
theorem foldl_selMin_of_nan {acc n : α} {s : List α} (hacc : isNaN (num acc) = false)
    (hs : ∀ x ∈ s, isNaN (num x) = false) (hn : isNaN (num n) = true) (t : List α) :
    (s ++ n :: t).foldl (selMin num) acc = n := by
  induction s generalizing acc with
  | nil =>
    have : selMin num acc n = n := by simp [selMin, hacc, hn]
    rw [List.nil_append, List.foldl_cons, this, foldl_selMin_of_nan_acc num hn]
  | cons x s ih =>
    rw [List.cons_append, List.foldl_cons]
    apply ih _ fun y hy => hs y (List.mem_cons_of_mem _ hy)
    rw [MinMaxSelection.selMin_nan, hacc, hs x List.mem_cons_self]
    rfl

/-- The `selMax`-fold regroups: `selMax` is associative. -/
theorem foldl_selMax_cons (a b : α) (l : List α) :
    (b :: l).foldl (selMax num) a = selMax num a (l.foldl (selMax num) b) :=
  @List.foldl_assoc _ _ ⟨MinMaxSelection.selMax_assoc num⟩ l a b

theorem foldl_selMax_mem (a : α) (l : List α) : l.foldl (selMax num) a ∈ a :: l := by
  induction l generalizing a with
  | nil => exact List.mem_cons_self
  | cons b l ih =>
    rw [foldl_selMax_cons]
    rcases MinMaxSelection.selMax_mem num a (l.foldl (selMax num) b) with h | h <;> rw [h]
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih b)

/-- **The `selMax`-fold is the rightmost maximum**: on operands that are not NaN it answers an
occurrence at least everything before it and strictly above everything after it. -/
theorem foldl_selMax_split (a : α) (l : List α) (h : ∀ x ∈ a :: l, isNaN (num x) = false) :
    ∃ s t, a :: l = s ++ l.foldl (selMax num) a :: t ∧
      (∀ x ∈ s, valOf (num x) ≤ valOf (num (l.foldl (selMax num) a))) ∧
      ∀ x ∈ t, valOf (num x) < valOf (num (l.foldl (selMax num) a)) := by
  induction l generalizing a with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons b l ih =>
    obtain ⟨s, t, hst, hs, ht⟩ := ih b fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hle : ∀ x ∈ b :: l, valOf (num x) ≤ valOf (num (l.foldl (selMax num) b)) := by
      intro x hx
      rw [hst, List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact hs x hx
      · exact le_rfl
      · exact (ht x hx).le
    have hm := h _ (List.mem_cons_of_mem _ (foldl_selMax_mem num b l))
    rw [foldl_selMax_cons, MinMaxSelection.selMax_eq_le_test num (h a List.mem_cons_self) hm]
    split_ifs with ham
    · refine ⟨a :: s, t, by rw [hst]; rfl, ?_, ht⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ham
      · exact hs x hx
    · exact ⟨[], b :: l, rfl, by simp, fun x hx => (hle x hx).trans_lt (not_le.mp ham)⟩

section SelectionSort

/-- The `selMin`-fold of `a :: l`: CeTTa's `min` of a nonempty list. -/
def minOf (a : α) (l : List α) : α := l.foldl (selMin num) a

theorem minOf_mem (a : α) (l : List α) : minOf num a l ∈ a :: l := foldl_selMin_mem num a l

/-- The `selMax`-fold of `a :: l`: CeTTa's `max` of a nonempty list. -/
def maxOf (a : α) (l : List α) : α := l.foldl (selMax num) a

theorem maxOf_mem (a : α) (l : List α) : maxOf num a l ∈ a :: l := foldl_selMax_mem num a l

variable [DecidableEq α]

/-- **Selection sort by the rule**: the `selMin`-fold of the list, its leftmost minimum, then
the sort of the list with that occurrence removed. -/
def selSort : List α → List α
  | [] => []
  | a :: l => minOf num a l :: selSort ((a :: l).erase (minOf num a l))
termination_by l => l.length
decreasing_by
  rw [List.length_erase_of_mem (minOf_mem num a l)]
  simp

/-- **Selection sort by the rule is the stable sort by value** on every input without NaN. -/
theorem selSort_eq (l : List α) (h : ∀ x ∈ l, isNaN (num x) = false) :
    selSort num l = l.insertionSort (fun a b => valOf (num a) ≤ valOf (num b)) := by
  induction l using selSort.induct num with
  | case1 => simp [selSort]
  | case2 a l ih =>
    rw [selSort, minOf]
    obtain ⟨s, t, hst, hs, ht⟩ := foldl_selMin_split num a l h
    have hms : l.foldl (selMin num) a ∉ s := fun hm => lt_irrefl _ (hs _ hm)
    have herase : (a :: l).erase (l.foldl (selMin num) a) = s ++ t := by
      rw [hst, List.erase_append_right _ hms, List.erase_cons_head]
    rw [minOf] at ih
    rw [ih fun x hx => h x (List.mem_of_mem_erase hx), herase, hst,
      insertionSort_extract (r := fun a b => valOf (num a) ≤ valOf (num b))
        (fun x hx => not_le.mpr (hs x hx)) ht]

/-- Selection sort by the rule is merge sort by value. -/
theorem selSort_eq_mergeSort (l : List α) (h : ∀ x ∈ l, isNaN (num x) = false) :
    selSort num l = l.mergeSort (fun a b => decide (valOf (num a) ≤ valOf (num b))) := by
  rw [selSort_eq num l h, mergeSort_eq_insertionSort_byKey (fun a => valOf (num a))]

/-- **The value preorder, then input position**: selection sort by the rule is the sort of the
input's occurrences by value and then by position. -/
theorem selSort_eq_zipIdx (l : List α) (h : ∀ x ∈ l, isNaN (num x) = false) :
    selSort num l =
      (l.zipIdx.mergeSort (List.zipIdxLE fun a b => decide (valOf (num a) ≤ valOf (num b)))).map
        (·.1) := by
  rw [List.mergeSort_zipIdx, selSort_eq_mergeSort num l h]

/-- **Selection sort by the rule puts NaN first**: the NaN operands in input order, then the
stable sort by value of the rest. -/
theorem selSort_nan (l : List α) :
    selSort num l = l.filter (fun x => isNaN (num x)) ++
      (l.filter (fun x => !isNaN (num x))).insertionSort
        (fun a b => valOf (num a) ≤ valOf (num b)) := by
  induction l using selSort.induct num with
  | case1 => simp [selSort]
  | case2 a l ih =>
    by_cases hn : ∃ x ∈ a :: l, isNaN (num x) = true
    · obtain ⟨n, hfind⟩ : ∃ n, (a :: l).find? (fun x => isNaN (num x)) = some n := by
        rcases hf : (a :: l).find? (fun x => isNaN (num x)) with _ | n
        · rw [List.find?_eq_none] at hf
          obtain ⟨x, hx, hxn⟩ := hn
          exact absurd hxn (hf x hx)
        · exact ⟨n, rfl⟩
      obtain ⟨hnn, s, t, hst, hs⟩ := List.find?_eq_some_iff_append.mp hfind
      have hs' : ∀ x ∈ s, isNaN (num x) = false := fun x hx => by simpa using hs x hx
      have hfold : l.foldl (selMin num) a = n := by
        cases s with
        | nil =>
          rw [List.nil_append, List.cons.injEq] at hst
          obtain ⟨rfl, rfl⟩ := hst
          exact foldl_selMin_of_nan_acc num hnn l
        | cons x s =>
          rw [List.cons_append, List.cons.injEq] at hst
          obtain ⟨rfl, rfl⟩ := hst
          exact foldl_selMin_of_nan num (hs' a List.mem_cons_self)
            (fun y hy => hs' y (List.mem_cons_of_mem _ hy)) hnn t
      have hns : n ∉ s := fun hm => by simp [hs' n hm] at hnn
      have herase : (a :: l).erase n = s ++ t := by
        rw [hst, List.erase_append_right _ hns, List.erase_cons_head]
      have hsn : s.filter (fun x => isNaN (num x)) = [] :=
        List.filter_eq_nil_iff.mpr fun x hx => by simp [hs' x hx]
      have hsn' : s.filter (fun x => !isNaN (num x)) = s :=
        List.filter_eq_self.mpr fun x hx => by simp [hs' x hx]
      rw [minOf] at ih
      rw [selSort, minOf, ih, hfold, herase, hst]
      simp [List.filter_append, hnn, hsn, hsn']
    · have h : ∀ x ∈ a :: l, isNaN (num x) = false := fun x hx => by
        simpa using fun h' => hn ⟨x, hx, h'⟩
      rw [selSort_eq num (a :: l) h, List.filter_eq_nil_iff.mpr fun x hx => by simp [h x hx],
        List.filter_eq_self.mpr fun x hx => by simp [h x hx], List.nil_append]

/-- Selection sort by the rule permutes its input, NaN included. -/
theorem selSort_perm (l : List α) : (selSort num l).Perm l := by
  rw [selSort_nan]
  exact ((List.perm_insertionSort _ _).append_left _).trans (List.filter_append_perm _ l)

/-- A list with the last occurrence of `a` removed. -/
def eraseLast (l : List α) (a : α) : List α := (l.reverse.erase a).reverse

theorem eraseLast_split {s t : List α} {m : α} (hm : m ∉ t) : eraseLast (s ++ m :: t) m = s ++ t := by
  unfold eraseLast
  rw [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append,
    List.erase_append_right _ (by simpa using hm), List.erase_cons_head, List.reverse_append,
    List.reverse_reverse, List.reverse_reverse]

theorem length_eraseLast {l : List α} {a : α} (h : a ∈ l) : (eraseLast l a).length = l.length - 1 := by
  unfold eraseLast
  rw [List.length_reverse, List.length_erase_of_mem (List.mem_reverse.mpr h), List.length_reverse]

/-- **Selection sort from the top**: the `selMax`-fold of the list, its rightmost maximum, goes
last, after the sort of the list with that occurrence removed. -/
def selSortTop : List α → List α
  | [] => []
  | a :: l => selSortTop (eraseLast (a :: l) (maxOf num a l)) ++ [maxOf num a l]
termination_by l => l.length
decreasing_by
  rw [length_eraseLast (maxOf_mem num a l)]
  simp

/-- **Selection sort from the top is the stable sort by value** on every input without NaN. -/
theorem selSortTop_eq (l : List α) (h : ∀ x ∈ l, isNaN (num x) = false) :
    selSortTop num l = l.insertionSort (fun a b => valOf (num a) ≤ valOf (num b)) := by
  induction l using selSortTop.induct num with
  | case1 => simp [selSortTop]
  | case2 a l ih =>
    rw [selSortTop, maxOf]
    obtain ⟨s, t, hst, hs, ht⟩ := foldl_selMax_split num a l h
    have hmt : l.foldl (selMax num) a ∉ t := fun hm => lt_irrefl _ (ht _ hm)
    have herase : eraseLast (a :: l) (l.foldl (selMax num) a) = s ++ t := by
      rw [hst, eraseLast_split hmt]
    rw [maxOf] at ih
    rw [ih fun x hx => h x (by
        unfold eraseLast at hx
        exact List.mem_reverse.mp (List.mem_of_mem_erase (List.mem_reverse.mp hx))),
      herase, hst, insertionSort_extract_last (fun a => valOf (num a)) hs ht]

end SelectionSort

/-- A NaN accumulator absorbs the `selMax`-fold. -/
theorem foldl_selMax_of_nan_acc {acc : α} (hacc : isNaN (num acc) = true) (l : List α) :
    l.foldl (selMax num) acc = acc := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have : selMax num acc b = acc := by simp [selMax, hacc]
    rw [List.foldl_cons, this, ih]

/-- The `selMax`-fold answers the first NaN, as the `selMin`-fold does. -/
theorem foldl_selMax_of_nan {acc n : α} {s : List α} (hacc : isNaN (num acc) = false)
    (hs : ∀ x ∈ s, isNaN (num x) = false) (hn : isNaN (num n) = true) (t : List α) :
    (s ++ n :: t).foldl (selMax num) acc = n := by
  induction s generalizing acc with
  | nil =>
    have : selMax num acc n = n := by simp [selMax, hacc, hn]
    rw [List.nil_append, List.foldl_cons, this, foldl_selMax_of_nan_acc num hn t]
  | cons x s ih =>
    rw [List.cons_append, List.foldl_cons]
    apply ih _ fun y hy => hs y (List.mem_cons_of_mem _ hy)
    rw [MinMaxSelection.selMax_nan, hacc, hs x List.mem_cons_self]
    rfl

/-- **Selection sort from the top puts NaN last**: on numbers it answers the stable sort by
value of the numbers that are not NaN, then the NaNs. -/
theorem selSortTop_nan (l : List Num) :
    selSortTop id l = (l.filter (fun x => !isNaN x)).insertionSort (fun a b => valOf a ≤ valOf b) ++
      l.filter (fun x => isNaN x) := by
  induction l using selSortTop.induct id with
  | case1 => simp [selSortTop]
  | case2 a l ih =>
    by_cases hn : ∃ x ∈ a :: l, isNaN x = true
    · have hfold : maxOf id a l = .flt .nan := by
        obtain ⟨n, hfind⟩ : ∃ n, (a :: l).find? (fun x => isNaN x) = some n := by
          rcases hf : (a :: l).find? (fun x => isNaN x) with _ | n
          · rw [List.find?_eq_none] at hf
            obtain ⟨x, hx, hxn⟩ := hn
            exact absurd hxn (hf x hx)
          · exact ⟨n, rfl⟩
        obtain ⟨hnn, s, t, hst, hs⟩ := List.find?_eq_some_iff_append.mp hfind
        have hs' : ∀ x ∈ s, isNaN (id x) = false := fun x hx => by simpa using hs x hx
        rw [← isNaN_eq_true hnn]
        unfold maxOf
        cases s with
        | nil =>
          rw [List.nil_append, List.cons.injEq] at hst
          obtain ⟨rfl, rfl⟩ := hst
          exact foldl_selMax_of_nan_acc id hnn _
        | cons x s =>
          rw [List.cons_append, List.cons.injEq] at hst
          obtain ⟨rfl, rfl⟩ := hst
          exact foldl_selMax_of_nan id (hs' a List.mem_cons_self)
            (fun y hy => hs' y (List.mem_cons_of_mem _ hy)) hnn t
      obtain ⟨n, hfind⟩ : ∃ n, (a :: l).reverse.find? (fun x => isNaN x) = some n := by
        rcases hf : (a :: l).reverse.find? (fun x => isNaN x) with _ | n
        · rw [List.find?_eq_none] at hf
          obtain ⟨x, hx, hxn⟩ := hn
          exact absurd hxn (hf x (List.mem_reverse.mpr hx))
        · exact ⟨n, rfl⟩
      obtain ⟨hnn, u, w, huw, hu⟩ := List.find?_eq_some_iff_append.mp hfind
      have hnan : n = .flt .nan := isNaN_eq_true hnn
      subst hnan
      have hsplit : a :: l = w.reverse ++ .flt .nan :: u.reverse := by
        rw [← List.reverse_reverse (a :: l), huw]
        simp
      have hu' : ∀ x ∈ u.reverse, isNaN x = false := fun x hx => by
        simpa using hu x (List.mem_reverse.mp hx)
      have hmu : Num.flt .nan ∉ u.reverse := fun hm => absurd (hu' _ hm) (by decide)
      rw [selSortTop, ih, hfold, hsplit, eraseLast_split hmu]
      have hun : u.reverse.filter (fun x => isNaN x) = [] :=
        List.filter_eq_nil_iff.mpr fun x hx => by simp [hu' x hx]
      have hun' : u.reverse.filter (fun x => !isNaN x) = u.reverse :=
        List.filter_eq_self.mpr fun x hx => by simp [hu' x hx]
      have hnanT : isNaN (Num.flt .nan) = true := rfl
      simp [List.filter_append, hun, hun', hnanT]
    · have h : ∀ x ∈ a :: l, isNaN x = false := fun x hx => by
        cases hx' : isNaN x
        · rfl
        · exact absurd ⟨x, hx, hx'⟩ hn
      rw [selSortTop_eq id (a :: l) h,
        List.filter_eq_nil_iff (p := fun x => isNaN x).mpr fun x hx => by simp [h x hx],
        List.filter_eq_self (p := fun x => !isNaN x).mpr fun x hx => by simp [h x hx],
        List.append_nil]
      rfl

/-- **Insertion by compare-exchange**: `x` meets each element in turn; `selMin` stays, `selMax`
moves on. -/
def ceInsert (x : α) : List α → List α
  | [] => [x]
  | y :: l => selMin num x y :: ceInsert (selMax num x y) l

/-- **Insertion sort by compare-exchange.** -/
def ceSort : List α → List α
  | [] => []
  | a :: l => ceInsert num a (ceSort l)

/-- On a sorted list without NaN, insertion by compare-exchange is insertion by value. -/
theorem ceInsert_eq {x : α} {s : List α} (hx : isNaN (num x) = false)
    (hs : ∀ y ∈ s, isNaN (num y) = false)
    (hsort : s.Pairwise (fun a b => valOf (num a) ≤ valOf (num b))) :
    ceInsert num x s = s.orderedInsert (fun a b => valOf (num a) ≤ valOf (num b)) x := by
  induction s generalizing x with
  | nil => rfl
  | cons y s ih =>
    have hy := hs y List.mem_cons_self
    have hs' := fun z hz => hs z (List.mem_cons_of_mem y hz)
    rw [List.pairwise_cons] at hsort
    simp only [ceInsert, List.orderedInsert_cons]
    rw [MinMaxSelection.selMin_eq_le_test num hx hy, MinMaxSelection.selMax_eq_le_test num hx hy]
    split_ifs with hxy
    · rw [ih hy hs' hsort.2]
      cases s with
      | nil => rfl
      | cons z s =>
        rw [List.orderedInsert_cons_of_le (fun a b => valOf (num a) ≤ valOf (num b)) s
          (hsort.1 z List.mem_cons_self)]
    · rw [ih hx hs' hsort.2]

/-- **Insertion sort by compare-exchange is the stable sort by value** on every input without
NaN. -/
theorem ceSort_eq (l : List α) (h : ∀ x ∈ l, isNaN (num x) = false) :
    ceSort num l = l.insertionSort (fun a b => valOf (num a) ≤ valOf (num b)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h' := fun x hx => h x (List.mem_cons_of_mem a hx)
    rw [ceSort, List.insertionSort_cons, ih h',
      ceInsert_eq num (h a List.mem_cons_self)
        (fun y hy => h' y ((List.perm_insertionSort _ l).mem_iff.mp hy))
        (sorted_insertionSort (fun a => valOf (num a)) l)]

theorem length_ceInsert (x : α) (s : List α) : (ceInsert num x s).length = s.length + 1 := by
  induction s generalizing x with
  | nil => rfl
  | cons y s ih => simp [ceInsert, ih]

theorem length_ceSort (l : List α) : (ceSort num l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ceSort, length_ceInsert, ih]

/-- A NaN inserted by compare-exchange makes every place NaN. -/
theorem ceInsert_of_nan {x : α} (hx : isNaN (num x) = true) (s : List α) :
    ∀ y ∈ ceInsert num x s, isNaN (num y) = true := by
  induction s generalizing x with
  | nil => simpa [ceInsert] using hx
  | cons z s ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [MinMaxSelection.selMin_nan, hx, Bool.true_or]
    · exact ih (by rw [MinMaxSelection.selMax_nan, hx, Bool.true_or]) y hy

/-- **A NaN anywhere makes insertion sort by compare-exchange answer NaN everywhere.** -/
theorem ceSort_nan (l : List α) (h : ∃ x ∈ l, isNaN (num x) = true) :
    ∀ y ∈ ceSort num l, isNaN (num y) = true := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : isNaN (num a) = true
    · exact ceInsert_of_nan num ha _
    · obtain ⟨x, hx, hxn⟩ := h
      have hxl : x ∈ l := by
        rcases List.mem_cons.mp hx with rfl | hxl
        · exact absurd hxn ha
        · exact hxl
      have hl := ih ⟨x, hxl, hxn⟩
      have hne : ceSort num l ≠ [] := by
        intro he
        have := length_ceSort num l
        rw [he] at this
        exact List.ne_nil_of_mem hxl (List.length_eq_zero_iff.mp this.symm)
      obtain ⟨z, s, hzs⟩ := List.exists_cons_of_ne_nil hne
      have hz : isNaN (num z) = true := hl z (by rw [hzs]; exact List.mem_cons_self)
      intro y hy
      simp only [ceSort, hzs, ceInsert, List.mem_cons] at hy
      rcases hy with rfl | hy
      · rw [MinMaxSelection.selMin_nan, hz, Bool.or_true]
      · exact ceInsert_of_nan num (by rw [MinMaxSelection.selMax_nan, hz, Bool.or_true]) s y hy

/-- **With NaN, insertion sort by compare-exchange is no permutation**: a NaN beside any
number loses the number. -/
theorem ceSort_not_perm (l : List α) (hn : ∃ x ∈ l, isNaN (num x) = true)
    (hm : ∃ x ∈ l, isNaN (num x) = false) : ¬ (ceSort num l).Perm l := by
  intro hp
  obtain ⟨x, hx, hxm⟩ := hm
  have := ceSort_nan num l hn x (hp.mem_iff.mpr hx)
  rw [hxm] at this
  exact Bool.false_ne_true this

end Rule

/-! ## Comparator networks -/

/-- A comparator: compare-exchange of the wires `lo < hi`. -/
structure Comparator where
  lo : ℕ
  hi : ℕ
  lo_lt_hi : lo < hi

/-- A comparator of neighbouring wires. -/
def Comparator.Adjacent (c : Comparator) : Prop := c.hi = c.lo + 1

/-- Swapping two places of a list permutes it. -/
theorem set_set_perm {α : Type*} (l : List α) {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (hij : i ≠ j) : ((l.set i l[j]).set j l[i]).Perm l := by
  have key : (l.set i l[j]).set j l[i] =
      List.ofFn ((fun k : Fin l.length => l[k.1]) ∘ Equiv.swap ⟨i, hi⟩ ⟨j, hj⟩) := by
    apply List.ext_getElem (by simp)
    intro k hk hk'
    simp only [List.getElem_set, List.getElem_ofFn, Function.comp, Equiv.swap_apply_def,
      Fin.ext_iff]
    by_cases hjk : j = k
    · subst hjk
      simp [Ne.symm hij]
    · by_cases hik : i = k
      · subst hik
        simp [hjk]
      · simp [hjk, hik, Ne.symm hjk, Ne.symm hik]
  rw [key]
  exact (Equiv.Perm.ofFn_comp_perm _ _).trans (by rw [List.ofFn_getElem])

/-- A list with two neighbouring places `i` and `i + 1`. -/
theorem exists_split_two {α : Type*} {l : List α} {i : ℕ} (h : i + 1 < l.length) :
    ∃ l₁ x y l₂, l = l₁ ++ x :: y :: l₂ ∧ l₁.length = i := by
  refine ⟨l.take i, l[i], l[i + 1], l.drop (i + 2), ?_, by simp; omega⟩
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons h]

section Network

variable {α : Type} (num : α → Num)

/-- **A comparator's run**: `selMin` of its two wires to `lo`, `selMax` to `hi`; a comparator
past the end of the list leaves it. -/
def Comparator.run (c : Comparator) (l : List α) : List α :=
  if h : c.hi < l.length then
    (l.set c.lo (selMin num (l[c.lo]'(c.lo_lt_hi.trans h)) l[c.hi])).set c.hi
      (selMax num (l[c.lo]'(c.lo_lt_hi.trans h)) l[c.hi])
  else l

/-- **A comparator network's run**: its comparators in order. -/
def runNet (net : List Comparator) (l : List α) : List α :=
  net.foldl (fun l c => c.run num l) l

theorem Comparator.run_of_lt (c : Comparator) {l : List α} (h : c.hi < l.length) :
    c.run num l = (l.set c.lo (selMin num (l[c.lo]'(c.lo_lt_hi.trans h)) l[c.hi])).set c.hi
      (selMax num (l[c.lo]'(c.lo_lt_hi.trans h)) l[c.hi]) := by
  rw [Comparator.run, dif_pos h]

theorem Comparator.run_of_le (c : Comparator) {l : List α} (h : ¬ c.hi < l.length) :
    c.run num l = l := by
  rw [Comparator.run, dif_neg h]

theorem runNet_cons (c : Comparator) (net : List Comparator) (l : List α) :
    runNet num (c :: net) l = runNet num net (c.run num l) := rfl

/-- **On operands without NaN a comparator permutes its input**: it keeps its two wires, or
swaps them where the second is strictly below the first. -/
theorem Comparator.run_perm (c : Comparator) {l : List α}
    (h : ∀ x ∈ l, isNaN (num x) = false) : (c.run num l).Perm l := by
  by_cases hl : c.hi < l.length
  · have hlo : c.lo < l.length := c.lo_lt_hi.trans hl
    rw [Comparator.run_of_lt num c hl]
    have hss := MinMaxSelection.stable_sort num (h _ (List.getElem_mem hlo))
      (h _ (List.getElem_mem hl))
    split_ifs at hss
    · simp only [Prod.mk.injEq] at hss
      rw [hss.1, hss.2]
      exact set_set_perm l hlo hl c.lo_lt_hi.ne
    · simp only [Prod.mk.injEq] at hss
      rw [hss.1, hss.2, List.set_getElem_self, List.set_getElem_self]
  · rw [Comparator.run_of_le num c hl]

/-- A neighbouring comparator compare-exchanges the two neighbours in place. -/
theorem Comparator.run_adjacent {c : Comparator} (hc : c.Adjacent) (l₁ l₂ : List α) (x y : α)
    (hlen : l₁.length = c.lo) :
    c.run num (l₁ ++ x :: y :: l₂) = l₁ ++ selMin num x y :: selMax num x y :: l₂ := by
  obtain ⟨lo, hi, hlt⟩ := c
  simp only [Comparator.Adjacent] at hc
  subst hc hlen
  have h : l₁.length + 1 < (l₁ ++ x :: y :: l₂).length := by simp
  rw [Comparator.run_of_lt num _ h]
  simp [List.getElem_append_right, List.set_append_right]

/-- **A neighbouring comparator keeps every block**: on operands without NaN it swaps only
neighbours of different values. -/
theorem Comparator.run_blocks {c : Comparator} (hc : c.Adjacent) {l : List α}
    (h : ∀ x ∈ l, isNaN (num x) = false) (v : XR) :
    (c.run num l).filter (fun x => valOf (num x) = v) = l.filter (fun x => valOf (num x) = v) := by
  by_cases hl : c.hi < l.length
  · obtain ⟨l₁, x, y, l₂, rfl, hlen⟩ := exists_split_two (hc ▸ hl : c.lo + 1 < l.length)
    rw [Comparator.run_adjacent num hc l₁ l₂ x y hlen]
    have hss := MinMaxSelection.stable_sort num (h x (by simp)) (h y (by simp))
    split_ifs at hss with hyx
    · simp only [Prod.mk.injEq] at hss
      rw [hss.1, hss.2]
      simp only [List.filter_append, List.filter_cons]
      by_cases hxv : valOf (num x) = v
      · have hyv : valOf (num y) ≠ v := fun e => (e.trans hxv.symm ▸ hyx).false
        simp [hxv, hyv]
      · by_cases hyv : valOf (num y) = v <;> simp [hxv, hyv]
    · simp only [Prod.mk.injEq] at hss
      rw [hss.1, hss.2]
  · rw [Comparator.run_of_le num c hl]

/-- **On operands without NaN every comparator network permutes its input.** -/
theorem runNet_perm (net : List Comparator) {l : List α} (h : ∀ x ∈ l, isNaN (num x) = false) :
    (runNet num net l).Perm l := by
  induction net generalizing l with
  | nil => exact List.Perm.refl l
  | cons c net ih =>
    have hp := c.run_perm num h
    exact (ih fun x hx => h x (hp.mem_iff.mp hx)).trans hp

/-- **Networks of neighbouring comparators are stable**: on operands without NaN they keep the
operands of each value in input order. -/
theorem runNet_blocks {net : List Comparator} (hnet : ∀ c ∈ net, c.Adjacent) {l : List α}
    (h : ∀ x ∈ l, isNaN (num x) = false) (v : XR) :
    (runNet num net l).filter (fun x => valOf (num x) = v) =
      l.filter (fun x => valOf (num x) = v) := by
  induction net generalizing l with
  | nil => rfl
  | cons c net ih =>
    have hp := c.run_perm num h
    rw [runNet_cons, ih (fun c hc => hnet c (List.mem_cons_of_mem _ hc))
      (fun x hx => h x (hp.mem_iff.mp hx)),
      Comparator.run_blocks num (hnet c List.mem_cons_self) h]

/-- **A sorting network of neighbouring comparators is the stable sort by value**: wherever its
output is sorted by value, on operands without NaN, it is the stable sort. -/
theorem runNet_eq_insertionSort {net : List Comparator} (hnet : ∀ c ∈ net, c.Adjacent)
    {l : List α} (h : ∀ x ∈ l, isNaN (num x) = false)
    (hsort : (runNet num net l).Pairwise (fun a b => valOf (num a) ≤ valOf (num b))) :
    runNet num net l = l.insertionSort (fun a b => valOf (num a) ≤ valOf (num b)) :=
  eq_insertionSort_of_sorted (fun a => valOf (num a)) hsort (runNet_blocks num hnet h)

/-- **Every sorting network has the stable sort's values**: wherever a network's output is
sorted by value, on operands without NaN, it has the stable sort's value at every place; only
the order of operands of one value can differ. -/
theorem runNet_values (net : List Comparator) {l : List α} (h : ∀ x ∈ l, isNaN (num x) = false)
    (hsort : (runNet num net l).Pairwise (fun a b => valOf (num a) ≤ valOf (num b))) :
    (runNet num net l).map (fun x => valOf (num x)) =
      (l.insertionSort (fun a b => valOf (num a) ≤ valOf (num b))).map (fun x => valOf (num x)) :=
  List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
    (List.pairwise_map.mpr hsort)
    (List.pairwise_map.mpr (sorted_insertionSort (fun a => valOf (num a)) l))
    (((runNet_perm num net h).trans (List.perm_insertionSort _ l).symm).map _)

/-- **Every network leaves a tie of two as it is**: on two operands of one value, neither NaN,
each comparator in range answers them in place. -/
theorem runNet_tie (net : List Comparator) {x y : α} (hx : isNaN (num x) = false)
    (hy : isNaN (num y) = false) (hv : valOf (num x) = valOf (num y)) :
    runNet num net [x, y] = [x, y] := by
  induction net with
  | nil => rfl
  | cons c net ih =>
    rw [runNet_cons]
    convert ih using 2
    by_cases hc : c.hi < 2
    · obtain ⟨lo, hi, hlt⟩ := c
      obtain rfl : hi = 1 := by simp only at hc; omega
      obtain rfl : lo = 0 := by omega
      have hss := MinMaxSelection.stable_sort num hx hy
      rw [if_neg (by rw [hv]; exact lt_irrefl _), Prod.mk.injEq] at hss
      rw [Comparator.run_of_lt num _ (by simp)]
      simp [hss.1, hss.2]
    · exact Comparator.run_of_le num c (by simpa using hc)

/-- A comparator one wire further on. -/
def Comparator.shift (c : Comparator) : Comparator :=
  ⟨c.lo + 1, c.hi + 1, Nat.succ_lt_succ c.lo_lt_hi⟩

/-- The pass `(0,1), (1,2), …, (n-1,n)`: compare-exchange insertion of wire `0`. -/
def passNet : ℕ → List Comparator
  | 0 => []
  | n + 1 => ⟨0, 1, Nat.zero_lt_one⟩ :: (passNet n).map Comparator.shift

/-- **The insertion network on `n` wires**: the network of the last `n - 1` wires, then the pass
that inserts wire `0`. -/
def insertionNet : ℕ → List Comparator
  | 0 => []
  | n + 1 => (insertionNet n).map Comparator.shift ++ passNet n

theorem Comparator.run_shift (c : Comparator) (a : α) (l : List α) :
    c.shift.run num (a :: l) = a :: c.run num l := by
  by_cases h : c.hi < l.length
  · rw [Comparator.run_of_lt num c.shift (by simp [Comparator.shift]; omega),
      Comparator.run_of_lt num c h]
    simp [Comparator.shift]
  · rw [Comparator.run_of_le num c.shift (by simp [Comparator.shift]; omega),
      Comparator.run_of_le num c h]

theorem runNet_shift (net : List Comparator) (a : α) (l : List α) :
    runNet num (net.map Comparator.shift) (a :: l) = a :: runNet num net l := by
  induction net generalizing l with
  | nil => rfl
  | cons c net ih =>
    rw [List.map_cons, runNet_cons, Comparator.run_shift, ih]
    rfl

theorem runNet_passNet (x : α) (s : List α) :
    runNet num (passNet s.length) (x :: s) = ceInsert num x s := by
  induction s generalizing x with
  | nil => rfl
  | cons y s ih =>
    have h01 := Comparator.run_adjacent num (c := ⟨0, 1, Nat.zero_lt_one⟩) rfl [] s x y rfl
    rw [List.nil_append, List.nil_append] at h01
    rw [List.length_cons, passNet, runNet_cons, h01, runNet_shift, ih]
    rfl

/-- **Insertion sort by compare-exchange is the insertion network.** -/
theorem runNet_insertionNet (l : List α) : runNet num (insertionNet l.length) l = ceSort num l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, insertionNet, runNet, List.foldl_append, ← runNet, ← runNet,
      runNet_shift, ih, ← length_ceSort num l, runNet_passNet]
    rfl

theorem passNet_adjacent (n : ℕ) : ∀ c ∈ passNet n, c.Adjacent := by
  induction n with
  | zero => simp [passNet]
  | succ n ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · rfl
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      exact congrArg (· + 1) (ih d hd)

/-- The insertion network has neighbouring comparators only. -/
theorem insertionNet_adjacent (n : ℕ) : ∀ c ∈ insertionNet n, c.Adjacent := by
  induction n with
  | zero => simp [insertionNet]
  | succ n ih =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      exact congrArg (· + 1) (ih d hd)
    · exact passNet_adjacent n c hc

/-- **The insertion network is the stable sort by value** on every input without NaN: a network
of neighbouring comparators that sorts. -/
theorem insertionNet_eq (l : List α) (h : ∀ x ∈ l, isNaN (num x) = false) :
    runNet num (insertionNet l.length) l =
      l.insertionSort (fun a b => valOf (num a) ≤ valOf (num b)) := by
  rw [runNet_insertionNet, ceSort_eq num l h]

/-- A 3-wire sorting network with a comparator of wires that are not neighbours. -/
def net3 : List Comparator := [⟨0, 2, by decide⟩, ⟨0, 1, by decide⟩, ⟨1, 2, by decide⟩]

/-- The 3-wire insertion network, of neighbouring comparators. -/
def insertion3 : List Comparator := [⟨1, 2, by decide⟩, ⟨0, 1, by decide⟩, ⟨1, 2, by decide⟩]

theorem runNet_net3 (a b c : α) :
    runNet num net3 [a, b, c] =
      [selMin num (selMin num a c) b,
        selMin num (selMax num (selMin num a c) b) (selMax num a c),
        selMax num (selMax num (selMin num a c) b) (selMax num a c)] := rfl

theorem insertion3_eq : insertion3 = insertionNet 3 := rfl

/-- The 3-wire insertion network is insertion sort by compare-exchange. -/
theorem runNet_insertion3 (a b c : α) : runNet num insertion3 [a, b, c] = ceSort num [a, b, c] :=
  runNet_insertionNet num [a, b, c]

theorem insertion3_adjacent : ∀ c ∈ insertion3, c.Adjacent := by
  simp [insertion3, Comparator.Adjacent]

theorem net3_not_adjacent : ¬ ∀ c ∈ net3, c.Adjacent := fun h =>
  absurd (h ⟨0, 2, by decide⟩ (by simp [net3])) (by simp [Comparator.Adjacent])

/-- **The 3-wire network sorts every input without NaN**, by value. -/
theorem net3_sorts {a b c : α} (ha : isNaN (num a) = false) (hb : isNaN (num b) = false)
    (hc : isNaN (num c) = false) :
    (runNet num net3 [a, b, c]).Pairwise (fun x y => valOf (num x) ≤ valOf (num y)) := by
  have hac : isNaN (num (selMin num a c)) = false := by
    rw [MinMaxSelection.selMin_nan, ha, hc]; rfl
  have hac' : isNaN (num (selMax num a c)) = false := by
    rw [MinMaxSelection.selMax_nan, ha, hc]; rfl
  have hacb : isNaN (num (selMax num (selMin num a c) b)) = false := by
    rw [MinMaxSelection.selMax_nan, hac, hb]; rfl
  rw [runNet_net3]
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true]
  rw [MinMaxSelection.valOf_selMin num hac hb, MinMaxSelection.valOf_selMin num hacb hac',
    MinMaxSelection.valOf_selMax num hacb hac', MinMaxSelection.valOf_selMax num hac hb,
    MinMaxSelection.valOf_selMin num ha hc, MinMaxSelection.valOf_selMax num ha hc]
  have h1 : min (min (valOf (num a)) (valOf (num c))) (valOf (num b)) ≤
      min (max (min (valOf (num a)) (valOf (num c))) (valOf (num b)))
        (max (valOf (num a)) (valOf (num c))) :=
    le_min (min_le_left _ _ |>.trans (le_max_left _ _))
      (min_le_left _ _ |>.trans (min_le_left _ _) |>.trans (le_max_left _ _))
  exact ⟨⟨h1, h1.trans min_le_max⟩, min_le_max, fun _ h => h.elim⟩

end Network

/-! ## No term order comes out of positional ties -/

section NoOrder

variable {α : Type} (num : α → Num)

/-- **Positional ties make no order**: a sort that leaves both `[x, y]` and `[y, x]` as they
are, for two different operands, sorts by no antisymmetric relation. -/
theorem no_order_of_ties (sort : List α → List α) {x y : α} (hxy : x ≠ y)
    (h1 : sort [x, y] = [x, y]) (h2 : sort [y, x] = [y, x]) (R : α → α → Prop)
    (hR : ∀ a b, R a b → R b a → a = b) :
    ¬ ((sort [x, y]).Pairwise R ∧ (sort [y, x]).Pairwise R) := by
  rintro ⟨hxy', hyx'⟩
  rw [h1, List.pairwise_pair] at hxy'
  rw [h2, List.pairwise_pair] at hyx'
  exact hxy (hR x y hxy' hyx')

/-- The stable sort by value leaves a tie of two as it is. -/
theorem stable_tie {x y : α} (hv : valOf (num x) = valOf (num y)) :
    [x, y].insertionSort (fun a b => valOf (num a) ≤ valOf (num b)) = [x, y] := by
  simp [hv]

/-- **No sort made of the rule sorts by a term order**: given two different operands of one
value, neither NaN, no antisymmetric relation sorts every output of selection sort by the rule,
of insertion sort by compare-exchange, or of any comparator network. -/
theorem no_order_from_rule [DecidableEq α] {x y : α} (hxy : x ≠ y) (hx : isNaN (num x) = false)
    (hy : isNaN (num y) = false) (hv : valOf (num x) = valOf (num y)) (R : α → α → Prop)
    (hR : ∀ a b, R a b → R b a → a = b) :
    ¬ (∀ l, (∀ z ∈ l, isNaN (num z) = false) → (selSort num l).Pairwise R) ∧
      ¬ (∀ l, (∀ z ∈ l, isNaN (num z) = false) → (ceSort num l).Pairwise R) ∧
      ∀ net : List Comparator,
        ¬ ∀ l, (∀ z ∈ l, isNaN (num z) = false) → (runNet num net l).Pairwise R := by
  have hxy2 : ∀ z ∈ [x, y], isNaN (num z) = false := by simp [hx, hy]
  have hyx2 : ∀ z ∈ [y, x], isNaN (num z) = false := by simp [hx, hy]
  refine ⟨fun h => ?_, fun h => ?_, fun net h => ?_⟩
  · exact no_order_of_ties (selSort num) hxy
      ((selSort_eq num _ hxy2).trans (stable_tie num hv))
      ((selSort_eq num _ hyx2).trans (stable_tie num hv.symm)) R hR ⟨h _ hxy2, h _ hyx2⟩
  · exact no_order_of_ties (ceSort num) hxy
      ((ceSort_eq num _ hxy2).trans (stable_tie num hv))
      ((ceSort_eq num _ hyx2).trans (stable_tie num hv.symm)) R hR ⟨h _ hxy2, h _ hyx2⟩
  · exact no_order_of_ties (runNet num net) hxy (runNet_tie num net hx hy hv)
      (runNet_tie num net hy hx hv.symm) R hR ⟨h _ hxy2, h _ hyx2⟩

end NoOrder

/-! ## What the rule asks of an order -/

section Pairs

variable {α : Type} (num : α → Num)

/-- **A sort answers the rule's pairs**: on two operands of different values, neither NaN, it
answers the rule's `(min, max)`. -/
def PairsByRule (sort : List α → List α) : Prop :=
  ∀ x y, isNaN (num x) = false → isNaN (num y) = false → valOf (num x) ≠ valOf (num y) →
    sort [x, y] = [selMin num x y, selMax num x y]

theorem insertionSort_pair (T : α → α → Prop) [DecidableRel T] (x y : α) :
    [x, y].insertionSort T = if T x y then [x, y] else [y, x] := by
  by_cases h : T x y <;> simp [h]

/-- The stable sort answers the rule's `(min, max)` on every pair without NaN, ties included. -/
theorem stable_pair {x y : α} (hx : isNaN (num x) = false) (hy : isNaN (num y) = false) :
    [x, y].insertionSort (fun a b => valOf (num a) ≤ valOf (num b)) =
      [selMin num x y, selMax num x y] := by
  rw [insertionSort_pair, MinMaxSelection.selMin_eq_le_test num hx hy,
    MinMaxSelection.selMax_eq_le_test num hx hy]
  split_ifs <;> rfl

theorem selSort_pairs [DecidableEq α] : PairsByRule num (selSort num) := fun x y hx hy _ =>
  (selSort_eq num [x, y] (by simp [hx, hy])).trans (stable_pair num hx hy)

theorem ceSort_pairs : PairsByRule num (ceSort num) := fun x y hx hy _ =>
  (ceSort_eq num [x, y] (by simp [hx, hy])).trans (stable_pair num hx hy)

/-- **What the rule asks of an order**: the `T`-sort of every two operands of different values,
neither NaN, is the rule's `(min, max)` exactly when `T` puts the lower value first and not the
higher one. Nothing else about `T` is asked: not totality, not antisymmetry, not the order of
equal values, not the place of NaN. -/
theorem pairsByRule_iff (T : α → α → Prop) [DecidableRel T] :
    PairsByRule num (List.insertionSort T) ↔
      ∀ x y, isNaN (num x) = false → isNaN (num y) = false → valOf (num x) < valOf (num y) →
        T x y ∧ ¬ T y x := by
  constructor
  · intro h x y hx hy hlt
    have hne : x ≠ y := fun e => lt_irrefl _ (e ▸ hlt)
    have h1 := h x y hx hy hlt.ne
    have h2 := h y x hy hx hlt.ne'
    rw [insertionSort_pair, MinMaxSelection.selMin_eq_le_test num hx hy,
      MinMaxSelection.selMax_eq_le_test num hx hy, if_pos hlt.le, if_pos hlt.le] at h1
    rw [insertionSort_pair, MinMaxSelection.selMin_eq_le_test num hy hx,
      MinMaxSelection.selMax_eq_le_test num hy hx, if_neg (not_le.mpr hlt),
      if_neg (not_le.mpr hlt)] at h2
    refine ⟨by_contra fun hT => ?_, fun hT => ?_⟩
    · rw [if_neg hT, List.cons.injEq] at h1
      exact hne h1.1.symm
    · rw [if_pos hT, List.cons.injEq] at h2
      exact hne h2.1.symm
  · intro h x y hx hy hne
    rw [insertionSort_pair, MinMaxSelection.selMin_eq_le_test num hx hy,
      MinMaxSelection.selMax_eq_le_test num hx hy]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [if_pos (h x y hx hy hlt).1, if_pos hlt.le, if_pos hlt.le]
    · rw [if_neg (h y x hy hx hlt).2, if_neg (not_le.mpr hlt), if_neg (not_le.mpr hlt)]

end Pairs

/-! ## Orders on numbers -/

section Numbers

/-- The place SWI gives a number among the numbers of its value: `-0.0`, then the other
doubles, then the integer. -/
def swiRank : Num → ℕ
  | .flt .negZero => 0
  | .flt _ => 1
  | .int _ => 2

/-- The integer-first place: the integer, then `-0.0`, then the other doubles. -/
def intRank : Num → ℕ
  | .int _ => 0
  | .flt .negZero => 1
  | .flt _ => 2

/-- The key of an order on numbers: NaN first, then the value, then a rank among the numbers of
one value. -/
def rankKey (rank : Num → ℕ) (x : Num) : WithBot (Lex (XR × ℕ)) :=
  if isNaN x then ⊥ else ↑(toLex (valOf x, rank x))

/-- The order of a rank key. -/
def RankLE (rank : Num → ℕ) (x y : Num) : Prop := rankKey rank x ≤ rankKey rank y

instance (rank : Num → ℕ) : DecidableRel (RankLE rank) := fun x y =>
  inferInstanceAs (Decidable (rankKey rank x ≤ rankKey rank y))

/-- **SWI-Prolog's standard order of numbers**: NaN first, then by value, then among numbers of
one value `-0.0`, the other doubles, the integer. -/
abbrev swiLE : Num → Num → Prop := RankLE swiRank

/-- SWI's strict order of numbers. -/
def swiLT (x y : Num) : Prop := rankKey swiRank x < rankKey swiRank y

instance : DecidableRel swiLT := fun x y =>
  inferInstanceAs (Decidable (rankKey swiRank x < rankKey swiRank y))

/-- **The integer-first order of numbers**: NaN first, then by value, then among numbers of one
value the integer, `-0.0`, the other doubles. -/
abbrev intFirstLE : Num → Num → Prop := RankLE intRank

/-- A rank separates the numbers of one value: two numbers, neither NaN, of one value and one
rank are one number. -/
def Separates (rank : Num → ℕ) : Prop :=
  ∀ x y, isNaN x = false → isNaN y = false → valOf x = valOf y → rank x = rank y → x = y

theorem swiRank_separates : Separates swiRank := by
  intro x y hx hy hv hr
  rcases x with m | (_ | _ | a) <;> rcases y with n | (_ | _ | b) <;>
    simp_all [swiRank, isNaN, valOf]
  exact_mod_cast ofQ_injective hv

theorem intRank_separates : Separates intRank := by
  intro x y hx hy hv hr
  rcases x with m | (_ | _ | a) <;> rcases y with n | (_ | _ | b) <;>
    simp_all [intRank, isNaN, valOf]
  exact_mod_cast ofQ_injective hv

theorem rankKey_injective {rank : Num → ℕ} (h : Separates rank) :
    Function.Injective (rankKey rank) := by
  intro x y hxy
  unfold rankKey at hxy
  cases hx : isNaN x <;> cases hy : isNaN y <;>
    simp only [hx, hy, Bool.false_eq_true, if_true, if_false] at hxy
  · have e := WithBot.coe_injective hxy
    simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at e
    exact h x y hx hy e.1 e.2
  · exact absurd hxy WithBot.coe_ne_bot
  · exact absurd hxy.symm WithBot.coe_ne_bot
  · rw [isNaN_eq_true hx, isNaN_eq_true hy]

theorem rankKey_lt {rank : Num → ℕ} {x y : Num} (hx : isNaN x = false) (hy : isNaN y = false) :
    rankKey rank x < rankKey rank y ↔
      valOf x < valOf y ∨ (valOf x = valOf y ∧ rank x < rank y) := by
  simp only [rankKey, hx, hy, Bool.false_eq_true, if_false, WithBot.coe_lt_coe, Prod.Lex.lt_iff,
    ofLex_toLex]

/-- **A term order on numbers, as the spec states it**: total, equal only on identical
numbers, transitive, value-consistent, and NaN at one fixed place. -/
structure IsNumberOrder (T : Num → Num → Prop) : Prop where
  total : ∀ x y, T x y ∨ T y x
  antisymm : ∀ x y, T x y → T y x → x = y
  trans : ∀ x y z, T x y → T y z → T x z
  value : ∀ x y, isNaN x = false → isNaN y = false → valOf x < valOf y → T x y ∧ ¬ T y x
  nan_place : (∀ x, T (.flt .nan) x) ∨ ∀ x, T x (.flt .nan)

/-- **Every separating rank gives a term order on numbers**, with NaN first. -/
theorem rankLE_isNumberOrder {rank : Num → ℕ} (h : Separates rank) :
    IsNumberOrder (RankLE rank) where
  total x y := le_total _ _
  antisymm x y hxy hyx := rankKey_injective h (le_antisymm hxy hyx)
  trans x y z := le_trans
  value x y hx hy hlt := by
    have : rankKey rank x < rankKey rank y := (rankKey_lt hx hy).mpr (Or.inl hlt)
    exact ⟨this.le, not_le.mpr this⟩
  nan_place := Or.inl fun x => by simp [RankLE, rankKey, isNaN]

theorem swi_isNumberOrder : IsNumberOrder swiLE := rankLE_isNumberOrder swiRank_separates

theorem intFirst_isNumberOrder : IsNumberOrder intFirstLE :=
  rankLE_isNumberOrder intRank_separates

/-- The key of a NaN-last order: the value, then a rank among the numbers of one value, NaN
last. -/
def nanLastKey (rank : Num → ℕ) (x : Num) : WithTop (Lex (XR × ℕ)) :=
  if isNaN x then ⊤ else ↑(toLex (valOf x, rank x))

/-- **SWI's tie-break with NaN last.** -/
def NaNLastLE (x y : Num) : Prop := nanLastKey swiRank x ≤ nanLastKey swiRank y

instance : DecidableRel NaNLastLE := fun x y =>
  inferInstanceAs (Decidable (nanLastKey swiRank x ≤ nanLastKey swiRank y))

/-- **NaN may come last**: SWI's tie-break with NaN last is a term order on numbers too. -/
theorem nanLast_isNumberOrder : IsNumberOrder NaNLastLE where
  total x y := le_total _ _
  antisymm x y hxy hyx := by
    have hk := le_antisymm hxy hyx
    unfold nanLastKey at hk
    cases hx : isNaN x <;> cases hy : isNaN y <;>
      simp only [hx, hy, Bool.false_eq_true, if_true, if_false] at hk
    · have e := WithTop.coe_injective hk
      simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at e
      exact swiRank_separates x y hx hy e.1 e.2
    · exact absurd hk WithTop.coe_ne_top
    · exact absurd hk.symm WithTop.coe_ne_top
    · rw [isNaN_eq_true hx, isNaN_eq_true hy]
  trans x y z := le_trans
  value x y hx hy hlt := by
    have : nanLastKey swiRank x < nanLastKey swiRank y := by
      simp only [nanLastKey, hx, hy, Bool.false_eq_true, if_false, WithTop.coe_lt_coe,
        Prod.Lex.lt_iff, ofLex_toLex]
      exact Or.inl hlt
    exact ⟨this.le, not_le.mpr this⟩
  nan_place := Or.inr fun x => by simp [NaNLastLE, nanLastKey, isNaN]

namespace IsNumberOrder

variable {T : Num → Num → Prop} [DecidableRel T] (hT : IsNumberOrder T)
include hT

omit [DecidableRel T] in
/-- A number order puts the lower value first: it refines the order of values. -/
theorem le_value {x y : Num} (hx : isNaN x = false) (hy : isNaN y = false) (h : T x y) :
    valOf x ≤ valOf y :=
  not_lt.mp fun hlt => (hT.value y x hy hx hlt).2 h

theorem sorted (l : List Num) : (l.insertionSort T).Pairwise T := by
  have : Std.Total T := ⟨hT.total⟩
  have : IsTrans Num T := ⟨hT.trans⟩
  exact List.pairwise_insertionSort T l

theorem sorted_value {l : List Num} (h : ∀ x ∈ l, isNaN x = false) :
    (l.insertionSort T).Pairwise (fun a b => valOf a ≤ valOf b) :=
  (hT.sorted l).imp_of_mem fun ha hb hab =>
    hT.le_value (h _ ((List.perm_insertionSort T l).mem_iff.mp ha))
      (h _ ((List.perm_insertionSort T l).mem_iff.mp hb)) hab

/-- **The rule's pairs**: a number order's sort answers the rule's `(min, max)` on numbers of
different values. -/
theorem pairs : PairsByRule id (List.insertionSort T) :=
  (pairsByRule_iff id T).mpr fun x y hx hy hlt => hT.value x y hx hy hlt

/-- **A number order's sort has the stable sort's values**, place by place. -/
theorem sort_values {l : List Num} (h : ∀ x ∈ l, isNaN x = false) :
    (l.insertionSort T).map valOf = (l.insertionSort (fun a b => valOf a ≤ valOf b)).map valOf :=
  List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
    (List.pairwise_map.mpr (hT.sorted_value h))
    (List.pairwise_map.mpr (sorted_insertionSort valOf l))
    (((List.perm_insertionSort T l).trans (List.perm_insertionSort _ l).symm).map _)

/-- **Within a block a number order's sort is its sort of the block**: the numbers of one
value come in the order's order. -/
theorem sort_blocks (l : List Num) (v : XR) :
    (l.insertionSort T).filter (fun x => valOf x = v) =
      (l.filter (fun x => valOf x = v)).insertionSort T :=
  List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => hT.antisymm a b h1 h2)
    ((hT.sorted l).sublist List.filter_sublist) (hT.sorted _)
    (((List.perm_insertionSort T l).filter _).trans (List.perm_insertionSort T _).symm)

/-- **A number order's sort is the stable sort exactly when every block is in its order**:
on numbers without NaN, sorting by the order and the stable sort by value agree except within
blocks of one value, and they are equal exactly when each block of the input already is in the
order's order. -/
theorem sort_eq_stable_iff {l : List Num} (h : ∀ x ∈ l, isNaN x = false) :
    l.insertionSort T = l.insertionSort (fun a b => valOf a ≤ valOf b) ↔
      ∀ v, (l.filter (fun x => valOf x = v)).Pairwise T := by
  constructor
  · intro he v
    rw [← insertionSort_blocks valOf l v, ← he]
    exact (hT.sorted l).sublist List.filter_sublist
  · intro hb
    refine eq_insertionSort_of_sorted valOf (hT.sorted_value h) fun v => ?_
    rw [hT.sort_blocks, (hb v).insertionSort_eq]

end IsNumberOrder

/-! ### ISO's order -/

/-- The kind ISO orders numbers by first: doubles, then integers. -/
def isoKind : Num → ℕ
  | .flt _ => 0
  | .int _ => 1

/-- **ISO's standard order of numbers** (GNU Prolog, SICStus): every double before every
integer, each by value. ISO has no NaN; it leaves `-0.0` and `0.0` tied. -/
def isoLE (x y : Num) : Prop := toLex (isoKind x, valOf x) ≤ toLex (isoKind y, valOf y)

/-- ISO's strict order of numbers. -/
def isoLT (x y : Num) : Prop := toLex (isoKind x, valOf x) < toLex (isoKind y, valOf y)

instance : DecidableRel isoLE := fun x y =>
  inferInstanceAs (Decidable (toLex (isoKind x, valOf x) ≤ toLex (isoKind y, valOf y)))

instance : DecidableRel isoLT := fun x y =>
  inferInstanceAs (Decidable (toLex (isoKind x, valOf x) < toLex (isoKind y, valOf y)))

/-- **ISO's order is not value-consistent**: `-1.0` comes before `-9`. -/
theorem iso_not_value_consistent :
    valOf (Num.int (-9)) < valOf (dq (-1)) ∧ isoLT (dq (-1)) (.int (-9)) := by
  constructor <;> decide +kernel

/-- **No sort that answers the rule's pairs is ISO's sort**: on `[-1.0, -9]` it answers
`[-9, -1.0]`, where ISO's sort answers `[-1.0, -9]`. -/
theorem iso_disagrees (sort : List Num → List Num) (h : PairsByRule id sort) :
    sort [dq (-1), .int (-9)] ≠ [dq (-1), Num.int (-9)].insertionSort isoLE := by
  rw [h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem iso_not_pairsByRule : ¬ PairsByRule id (List.insertionSort isoLE) := fun h =>
  iso_disagrees _ h rfl

/-! ### SWI's tie-break is ISO's order -/

/-- The order by value, then by ISO's order. -/
def ValueThenIsoLT (x y : Num) : Prop := valOf x < valOf y ∨ (valOf x = valOf y ∧ isoLT x y)

theorem isoLT_iff (x y : Num) :
    isoLT x y ↔ isoKind x < isoKind y ∨ (isoKind x = isoKind y ∧ valOf x < valOf y) := by
  simp only [isoLT, Prod.Lex.lt_iff, ofLex_toLex]

/-- **SWI's tie-break is ISO's order as the second key**: on numbers that are not NaN, SWI's
strict order is the order by value, then by ISO's order, and `-0.0` before `0.0`, the one pair
that order leaves tied. -/
theorem swiLT_iff {x y : Num} (hx : isNaN x = false) (hy : isNaN y = false) :
    swiLT x y ↔ ValueThenIsoLT x y ∨ (x = .flt .negZero ∧ y = dq 0) := by
  rw [swiLT, rankKey_lt hx hy, ValueThenIsoLT, isoLT_iff]
  rcases lt_trichotomy (valOf x) (valOf y) with h | h | h
  · simp [h]
  · rcases x with m | (_ | _ | a) <;> rcases y with n | (_ | _ | b) <;>
      simp_all [swiRank, isoKind, isNaN, valOf, dq, ofQ]
  · have h1 : valOf x ≠ valOf y := h.ne'
    have h2 : ¬ valOf x < valOf y := not_lt.mpr h.le
    refine iff_of_false (by simp [h1, h2]) ?_
    rintro (h3 | ⟨rfl, rfl⟩)
    · simp [h1, h2] at h3
    · exact absurd h (by decide +kernel)

/-- **Value, then ISO's order, leaves one pair tied**: two different numbers, neither NaN, are
ordered one way or the other unless they are `-0.0` and `0.0`. -/
theorem valueThenIso_total {x y : Num} (hx : isNaN x = false) (hy : isNaN y = false)
    (hxy : x ≠ y) (hz : ¬ (x = .flt .negZero ∧ y = dq 0))
    (hz' : ¬ (x = dq 0 ∧ y = .flt .negZero)) :
    ValueThenIsoLT x y ∨ ValueThenIsoLT y x := by
  rw [ValueThenIsoLT, ValueThenIsoLT, isoLT_iff, isoLT_iff]
  rcases lt_trichotomy (valOf x) (valOf y) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases x with m | (_ | _ | a) <;> rcases y with n | (_ | _ | b) <;>
      simp_all [isoKind, isNaN, valOf, dq, ofQ]
  · exact Or.inr (Or.inl h)

/-- **ISO's order against the order of values**: a double below an integer in value, ISO and
value agree; an integer below a double, they conflict, and SWI follows value; one value, value
leaves the pair free and ISO puts the double first, as SWI does. -/
theorem iso_against_value (d : Dbl) (n : ℤ) (hd : isNaN (.flt d) = false) :
    (valOf (.flt d) < valOf (.int n) → isoLT (.flt d) (.int n) ∧ swiLT (.flt d) (.int n)) ∧
      (valOf (.int n) < valOf (.flt d) → isoLT (.flt d) (.int n) ∧ swiLT (.int n) (.flt d)) ∧
      (valOf (.flt d) = valOf (.int n) → isoLT (.flt d) (.int n) ∧ swiLT (.flt d) (.int n)) := by
  have hiso : isoLT (.flt d) (.int n) := (isoLT_iff _ _).mpr (Or.inl (by simp [isoKind]))
  have hrank : swiRank (.flt d) < swiRank (.int n) := by
    rcases d with _ | _ | _ <;> simp [swiRank]
  refine ⟨fun h => ⟨hiso, ?_⟩, fun h => ⟨hiso, ?_⟩, fun h => ⟨hiso, ?_⟩⟩
  · exact (rankKey_lt hd rfl).mpr (Or.inl h)
  · exact (rankKey_lt rfl hd).mpr (Or.inl h)
  · exact (rankKey_lt hd rfl).mpr (Or.inr ⟨h, hrank⟩)

/-- **SWI's order is the one order that follows ISO wherever value leaves it free**: a total,
antisymmetric, value-consistent order that agrees with ISO's strict order on every pair where
ISO does not contradict value is SWI's on every pair but `-0.0` and `0.0`. -/
theorem swi_unique (T : Num → Num → Prop) (total : ∀ x y, T x y ∨ T y x)
    (antisymm : ∀ x y, T x y → T y x → x = y)
    (value : ∀ x y, isNaN x = false → isNaN y = false → valOf x < valOf y → T x y)
    (iso : ∀ x y, isNaN x = false → isNaN y = false → isoLT x y → ¬ valOf y < valOf x → T x y)
    {x y : Num} (hx : isNaN x = false) (hy : isNaN y = false)
    (hz : ¬ (x = .flt .negZero ∧ y = dq 0)) (hz' : ¬ (x = dq 0 ∧ y = .flt .negZero)) :
    T x y ↔ swiLE x y := by
  by_cases hxy : x = y
  · subst hxy
    exact iff_of_true ((total x x).elim id id) (le_refl _)
  have notT {a b : Num} (hab : T a b) (hne : a ≠ b) : ¬ T b a := fun hba =>
    hne (antisymm a b hab hba)
  have swi_of {a b : Num} (ha : isNaN a = false) (hb : isNaN b = false) (h : ValueThenIsoLT a b) :
      swiLT a b := (swiLT_iff ha hb).mpr (Or.inl h)
  have T_of {a b : Num} (ha : isNaN a = false) (hb : isNaN b = false) (h : ValueThenIsoLT a b) :
      T a b := by
    rcases h with h | ⟨h, hiso⟩
    · exact value a b ha hb h
    · exact iso a b ha hb hiso (by rw [h]; exact lt_irrefl _)
  rcases valueThenIso_total hx hy hxy hz hz' with h | h
  · exact iff_of_true (T_of hx hy h) (swi_of hx hy h).le
  · exact iff_of_false (notT (T_of hy hx h) (Ne.symm hxy)) (not_le.mpr (swi_of hy hx h))

/-- **With IEEE's order of the zeros, SWI's order is the only one**: adding `-0.0` before `0.0`
pins the order down on every pair of numbers that are not NaN. -/
theorem swi_unique_of_zeros (T : Num → Num → Prop) (total : ∀ x y, T x y ∨ T y x)
    (antisymm : ∀ x y, T x y → T y x → x = y)
    (value : ∀ x y, isNaN x = false → isNaN y = false → valOf x < valOf y → T x y)
    (iso : ∀ x y, isNaN x = false → isNaN y = false → isoLT x y → ¬ valOf y < valOf x → T x y)
    (zeros : T (.flt .negZero) (dq 0)) {x y : Num} (hx : isNaN x = false)
    (hy : isNaN y = false) : T x y ↔ swiLE x y := by
  by_cases hz : x = .flt .negZero ∧ y = dq 0
  · obtain ⟨rfl, rfl⟩ := hz
    exact iff_of_true zeros (by decide +kernel)
  by_cases hz' : x = dq 0 ∧ y = .flt .negZero
  · obtain ⟨rfl, rfl⟩ := hz'
    refine iff_of_false (fun h => absurd (antisymm _ _ zeros h) (by decide)) (by decide +kernel)
  exact swi_unique T total antisymm value iso hx hy hz hz'

/-- **SWI's order meets every condition of `swi_unique_of_zeros`**: total, antisymmetric,
value-consistent, following ISO wherever ISO does not contradict value, and `-0.0` first. -/
theorem swi_satisfies :
    (∀ x y, swiLE x y ∨ swiLE y x) ∧ (∀ x y, swiLE x y → swiLE y x → x = y) ∧
      (∀ x y, isNaN x = false → isNaN y = false → valOf x < valOf y → swiLE x y) ∧
      (∀ x y, isNaN x = false → isNaN y = false → isoLT x y → ¬ valOf y < valOf x →
        swiLE x y) ∧
      swiLE (.flt .negZero) (dq 0) := by
  refine ⟨swi_isNumberOrder.total, swi_isNumberOrder.antisymm,
    fun x y hx hy h => (swi_isNumberOrder.value x y hx hy h).1, fun x y hx hy hiso hv => ?_,
    by decide +kernel⟩
  rcases lt_or_eq_of_le (not_lt.mp hv) with h | h
  · exact (swi_isNumberOrder.value x y hx hy h).1
  · exact ((swiLT_iff hx hy).mpr (Or.inl (Or.inr ⟨h, hiso⟩))).le

/-- **Any other tie-break breaks ISO where value leaves it free**: a total, antisymmetric,
value-consistent order that differs from SWI's on a pair other than the zeros puts an integer
before a double of its value, against ISO. -/
theorem tie_break_breaks_iso (T : Num → Num → Prop) (total : ∀ x y, T x y ∨ T y x)
    (antisymm : ∀ x y, T x y → T y x → x = y)
    (value : ∀ x y, isNaN x = false → isNaN y = false → valOf x < valOf y → T x y)
    {x y : Num} (hx : isNaN x = false) (hy : isNaN y = false)
    (hz : ¬ (x = .flt .negZero ∧ y = dq 0)) (hz' : ¬ (x = dq 0 ∧ y = .flt .negZero))
    (hne : ¬ (T x y ↔ swiLE x y)) :
    ∃ a b, isNaN a = false ∧ isNaN b = false ∧ valOf a = valOf b ∧ isoLT a b ∧ ¬ T a b := by
  by_contra hno
  refine hne (swi_unique T total antisymm value (fun a b ha hb hiso hv => ?_) hx hy hz hz')
  rcases lt_or_eq_of_le (not_lt.mp hv) with h | h
  · exact value a b ha hb h
  · by_contra hT
    exact hno ⟨a, b, ha, hb, h, hiso, hT⟩

/-- **SWI puts `-0.0` before `0.0`**, the one pair of numbers of one value that ISO's order
leaves tied; IEEE 754's `totalOrder` does the same. -/
theorem swi_zeros :
    swiLT (.flt .negZero) (dq 0) ∧ isoLE (.flt .negZero) (dq 0) ∧ isoLE (dq 0) (.flt .negZero) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end Numbers

/-! ## Controls -/

namespace Controls

/-- The stable sort by value of numbers. -/
abbrev stable (l : List Num) : List Num := l.insertionSort (fun a b => valOf a ≤ valOf b)

/-- **The sorts are the stable sort**: on `[2, 1.0, 1, 2.0, 0]`, selection sort by the rule
from the bottom and from the top, and insertion sort by compare-exchange, answer
`[0, 1.0, 1, 2, 2.0]`. -/
theorem sorts_stable :
    selSort id [.int 2, dq 1, .int 1, dq 2, .int 0] = [.int 0, dq 1, .int 1, .int 2, dq 2] ∧
      selSortTop id [.int 2, dq 1, .int 1, dq 2, .int 0] =
        [.int 0, dq 1, .int 1, .int 2, dq 2] ∧
      ceSort id [.int 2, dq 1, .int 1, dq 2, .int 0] = [.int 0, dq 1, .int 1, .int 2, dq 2] ∧
      stable [.int 2, dq 1, .int 1, dq 2, .int 0] = [.int 0, dq 1, .int 1, .int 2, dq 2] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **NaN's place is the algorithm's**: on `[1, nan, -1]` selection sort from the bottom answers
`[nan, -1, 1]` and from the top `[-1, 1, nan]`. -/
theorem nan_place_by_algorithm :
    selSort id [.int 1, .flt .nan, .int (-1)] = [.flt .nan, .int (-1), .int 1] ∧
      selSortTop id [.int 1, .flt .nan, .int (-1)] = [.int (-1), .int 1, .flt .nan] := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **Ties stay in input order**: `[1, 1.0]` and `[1.0, 1]` are both fixed points of both
sorts, so their outputs are sorted by no antisymmetric relation. -/
theorem tie_fixed_points :
    selSort id [.int 1, dq 1] = [.int 1, dq 1] ∧ selSort id [dq 1, .int 1] = [dq 1, .int 1] ∧
      ceSort id [.int 1, dq 1] = [.int 1, dq 1] ∧ ceSort id [dq 1, .int 1] = [dq 1, .int 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **NaN**: selection sort by the rule puts NaN first and permutes, `[1, nan, 0]` giving
`[nan, 0, 1]`, which is not the stable sort by value (NaN's value is read as `0`); insertion sort
by compare-exchange answers NaN everywhere, `[1, nan]` giving `[nan, nan]`. -/
theorem nan_handling :
    selSort id [.int 1, .flt .nan, .int (-1)] = [.flt .nan, .int (-1), .int 1] ∧
      stable [.int 1, .flt .nan, .int (-1)] = [.int (-1), .flt .nan, .int 1] ∧
      ceSort id [.int 1, .flt .nan] = [.flt .nan, .flt .nan] ∧
      ¬ (ceSort id [Num.int 1, .flt .nan]).Perm [.int 1, .flt .nan] := by
  refine ⟨?_, ?_, ?_, ceSort_not_perm id _ ⟨.flt .nan, by simp, rfl⟩ ⟨.int 1, by simp, rfl⟩⟩ <;>
    decide +kernel

/-- **A sorting network built from the rule need not be stable**: on `[1, 1.0, 0]` the 3-wire
network `[(0,2), (0,1), (1,2)]` answers `[0, 1.0, 1]`, the insertion network
`[(1,2), (0,1), (1,2)]` and the stable sort `[0, 1, 1.0]`; both networks sort every input by
value. -/
theorem networks_differ :
    runNet id net3 [.int 1, dq 1, .int 0] = [.int 0, dq 1, .int 1] ∧
      runNet id insertion3 [.int 1, dq 1, .int 0] = [.int 0, .int 1, dq 1] ∧
      stable [.int 1, dq 1, .int 0] = [.int 0, .int 1, dq 1] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- **SWI's sort and the stable sort**: on `[1, 1.0]` SWI's sort answers `[1.0, 1]` and the
stable sort keeps `[1, 1.0]`, whose block of value 1 is not in SWI's order; on `[1.0, 1]` they
agree. -/
theorem swi_vs_stable :
    [Num.int 1, dq 1].insertionSort swiLE = [dq 1, .int 1] ∧
      stable [.int 1, dq 1] = [.int 1, dq 1] ∧
      ¬ ([Num.int 1, dq 1].filter (fun x => valOf x = 1)).Pairwise swiLE ∧
      [dq 1, Num.int 1].insertionSort swiLE = stable [dq 1, .int 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **The tie-break is free**: SWI's order puts `1.0` before `1`, the integer-first order `1`
before `1.0`; both are number orders answering the rule's pairs. -/
theorem tie_break_free :
    swiLE (dq 1) (.int 1) ∧ ¬ swiLE (.int 1) (dq 1) ∧
      intFirstLE (.int 1) (dq 1) ∧ ¬ intFirstLE (dq 1) (.int 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **The integer-first order breaks ISO where value leaves the pair free**: ISO puts `1.0`
before `1`, of one value, and the integer-first order does not. -/
theorem intFirst_breaks_iso :
    valOf (dq 1) = valOf (.int 1) ∧ isoLT (dq 1) (.int 1) ∧ ¬ intFirstLE (dq 1) (.int 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- **ISO's sort against the rule's sorts**: on `[-1.0, -9]` ISO's sort keeps the input, the
rule's sorts answer `[-9, -1.0]`. -/
theorem iso_vs_rule :
    [dq (-1), Num.int (-9)].insertionSort isoLE = [dq (-1), .int (-9)] ∧
      selSort id [dq (-1), .int (-9)] = [.int (-9), dq (-1)] ∧
      ceSort id [dq (-1), .int (-9)] = [.int (-9), dq (-1)] ∧
      [dq (-1), Num.int (-9)].insertionSort swiLE = [.int (-9), dq (-1)] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### The theorems on the controls' inputs -/

theorem sorts_instances :
    selSort id [.int 2, dq 1, .int 1, dq 2, .int 0] = stable [.int 2, dq 1, .int 1, dq 2, .int 0] ∧
      selSortTop id [.int 2, dq 1, .int 1, dq 2, .int 0] =
        stable [.int 2, dq 1, .int 1, dq 2, .int 0] ∧
      ceSort id [.int 2, dq 1, .int 1, dq 2, .int 0] =
        stable [.int 2, dq 1, .int 1, dq 2, .int 0] ∧
      selSort id [.int 1, .flt .nan, .int (-1)] = [.flt .nan] ++ stable [.int 1, .int (-1)] ∧
      selSortTop id [.int 1, .flt .nan, .int (-1)] = stable [.int 1, .int (-1)] ++ [.flt .nan] ∧
      (∀ y ∈ ceSort id [Num.int 1, .flt .nan], isNaN y = true) :=
  ⟨selSort_eq id _ (by decide +kernel), selSortTop_eq id _ (by decide +kernel),
    ceSort_eq id _ (by decide +kernel), selSort_nan id _, selSortTop_nan _,
    ceSort_nan id _ ⟨.flt .nan, by simp, rfl⟩⟩

theorem networks_instances :
    runNet id insertion3 [.int 1, dq 1, .int 0] = stable [.int 1, dq 1, .int 0] ∧
      (runNet id net3 [.int 1, dq 1, .int 0]).map valOf =
        (stable [.int 1, dq 1, .int 0]).map valOf ∧
      runNet id (insertionNet 4) [.int 3, dq 1, .int 1, dq 0] =
        stable [.int 3, dq 1, .int 1, dq 0] :=
  ⟨runNet_eq_insertionSort id insertion3_adjacent (by decide +kernel) (by decide +kernel),
    runNet_values id net3 (by decide +kernel)
      (net3_sorts id (a := .int 1) (b := dq 1) (c := .int 0) rfl rfl rfl),
    insertionNet_eq id _ (by decide +kernel)⟩

theorem no_order_instance :
    ¬ (∀ l, (∀ z ∈ l, isNaN z = false) → (selSort id l).Pairwise swiLE) ∧
      ¬ (∀ l, (∀ z ∈ l, isNaN z = false) → (ceSort id l).Pairwise swiLE) ∧
      ∀ net : List Comparator,
        ¬ ∀ l, (∀ z ∈ l, isNaN z = false) → (runNet id net l).Pairwise swiLE :=
  no_order_from_rule id (x := .int 1) (y := dq 1) (by decide) rfl rfl (by decide +kernel) swiLE
    swi_isNumberOrder.antisymm

theorem orders_instances :
    PairsByRule id (List.insertionSort swiLE) ∧ PairsByRule id (List.insertionSort intFirstLE) ∧
      PairsByRule id (List.insertionSort NaNLastLE) ∧
      ¬ PairsByRule id (List.insertionSort isoLE) ∧
      ([Num.int 1, dq 1].insertionSort swiLE ≠ stable [.int 1, dq 1]) ∧
      [dq 1, Num.int 1].insertionSort swiLE = stable [dq 1, .int 1] := by
  refine ⟨swi_isNumberOrder.pairs, intFirst_isNumberOrder.pairs, nanLast_isNumberOrder.pairs,
    iso_not_pairsByRule, fun h => ?_, ?_⟩
  · have := (swi_isNumberOrder.sort_eq_stable_iff (l := [Num.int 1, dq 1])
      (by decide +kernel)).mp h 1
    exact absurd this (by decide +kernel)
  · exact (swi_isNumberOrder.sort_eq_stable_iff (by decide +kernel)).mpr fun v => by
      by_cases hv : v = 1
      · subst hv
        decide +kernel
      · have h1 : valOf (dq 1) ≠ v := fun e => hv (e.symm.trans (by decide +kernel))
        have h2 : valOf (Num.int 1) ≠ v := fun e => hv (e.symm.trans (by decide +kernel))
        simp [h1, h2]

/-- **The integer-first order fails ISO on a pair that value leaves free**, as every other
tie-break must (`tie_break_breaks_iso`); SWI's order meets every condition of its uniqueness
(`swi_satisfies`). -/
theorem iso_instance :
    ∃ a b, isNaN a = false ∧ isNaN b = false ∧ valOf a = valOf b ∧ isoLT a b ∧
      ¬ intFirstLE a b :=
  tie_break_breaks_iso intFirstLE intFirst_isNumberOrder.total intFirst_isNumberOrder.antisymm
    (fun x y hx hy h => (intFirst_isNumberOrder.value x y hx hy h).1) (x := dq 1) (y := .int 1)
    rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Controls

end Mettapedia.Machines.AdmissionRewriting.SortBySelection

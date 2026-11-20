import Mettapedia.Machines.ObserverLicence.Table
import Mettapedia.Machines.Order.PrefixInterval
import Mettapedia.Machines.Cursor.JoinOrderProfiles
import Mathlib.Data.Multiset.Sort

/-!
# Declared-order reads and their lazy reference cursor

The list denotes an already captured read view, not copied native storage.
Each successful cursor step consumes the scanned prefix once. Least-first
reading is sorting the matched occurrence bag under the declared linear order.
Payloads may coincide: order and cursor position belong to occurrences.

The order is a parameter. An implementation's semantic term view must supply
its order and matching adapters; a token encoding is not silently identified
with the native term comparator.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedRead

universe u
variable {α : Type u}

def read (accept : α → Bool) (rows : List α) : List α := rows.filter accept

theorem read_permutation (accept : α → Bool) {first second : List α}
    (same : first.Perm second) : (read accept first).Perm (read accept second) :=
  same.filter accept

theorem newest_and_oldest_same_bag (accept : α → Bool) (arrivals : List α) :
    (read accept arrivals.reverse).Perm (read accept arrivals) :=
  (List.reverse_perm arrivals).filter accept

def leastFirst [LinearOrder α] (accept : α → Bool) (rows : List α) : List α :=
  read accept ((rows : Multiset α).sort (· ≤ ·))

theorem leastFirst_bag [LinearOrder α] (accept : α → Bool) (rows : List α) :
    (leastFirst accept rows : Multiset α) = (read accept rows : Multiset α) := by
  apply Multiset.coe_eq_coe.mpr
  have sorted : ((rows : Multiset α).sort (· ≤ ·)).Perm rows :=
    Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _)
  exact sorted.filter accept

theorem leastFirst_sorted [LinearOrder α] (accept : α → Bool) (rows : List α) :
    (leastFirst accept rows).Pairwise (· ≤ ·) :=
  (Multiset.pairwise_sort (rows : Multiset α) (· ≤ ·)).filter _

theorem leastFirst_is_sorting_the_answer_bag [LinearOrder α]
    (accept : α → Bool) (rows : List α) :
    leastFirst accept rows = (read accept rows : Multiset α).sort (· ≤ ·) := by
  have permutation : (leastFirst accept rows).Perm ((read accept rows : Multiset α).sort (· ≤ ·)) :=
    Multiset.coe_eq_coe.mp ((leastFirst_bag accept rows).trans (Multiset.sort_eq _ _).symm)
  exact permutation.eq_of_pairwise' (leastFirst_sorted accept rows) (Multiset.pairwise_sort _ _)

theorem count_does_not_need_sorted_delivery [LinearOrder α] (accept : α → Bool) (rows : List α) :
    (leastFirst accept rows).length = (read accept rows).length := by
  exact (Multiset.coe_eq_coe.mp (leastFirst_bag accept rows)).length_eq

theorem existence_does_not_need_sorted_delivery [LinearOrder α] (accept : α → Bool) (rows : List α) :
    ObserverLicence.existsAnswer (leastFirst accept rows) =
      ObserverLicence.existsAnswer (read accept rows) :=
  ObserverLicence.exists_invariant (Multiset.coe_eq_coe.mp (leastFirst_bag accept rows))

structure Step (α : Type u) where
  answer : Option α
  remaining : List α
  examined : Nat
  deriving Repr, DecidableEq

def next (accept : α → Bool) : List α → Step α
  | [] => ⟨none, [], 0⟩
  | value :: later =>
      if accept value then ⟨some value, later, 1⟩
      else let reply := next accept later
        {reply with examined := reply.examined + 1}

theorem next_partition (accept : α → Bool) (rows : List α) :
    (next accept rows).answer.toList ++ read accept (next accept rows).remaining = read accept rows := by
  induction rows with
  | nil => rfl
  | cons value later ih =>
      cases admitted : accept value with
      | false => simpa [next, read, admitted] using ih
      | true => simp [next, read, admitted]

theorem next_work_partition (accept : α → Bool) (rows : List α) :
    (next accept rows).examined + (next accept rows).remaining.length = rows.length := by
  induction rows with
  | nil => rfl
  | cons value later ih =>
      cases admitted : accept value <;> simp [next, admitted] <;> omega

theorem next_head (accept : α → Bool) (rows : List α) :
    (next accept rows).answer = (read accept rows).head? := by
  induction rows with
  | nil => rfl
  | cons value later ih =>
      cases admitted : accept value <;> simp [next, read, admitted, ih]

def takeNext (accept : α → Bool) : Nat → List α → List α × List α × Nat
  | 0, rows => ([], rows, 0)
  | number + 1, rows =>
      let reply := next accept rows
      match reply.answer with
      | none => ([], reply.remaining, reply.examined)
      | some value =>
          let later := takeNext accept number reply.remaining
          (value :: later.1, later.2.1, reply.examined + later.2.2)

theorem next_none_remaining (accept : α → Bool) (rows : List α)
    (none : (next accept rows).answer = none) : (next accept rows).remaining = [] := by
  induction rows with
  | nil => rfl
  | cons value later ih =>
      cases admitted : accept value <;> simp_all [next]

theorem takeNext_exact (accept : α → Bool) (number : Nat) (rows : List α) :
    (takeNext accept number rows).1 = (read accept rows).take number ∧
      read accept (takeNext accept number rows).2.1 = (read accept rows).drop number ∧
      (takeNext accept number rows).2.2 + (takeNext accept number rows).2.1.length = rows.length := by
  induction number generalizing rows with
  | zero => simp [takeNext]
  | succ number ih =>
      have partition := next_partition accept rows
      have work := next_work_partition accept rows
      cases found : (next accept rows).answer with
      | none =>
          have empty := next_none_remaining accept rows found
          simp only [found, empty, Option.toList_none, List.nil_append, read, List.filter_nil] at partition
          simp only [empty, List.length_nil, Nat.add_zero] at work
          simp [takeNext, found, empty, ← partition, read, work]
      | some value =>
          have later := ih (next accept rows).remaining
          simp only [found, Option.toList_some, List.singleton_append] at partition
          simp only [takeNext, found, later.1, later.2.1, ← partition,
            List.take_succ_cons, List.drop_succ_cons]
          simp only [true_and]
          omega

theorem first_after_search_then_constant_delivery (rows : List α) :
    ∀ value rest, rows = value :: rest → next (fun _ => true) rows = ⟨some value, rest, 1⟩ := by
  intro value rest same
  subst rows
  rfl

theorem next_after_rejected_prefix (accept : α → Bool) (bad good : α)
    (rejects : accept bad = false) (accepts : accept good = true) (gap : Nat) :
    next accept (List.replicate gap bad ++ [good]) = ⟨some good, [], gap + 1⟩ := by
  induction gap with
  | zero => simp [next, accepts]
  | succ gap ih => simp [List.replicate_succ, next, rejects, ih]

def nested {A B : Type} (outer : List A) (inner : A → List B) : List (A × B) :=
  outer.flatMap fun first => (inner first).map (first, ·)

def pairLe (first second : Nat × Nat) : Prop :=
  first.1 < second.1 ∨ (first.1 = second.1 ∧ first.2 ≤ second.2)

theorem nested_is_lexicographic (outer : List Nat) (inner : Nat → List Nat)
    (outerSorted : outer.Pairwise (· < ·))
    (innerSorted : ∀ first ∈ outer, (inner first).Pairwise (· ≤ ·)) :
    (nested outer inner).Pairwise pairLe := by
  induction outer with
  | nil => simp [nested]
  | cons first rest ih =>
      obtain ⟨before, restSorted⟩ := List.pairwise_cons.mp outerSorted
      have headSorted := innerSorted first List.mem_cons_self
      have tailSorted := ih restSorted (fun value member => innerSorted value (List.mem_cons_of_mem _ member))
      rw [nested, List.flatMap_cons]
      apply List.pairwise_append.mpr
      refine ⟨?_, tailSorted, ?_⟩
      · simpa [List.pairwise_map, pairLe] using headSorted
      · intro left inLeft right inRight
        obtain ⟨leftValue, _, rfl⟩ := List.mem_map.mp inLeft
        obtain ⟨rightFirst, inRest, tailMember⟩ := List.mem_flatMap.mp inRight
        obtain ⟨rightValue, _, rfl⟩ := List.mem_map.mp tailMember
        exact Or.inl (before rightFirst inRest)

namespace Controls

theorem a_scattered_predicate_needs_more_than_one_interval :
    read (fun row => row == 0 || row == 2) [0, 1, 2] = [0, 2] ∧
      ¬ (∀ between : Nat, 0 ≤ between → between ≤ 2 → between ∈ read (fun row => row == 0 || row == 2) [0, 1, 2]) := by
  constructor
  · decide
  · intro convex
    have impossible := convex 1 (by decide) (by decide)
    contradiction

theorem a_next_step_does_not_rescan_the_prefix :
    next (fun n : Nat => n % 2 == 0) [1, 2, 3, 4] = ⟨some 2, [3, 4], 2⟩ ∧
      next (fun n : Nat => n % 2 == 0) [3, 4] = ⟨some 4, [], 2⟩ := by decide

theorem join_exchange_preserves_bag_but_not_order :
    (nested [1, 2] (fun _ => [1, 2])).Perm [(1, 1), (2, 1), (1, 2), (2, 2)] ∧
      nested [1, 2] (fun _ => [1, 2]) ≠ [(1, 1), (2, 1), (1, 2), (2, 2)] := by
  constructor
  · exact Machines.Cursor.JoinOrderProfiles.fixed_join_bag_commutes (fun _ _ : Nat => true) [1, 2] [1, 2]
  · decide

theorem equal_payloads_do_not_remove_occurrences :
    (([1, 2, 3] : List Nat).map (fun _ => 7)).length = 3 ∧
      (([1, 2, 3] : List Nat).map (fun _ => 7)).take 2 = [7, 7] := by decide

theorem a_ground_front_does_not_bound_suffix_filtering (gap : Nat) :
    let bad : Nat × Nat × Nat := (0, 0, 0)
    let good : Nat × Nat × Nat := (0, 7, 1)
    bad.1 = good.1 ∧
      next (fun row : Nat × Nat × Nat => row.2.2 == 1)
        (List.replicate gap bad ++ [good]) = ⟨some good, [], gap + 1⟩ := by
  exact ⟨rfl, next_after_rejected_prefix _ _ _ (by decide) (by decide) gap⟩

end Controls

end Mettapedia.Machines.OrderedRead

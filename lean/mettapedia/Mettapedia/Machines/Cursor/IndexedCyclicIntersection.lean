import Mettapedia.Machines.Cursor.IndexedIntersection
import Mettapedia.Machines.Cursor.CyclicProgress

/-!
# Binary-seeking cyclic intersection of a finite cursor family

The first cursor has the smallest head, the last the largest. Equal heads
deliver one key and advance only the first cursor. Otherwise that cursor
seeks to the largest head. It then rotates to the end. These are the cyclic
operations, rather than minimum-projection membership probing or advancing
every cursor at a match.

The ranges use the existing random-access binary partition. List rotation
and last-cursor lookup have an explicit family-width overhead; no constant
time circular-buffer implementation is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.IndexedCyclicIntersection

open IndexedIntersection

variable {Key : Type*} [LinearOrder Key]

structure Active (Key : Type*) where
  range : Range Key
  positive : 0 < range.width

def Active.head (cursor : Active Key) : Key := cursor.range.read cursor.range.lo

def Ready (cursors : List (Active Key)) : Prop :=
  cursors.Pairwise (fun left right => left.head ≤ right.head)

def Common (cursors : List (Active Key)) (key : Key) : Prop :=
  ∀ cursor ∈ cursors, key ∈ cursor.range.view

def sizes (cursors : List (Active Key)) : List Nat :=
  cursors.map (fun cursor => cursor.range.width)

def last (first : Active Key) (rest : List (Active Key)) : Active Key :=
  (first :: rest).getLast (by simp)

omit [LinearOrder Key] in
theorem last_member (first : Active Key) (rest : List (Active Key)) :
    last first rest ∈ first :: rest := List.getLast_mem _

theorem head_le_last (first : Active Key) (rest : List (Active Key))
    (ready : Ready (first :: rest)) (cursor : Active Key)
    (member : cursor ∈ first :: rest) : cursor.head ≤ (last first rest).head := by
  exact ready.rel_getLast_of_rel_getLast_getLast member le_rfl

theorem first_le_head (first : Active Key) (rest : List (Active Key))
    (ready : Ready (first :: rest)) (cursor : Active Key)
    (member : cursor ∈ first :: rest) : first.head ≤ cursor.head := by
  rcases List.mem_cons.mp member with same | member
  · subst cursor; exact le_rfl
  · exact (List.pairwise_cons.mp ready).1 cursor member

theorem head_le_value (cursor : Active Key) (sorted : cursor.range.Sorted)
    (key : Key) (member : key ∈ cursor.range.view) : cursor.head ≤ key := by
  rw [view_cons cursor.range cursor.positive] at member
  rcases List.mem_cons.mp member with same | member
  · exact le_of_eq same.symm
  · have ordered := List.pairwise_cons.mp
      (show (cursor.head :: cursor.range.tail.view).Pairwise (· < ·) by
        unfold Active.head
        rw [← view_cons cursor.range cursor.positive]; exact view_sorted _ sorted)
    exact le_of_lt (ordered.1 key member)

theorem tail_value_gt (cursor : Active Key) (sorted : cursor.range.Sorted)
    (key : Key) (member : key ∈ cursor.range.tail.view) : cursor.head < key := by
  have ordered := List.pairwise_cons.mp
    (show (cursor.head :: cursor.range.tail.view).Pairwise (· < ·) by
      unfold Active.head
      rw [← view_cons cursor.range cursor.positive]; exact view_sorted _ sorted)
  exact ordered.1 key member

theorem common_lower (first : Active Key) (rest : List (Active Key))
    (sorted : ∀ cursor ∈ first :: rest, cursor.range.Sorted)
    (key : Key) (member : Common (first :: rest) key) :
    (last first rest).head ≤ key :=
  head_le_value _ (sorted _ (last_member first rest)) _
    (member _ (last_member first rest))

theorem common_at_equal_heads (first : Active Key) (rest : List (Active Key))
    (ready : Ready (first :: rest)) (same : first.head = (last first rest).head) :
    Common (first :: rest) first.head := by
  intro cursor member
  have low := first_le_head first rest ready cursor member
  have high := head_le_last first rest ready cursor member
  have equal : cursor.head = first.head := le_antisymm (by simpa [same] using high) low
  rw [view_cons cursor.range cursor.positive]
  exact List.mem_cons.mpr (Or.inl equal.symm)

/-- The chosen successor has discarded at least the first key. -/
def successor (first : Active Key) (rest : List (Active Key)) : Range Key × Nat :=
  if first.head = (last first rest).head then (first.range.tail, 0)
  else first.range.tail.seek (last first rest).head

theorem successor_progress (first : Active Key) (rest : List (Active Key)) :
    (successor first rest).1.width < first.range.width := by
  have positive := first.positive
  unfold successor
  split
  · simp only [tail_width]; omega
  · have bound := seek_width first.range.tail (last first rest).head
    rw [tail_width] at bound
    omega

theorem successor_sorted (first : Active Key) (rest : List (Active Key))
    (sorted : first.range.Sorted) : (successor first rest).1.Sorted := by
  unfold successor
  split
  · exact tail_sorted _ sorted
  · exact seek_sorted _ _ (tail_sorted _ sorted)

theorem successor_membership (first : Active Key) (rest : List (Active Key))
    (sorted : first.range.Sorted) (key : Key) :
    key ∈ (successor first rest).1.view ↔
      key ∈ first.range.tail.view ∧ (last first rest).head ≤ key := by
  unfold successor
  split
  next same =>
    constructor
    · intro member
      exact ⟨member, by simpa [same] using le_of_lt (tail_value_gt first sorted key member)⟩
    · exact And.left
  · rw [seek_view _ _ (tail_sorted _ sorted),
      OrderedIntersection.seek_membership _ _ (view_sorted _ (tail_sorted _ sorted))]

theorem successor_head_lower (first : Active Key) (rest : List (Active Key))
    (sorted : first.range.Sorted) (positive : 0 < (successor first rest).1.width) :
    (last first rest).head ≤ (Active.mk (successor first rest).1 positive).head := by
  apply ((successor_membership first rest sorted _).mp ?_).2
  rw [view_cons _ positive]
  simp [Active.head]

theorem successor_ready (first : Active Key) (rest : List (Active Key))
    (ready : Ready (first :: rest)) (sorted : first.range.Sorted)
    (positive : 0 < (successor first rest).1.width) :
    Ready (rest ++ [⟨(successor first rest).1, positive⟩]) := by
  apply List.pairwise_append.mpr
  refine ⟨(List.pairwise_cons.mp ready).2, by simp, ?_⟩
  intro cursor member next inNext
  have same := List.mem_singleton.mp inNext
  subst next
  exact (head_le_last first rest ready cursor (by simp [member])).trans
    (successor_head_lower first rest sorted positive)

/-- One step partitions the common keys into the emitted head, if any, and
the intersection with the shortened first range. -/
theorem successor_exact (first : Active Key) (rest : List (Active Key))
    (ready : Ready (first :: rest))
    (sorted : ∀ cursor ∈ first :: rest, cursor.range.Sorted) (key : Key) :
    Common (first :: rest) key ↔
      (first.head = (last first rest).head ∧ key = first.head) ∨
      (Common rest key ∧ key ∈ (successor first rest).1.view) := by
  rw [successor_membership first rest (sorted first (by simp)) key]
  constructor
  · intro member
    have lower := common_lower first rest sorted key member
    have firstMem := member first (by simp)
    rw [view_cons first.range first.positive] at firstMem
    rcases List.mem_cons.mp firstMem with equal | tailMem
    · left
      refine ⟨?_, equal⟩
      have le := head_le_last first rest ready first (by simp)
      exact le_antisymm le (by simpa only [equal, Active.head] using lower)
    · right
      exact ⟨fun cursor inRest => member cursor (by simp [inRest]), tailMem, lower⟩
  · rintro (⟨same, rfl⟩ | ⟨inRest, inTail, lower⟩)
    · exact common_at_equal_heads first rest ready same
    · intro cursor member
      rcases List.mem_cons.mp member with equal | member
      · subst cursor
        rw [view_cons first.range first.positive]
        exact List.mem_cons.mpr (Or.inr inTail)
      · exact inRest cursor member

def addStep (first : Active Key) (rest : List (Active Key)) (charge : Nat)
    (result : Result Key) : Result Key :=
  if first.head = (last first rest).head then result.hit first.head
  else result.skip charge

def run : Nat → List (Active Key) → Option (Result Key)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, first :: rest =>
      let advanced := successor first rest
      if positive : 0 < advanced.1.width then
        (run fuel (rest ++ [⟨advanced.1, positive⟩])).map (addStep first rest advanced.2)
      else some (addStep first rest advanced.2 ⟨[], 0, 0⟩)

omit [LinearOrder Key] in
theorem sizes_positive (cursors : List (Active Key)) :
    ∀ size ∈ sizes cursors, 0 < size := by
  intro size member
  obtain ⟨cursor, _, rfl⟩ := List.mem_map.mp member
  exact cursor.positive

omit [LinearOrder Key] in
theorem rotated_common (rest : List (Active Key)) (next : Active Key) (key : Key) :
    Common (rest ++ [next]) key ↔ Common rest key ∧ key ∈ next.range.view := by
  simp only [Common, List.mem_append, List.mem_singleton, or_imp, forall_and]
  simp

/-- A sufficiently fueled run terminates, delivers exactly the sorted common
keys, and generates the very rotation trace used by the progress bound. -/
theorem run_spec (fuel : Nat) (cursors : List (Active Key))
    (nonempty : cursors ≠ []) (ready : Ready cursors)
    (sorted : ∀ cursor ∈ cursors, cursor.range.Sorted)
    (budget : (sizes cursors).sum ≤ fuel) :
    ∃ result, run fuel cursors = some result ∧
      (∀ key, key ∈ result.keys ↔ Common cursors key) ∧
      result.keys.Pairwise (· < ·) ∧
      CyclicProgress.Execution (sizes cursors) result.advances := by
  induction fuel generalizing cursors with
  | zero =>
      cases cursors with
      | nil => exact False.elim (nonempty rfl)
      | cons first rest =>
          have positive := first.positive
          simp only [sizes, List.map_cons, List.sum_cons] at budget
          omega
  | succ fuel ih =>
      cases cursors with
      | nil => exact False.elim (nonempty rfl)
      | cons first rest =>
          have firstSorted := sorted first (by simp)
          have progress := successor_progress first rest
          by_cases positive : 0 < (successor first rest).1.width
          · let next : Active Key := ⟨(successor first rest).1, positive⟩
            have nextReady := successor_ready first rest ready firstSorted positive
            have nextSorted : ∀ cursor ∈ rest ++ [next], cursor.range.Sorted := by
              intro cursor member
              rcases List.mem_append.mp member with member | member
              · exact sorted cursor (by simp [member])
              · have equal := List.mem_singleton.mp member
                subst cursor
                exact successor_sorted first rest firstSorted
            have nextBudget : (sizes (rest ++ [next])).sum ≤ fuel := by
              simp only [sizes, List.map_append, List.map_cons, List.map_nil,
                List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] at budget ⊢
              dsimp [next]
              omega
            obtain ⟨result, completed, members, ordered, trace⟩ :=
              ih (rest ++ [next]) (by simp) nextReady nextSorted nextBudget
            refine ⟨addStep first rest (successor first rest).2 result, ?_, ?_, ?_, ?_⟩
            · rw [run, dif_pos positive]
              change (run fuel (rest ++ [next])).map (addStep first rest (successor first rest).2) = _
              rw [completed]
              rfl
            · intro key
              have step := successor_exact first rest ready sorted key
              have remaining := (members key).trans (rotated_common rest next key)
              unfold addStep
              split
              next equal =>
                simp only [Result.hit, List.mem_cons, remaining]
                simpa only [equal, true_and] using step.symm
              next different =>
                simp only [Result.skip, remaining]
                simpa only [different, false_and, false_or] using step.symm
            · unfold addStep
              split
              · apply List.pairwise_cons.mpr
                refine ⟨?_, ordered⟩
                intro key member
                have inNext := ((rotated_common rest next key).mp ((members key).mp member)).2
                have tailMem := ((successor_membership first rest firstSorted key).mp inNext).1
                exact tail_value_gt first firstSorted key tailMem
              · exact ordered
            · have step := CyclicProgress.Execution.step (sizes_positive (first :: rest))
                progress (show CyclicProgress.Execution (sizes rest ++ [(successor first rest).1.width])
                  result.advances by simpa [sizes, next] using trace)
              unfold addStep
              split <;> exact step
          · have empty : (successor first rest).1.width = 0 := by omega
            have viewEmpty := view_empty (successor first rest).1 empty
            refine ⟨addStep first rest (successor first rest).2 ⟨[], 0, 0⟩,
              by simp only [run, dif_neg positive], ?_, ?_, ?_⟩
            · intro key
              have step := successor_exact first rest ready sorted key
              rw [viewEmpty] at step
              unfold addStep
              split
              next equal =>
                simpa only [Result.hit, List.mem_cons, List.not_mem_nil, or_false,
                  equal, true_and, and_false] using step.symm
              next different =>
                simpa only [Result.skip, List.not_mem_nil, different, false_and,
                  and_false, or_self] using step.symm
            · unfold addStep
              split <;> simp [Result.hit, Result.skip]
            · have terminal := CyclicProgress.Execution.exhausted
                (sizes rest ++ [(successor first rest).1.width]) (by simp [empty])
              have step := CyclicProgress.Execution.step (sizes_positive (first :: rest)) progress terminal
              unfold addStep
              split <;> exact step

theorem addStep_advances (first : Active Key) (rest : List (Active Key)) (charge : Nat)
    (result : Result Key) :
    (addStep first rest charge result).advances = result.advances + 1 := by
  unfold addStep
  split <;> rfl

theorem addStep_comparisons (first : Active Key) (rest : List (Active Key)) (result : Result Key) :
    (addStep first rest (successor first rest).2 result).comparisons =
      result.comparisons + (successor first rest).2 := by
  unfold addStep successor
  split <;> simp [Result.hit, Result.skip]

theorem successor_comparisons (first : Active Key) (rest : List (Active Key))
    (k : Nat) (bounded : first.range.width < 2 ^ k) : (successor first rest).2 ≤ k := by
  unfold successor
  split
  · exact Nat.zero_le _
  · apply seek_comparisons
    rw [tail_width]
    omega

theorem run_comparisons (fuel : Nat) (cursors : List (Active Key)) (k : Nat)
    (bounded : ∀ cursor ∈ cursors, cursor.range.width < 2 ^ k)
    (result : Result Key) (completed : run fuel cursors = some result) :
    result.comparisons ≤ result.advances * k := by
  induction fuel generalizing cursors result with
  | zero => simp only [run] at completed; cases completed
  | succ fuel ih =>
      cases cursors with
      | nil => simp only [run] at completed; cases completed
      | cons first rest =>
          have charge := successor_comparisons first rest k (bounded first (by simp))
          rw [run] at completed
          split at completed
          next positive =>
            obtain ⟨nextResult, nextRun, rfl⟩ := Option.map_eq_some_iff.mp completed
            have nextBounded : ∀ cursor ∈ rest ++ [⟨(successor first rest).1, positive⟩],
                cursor.range.width < 2 ^ k := by
              intro cursor member
              rcases List.mem_append.mp member with member | member
              · exact bounded cursor (by simp [member])
              · have equal := List.mem_singleton.mp member
                subst cursor
                exact (successor_progress first rest).trans (bounded first (by simp))
            have next := ih _ nextBounded nextResult nextRun
            rw [addStep_comparisons, addStep_advances]
            nlinarith
          next empty =>
            cases Option.some.inj completed
            rw [addStep_comparisons, addStep_advances]
            simpa using charge

end Mettapedia.Machines.Cursor.IndexedCyclicIntersection

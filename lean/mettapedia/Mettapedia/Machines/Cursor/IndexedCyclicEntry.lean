import Mettapedia.Machines.Cursor.IndexedCyclicIntersection
import Mettapedia.Machines.Cursor.IndexedMultiwayProjection

/-!
# Preparing and charging cyclic indexed intersection

Empty projections terminate successfully; an empty family declines. Initial
head ordering uses a counted insertion sort. All initial comparisons and all
binary-seek comparisons belong to the returned execution. Range construction
and the physical implementation of random access remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.IndexedCyclicEntry

open IndexedIntersection IndexedCyclicIntersection

variable {Key : Type} [LinearOrder Key]

def insert (cursor : Active Key) : List (Active Key) → List (Active Key) × Nat
  | [] => ([cursor], 0)
  | first :: rest =>
      if cursor.head ≤ first.head then (cursor :: first :: rest, 1)
      else let tail := insert cursor rest
           (first :: tail.1, tail.2 + 1)

theorem insert_perm (cursor : Active Key) (cursors : List (Active Key)) :
    (insert cursor cursors).1.Perm (cursor :: cursors) := by
  induction cursors with
  | nil => exact List.Perm.refl _
  | cons first rest ih =>
      rw [insert]
      split
      · exact List.Perm.refl _
      · exact (ih.cons first).trans (List.Perm.swap cursor first rest)

theorem insert_ready (cursor : Active Key) (cursors : List (Active Key))
    (ready : Ready cursors) : Ready (insert cursor cursors).1 := by
  induction cursors with
  | nil => simp [insert, Ready]
  | cons first rest ih =>
      have ordered := List.pairwise_cons.mp ready
      rw [insert]
      split
      next before =>
        apply List.pairwise_cons.mpr
        refine ⟨?_, ready⟩
        intro other member
        rcases List.mem_cons.mp member with same | member
        · subst other; exact before
        · exact before.trans (ordered.1 other member)
      next after =>
        apply List.pairwise_cons.mpr
        refine ⟨?_, ih ordered.2⟩
        intro other member
        have original := (insert_perm cursor rest).mem_iff.mp member
        rcases List.mem_cons.mp original with same | member
        · subst other; exact le_of_lt (lt_of_not_ge after)
        · exact ordered.1 other member

theorem insert_comparisons (cursor : Active Key) (cursors : List (Active Key)) :
    (insert cursor cursors).2 ≤ cursors.length := by
  induction cursors with
  | nil => simp [insert]
  | cons first rest ih =>
      rw [insert]
      split <;> simp only [List.length_cons] <;> omega

def arrange : List (Active Key) → List (Active Key) × Nat
  | [] => ([], 0)
  | cursor :: rest =>
      let tail := arrange rest
      let placed := insert cursor tail.1
      (placed.1, tail.2 + placed.2)

theorem arrange_perm (cursors : List (Active Key)) :
    (arrange cursors).1.Perm cursors := by
  induction cursors with
  | nil => exact List.Perm.refl _
  | cons cursor rest ih => exact (insert_perm cursor _).trans (ih.cons cursor)

theorem arrange_ready (cursors : List (Active Key)) : Ready (arrange cursors).1 := by
  induction cursors with
  | nil => simp [arrange, Ready]
  | cons cursor rest ih => exact insert_ready cursor _ ih

theorem arrange_comparisons (cursors : List (Active Key)) :
    (arrange cursors).2 ≤ cursors.length ^ 2 := by
  induction cursors with
  | nil => simp [arrange]
  | cons cursor rest ih =>
      have insertion := insert_comparisons cursor (arrange rest).1
      rw [(arrange_perm rest).length_eq] at insertion
      change (arrange rest).2 + (insert cursor (arrange rest).1).2 ≤ (rest.length + 1) ^ 2
      nlinarith

def activate : List (Range Key) → Option (List (Active Key))
  | [] => some []
  | range :: rest =>
      if positive : 0 < range.width then
        (activate rest).map (fun cursors => ⟨range, positive⟩ :: cursors)
      else none

omit [LinearOrder Key] in
theorem activate_exact (ranges : List (Range Key)) (cursors : List (Active Key))
    (loaded : activate ranges = some cursors) : cursors.map Active.range = ranges := by
  induction ranges generalizing cursors with
  | nil => simpa [activate] using loaded.symm
  | cons range rest ih =>
      rw [activate] at loaded
      split at loaded
      · obtain ⟨tail, next, rfl⟩ := Option.map_eq_some_iff.mp loaded
        simpa using congrArg (List.cons range) (ih tail next)
      · cases loaded

omit [LinearOrder Key] in
theorem activate_none (ranges : List (Range Key)) :
    activate ranges = none ↔ ∃ range ∈ ranges, range.width = 0 := by
  induction ranges with
  | nil => simp [activate]
  | cons range rest ih =>
      rw [activate]
      split
      next positive =>
        simpa [positive.ne', Option.map_eq_none_iff] using ih
      next empty =>
        have zero : range.width = 0 := by omega
        simp [zero]

structure Result (Key : Type*) where
  navigation : IndexedIntersection.Result Key
  initialComparisons : Nat
  deriving Repr, DecidableEq

def intersect (ranges : List (Range Key)) : Option (Result Key) :=
  if ranges.isEmpty then none
  else match activate ranges with
    | none => some ⟨⟨[], 0, 0⟩, 0⟩
    | some cursors =>
        let ordered := arrange cursors
        (run (sizes ordered.1).sum ordered.1).map (fun result => ⟨result, ordered.2⟩)

/-- Exactness and logarithmic seeking are proved for the same computed
result, including the empty-projection case. -/
theorem intersect_spec (ranges : List (Range Key)) (nonempty : ranges ≠ [])
    (sorted : ∀ range ∈ ranges, range.Sorted) (maximum : Nat)
    (bounded : ∀ range ∈ ranges, range.width ≤ maximum) :
    ∃ result, intersect ranges = some result ∧
      (∀ key, key ∈ result.navigation.keys ↔ ∀ range ∈ ranges, key ∈ range.view) ∧
      result.navigation.keys.Pairwise (· < ·) ∧
      result.initialComparisons ≤ ranges.length ^ 2 ∧
      (∀ range ∈ ranges, result.navigation.advances ≤ 2 * ranges.length * range.width) ∧
      result.navigation.comparisons ≤ result.navigation.advances * seekBudget maximum := by
  have active : ranges.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
  cases loaded : activate ranges with
  | none =>
      obtain ⟨empty, member, zero⟩ := (activate_none ranges).mp loaded
      refine ⟨⟨⟨[], 0, 0⟩, 0⟩, by simp [intersect, active, loaded], ?_, by simp,
        Nat.zero_le _, ?_, by simp⟩
      · intro key
        simp only [List.not_mem_nil, false_iff]
        intro all
        have impossible := all empty member
        rw [view_empty empty zero] at impossible
        exact List.not_mem_nil impossible
      · intro range member
        exact Nat.zero_le _
  | some cursors =>
      have representation := activate_exact ranges cursors loaded
      have cursorsNonempty : cursors ≠ [] := by
        intro empty
        simp only [empty, List.map_nil] at representation
        exact nonempty representation.symm
      have perm := arrange_perm cursors
      have orderedNonempty : (arrange cursors).1 ≠ [] := by
        intro empty
        have := perm.length_eq
        rw [empty] at this
        exact cursorsNonempty (List.length_eq_zero_iff.mp this.symm)
      have orderedSorted : ∀ cursor ∈ (arrange cursors).1, cursor.range.Sorted := by
        intro cursor member
        apply sorted cursor.range
        rw [← representation]
        exact List.mem_map.mpr ⟨cursor, perm.mem_iff.mp member, rfl⟩
      have orderedBounded : ∀ cursor ∈ (arrange cursors).1,
          cursor.range.width < 2 ^ seekBudget maximum := by
        intro cursor member
        apply width_lt_budget
        apply bounded cursor.range
        rw [← representation]
        exact List.mem_map.mpr ⟨cursor, perm.mem_iff.mp member, rfl⟩
      have length : (arrange cursors).1.length = ranges.length := by
        rw [perm.length_eq, ← representation, List.length_map]
      obtain ⟨navigation, completed, members, ordered, trace⟩ :=
        run_spec (sizes (arrange cursors).1).sum (arrange cursors).1 orderedNonempty
          (arrange_ready cursors) orderedSorted le_rfl
      refine ⟨⟨navigation, (arrange cursors).2⟩, ?_, ?_, ordered, ?_, ?_, ?_⟩
      · simp only [intersect, active, Bool.false_eq_true, ↓reduceIte, loaded, completed,
          Option.map_some]
      · intro key
        rw [members]
        constructor
        · intro common range member
          rw [← representation] at member
          obtain ⟨cursor, inCursors, rfl⟩ := List.mem_map.mp member
          exact common cursor (perm.mem_iff.mpr inCursors)
        · intro common cursor member
          apply common cursor.range
          rw [← representation]
          exact List.mem_map.mpr ⟨cursor, perm.mem_iff.mp member, rfl⟩
      · have charge := arrange_comparisons cursors
        simpa only [← representation, List.length_map] using charge
      · intro range member
        rw [← representation] at member
        obtain ⟨cursor, inCursors, rfl⟩ := List.mem_map.mp member
        have widthMember : cursor.range.width ∈ sizes (arrange cursors).1 :=
          List.mem_map.mpr ⟨cursor, perm.mem_iff.mpr inCursors, rfl⟩
        have bound := CyclicProgress.bound_by_any_cursor trace widthMember
        have positive := cursor.positive
        simp only [sizes, List.length_map, length] at bound
        have scale := Nat.mul_le_mul_left ranges.length (show cursor.range.width + 1 ≤
          2 * cursor.range.width by omega)
        nlinarith
      · exact run_comparisons _ _ _ orderedBounded navigation completed

/-- Ledger projection only. The executable `intersect` retains its refusal
status, and region adapters must not interpret a refusal as absence. -/
def receipt (ranges : List (Range Key)) : Result Key :=
  (intersect ranges).getD ⟨⟨[], 0, 0⟩, 0⟩

def keys (ranges : List (Range Key)) : List Key := (receipt ranges).navigation.keys

theorem keys_eq_probing (ranges : List (Range Key))
    (sorted : ∀ range ∈ ranges, range.Sorted) :
    keys ranges = IndexedMultiwayProjection.keys ranges := by
  by_cases empty : ranges = []
  · subst ranges
    rfl
  let maximum := (ranges.map Range.width).sum
  have bounded : ∀ range ∈ ranges, range.width ≤ maximum := by
    intro range member
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨range, member, rfl⟩)
  obtain ⟨result, completed, members, ordered, _⟩ := intersect_spec ranges empty sorted maximum bounded
  have chosen : ∃ seed, IndexedMultiwayProjection.selected ranges = some seed := by
    cases selected : IndexedMultiwayProjection.selected ranges with
    | none => exact False.elim (empty (List.argmin_eq_none.mp selected))
    | some seed => exact ⟨seed, rfl⟩
  obtain ⟨seed, selected⟩ := chosen
  obtain ⟨probeCompleted, probeMembers, probeOrdered, _⟩ :=
    IndexedMultiwayProjection.selected_spec selected sorted (seekBudget maximum)
      (fun range member => width_lt_budget range maximum (bounded range member))
  simp only [keys, receipt, completed, Option.getD_some,
    IndexedMultiwayProjection.keys, probeCompleted]
  exact ordered.eq_of_mem_iff probeOrdered (fun key => (members key).trans (probeMembers key).symm)

/-- A navigation event allowance. It includes initial head ordering, bounded
list traversal/rotation per advance, midpoint comparisons and key delivery.
It excludes index preparation, random-reader implementation and leaf work. -/
def workBound (ranges : List (Range Key)) : Nat :=
  let result := receipt ranges
  4 * ranges.length + 2 * result.initialComparisons +
    (3 * ranges.length + 4) * result.navigation.advances +
    result.navigation.comparisons + result.navigation.keys.length

theorem work_bound (ranges : List (Range Key)) (nonempty : ranges ≠ [])
    (sorted : ∀ range ∈ ranges, range.Sorted) (maximum : Nat)
    (bounded : ∀ range ∈ ranges, range.width ≤ maximum) :
    workBound ranges ≤ 4 * ranges.length + 2 * ranges.length ^ 2 +
      2 * ranges.length * IndexedMultiwayProjection.minimumWidth ranges *
        (3 * ranges.length + 4 + seekBudget maximum) + (keys ranges).length := by
  obtain ⟨result, completed, _, _, initial, advances, comparisons⟩ :=
    intersect_spec ranges nonempty sorted maximum bounded
  have chosen : ∃ seed, IndexedMultiwayProjection.selected ranges = some seed := by
    cases selected : IndexedMultiwayProjection.selected ranges with
    | none => exact False.elim (nonempty (List.argmin_eq_none.mp selected))
    | some seed => exact ⟨seed, rfl⟩
  obtain ⟨seed, selected⟩ := chosen
  have bound := advances seed (IndexedMultiwayProjection.selected_member selected)
  have scaled := Nat.mul_le_mul_right (3 * ranges.length + 4 + seekBudget maximum) bound
  simp only [workBound, keys, receipt, completed, Option.getD_some,
    IndexedMultiwayProjection.minimumWidth, selected]
  nlinarith

theorem sum_min_work_bound (stages : List (List (Range Key))) (maximum width : Nat)
    (nonempty : ∀ stage ∈ stages, stage ≠ [])
    (sorted : ∀ stage ∈ stages, ∀ range ∈ stage, range.Sorted)
    (bounded : ∀ stage ∈ stages, ∀ range ∈ stage, range.width ≤ maximum)
    (arity : ∀ stage ∈ stages, stage.length ≤ width) :
    (stages.map workBound).sum ≤ stages.length * (4 * width + 2 * width ^ 2) +
      IndexedMultiwayProjection.sumMin stages * (2 * width * (3 * width + 4 + seekBudget maximum)) +
      IndexedMultiwayProjection.delivered stages := by
  have pointwise : ∀ stage ∈ stages, workBound stage ≤ (4 * width + 2 * width ^ 2) +
      IndexedMultiwayProjection.minimumWidth stage * (2 * width * (3 * width + 4 + seekBudget maximum)) +
      (IndexedMultiwayProjection.keys stage).length := by
    intro stage member
    have localBound := work_bound stage (nonempty stage member) (sorted stage member)
      maximum (bounded stage member)
    rw [keys_eq_probing stage (sorted stage member)] at localBound
    have size := arity stage member
    have squared := Nat.pow_le_pow_left size 2
    have firstScale := Nat.mul_le_mul_right (IndexedMultiwayProjection.minimumWidth stage)
      (Nat.mul_le_mul_left 2 size)
    have lastScale : 3 * stage.length + 4 + seekBudget maximum ≤
        3 * width + 4 + seekBudget maximum := by omega
    have scaled := Nat.mul_le_mul firstScale lastScale
    nlinarith
  have summed := List.sum_le_sum (l := stages) pointwise
  simpa [IndexedMultiwayProjection.sumMin, IndexedMultiwayProjection.delivered,
    List.sum_map_add, List.map_const', List.sum_replicate, smul_eq_mul,
    List.sum_map_mul_right, List.map_map, Function.comp_def] using summed

namespace Controls

def small : Range Nat := Range.ofArray #[2, 8] 0
def wide : Range Nat := Range.ofArray #[0, 1, 2, 3, 4, 5, 8, 9] 0
def other : Range Nat := Range.ofArray #[1, 2, 6, 8] 0

theorem three_way_intersection : keys [wide, small, other] = [2, 8] := by decide +kernel

theorem permuted_family_same_keys : keys [other, wide, small] = [2, 8] := by decide +kernel

theorem empty_projection_is_success :
    intersect [wide, Range.ofArray (#[] : Array Nat) 0, small] =
      some ⟨⟨[], 0, 0⟩, 0⟩ := by decide +kernel

theorem empty_family_declines : intersect ([] : List (Range Nat)) = none := rfl

theorem zero_fuel_does_not_mean_absence :
    run 0 [⟨small, by decide⟩] = none := rfl

theorem unsorted_range_loses_a_real_key :
    keys [Range.ofArray #[0, 3, 1] 0, Range.ofArray #[1] 0] = [] := by decide +kernel

theorem unsorted_range_not_admitted : ¬(Range.ofArray #[0, 3, 1] 0).Sorted := by
  intro sorted
  have impossible := sorted 1 2 (by decide) (by decide) (by decide)
  contradiction

end Controls

end Mettapedia.Machines.Cursor.IndexedCyclicEntry

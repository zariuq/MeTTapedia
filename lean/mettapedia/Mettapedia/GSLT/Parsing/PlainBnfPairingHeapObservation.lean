import Mettapedia.GSLT.Parsing.PlainBnfSourceRank
import Mettapedia.GSLT.Parsing.PlainBnfDependencyWorklist
import Mathlib.Data.Multiset.Basic

/-!
# Exact observations of the existing pairing heap

The observer retains every payload occurrence. The operations being proved
are Batteries' merge, combine, and deleteMin; no replacement heap is defined.
The finite-set projection is used only at the pending-position selection
boundary, after the stronger multiset laws have been established.

Source execution and the whole dependency scheduler are separate bridges.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfPairingHeapObservation

open Batteries.PairingHeapImp

variable {α : Type*}

/-- Full payload multiplicity, independent of heap traversal order. -/
def contents : Heap α → Multiset α
  | .nil => 0
  | .node item children siblings => item ::ₘ (contents children + contents siblings)

theorem contents_merge_roots (le : α → α → Bool)
    (left right : α) (lc ls rc rs : Heap α) :
    contents (Heap.merge le (.node left lc ls) (.node right rc rs)) =
      (left ::ₘ contents lc) + (right ::ₘ contents rc) := by
  unfold Heap.merge
  dsimp
  split <;> simp only [contents, add_zero, ← Multiset.singleton_add] <;> ac_rfl

theorem contents_merge (le : α → α → Bool) {left right : Heap α}
    (hl : left.NoSibling) (hr : right.NoSibling) :
    contents (left.merge le right) = contents left + contents right := by
  cases hl with
  | nil => cases hr <;> simp [Heap.merge, contents]
  | node a children =>
      cases hr with
      | nil => simp [Heap.merge, contents]
      | node b other => simpa [contents] using contents_merge_roots le a b children .nil other .nil

theorem contents_combine (le : α → α → Bool) (forest : Heap α) :
    contents (forest.combine le) = contents forest := by
  cases forest with
  | nil => rfl
  | node a children rest =>
      cases rest with
      | nil => rfl
      | node b other tail =>
          rw [Heap.combine, contents_merge le (Heap.noSibling_merge _ _ _)
            (Heap.noSibling_combine _ _), contents_merge_roots, contents_combine le tail]
          simp only [contents, ← Multiset.singleton_add]
          ac_rfl
termination_by forest.size
decreasing_by simp [Heap.size]; omega

theorem contents_deleteMin (le : α → α → Bool) {heap rest : Heap α} {item : α}
    (single : heap.NoSibling) (returned : heap.deleteMin le = some (item, rest)) :
    contents heap = item ::ₘ contents rest := by
  cases single with
  | nil => cases returned
  | node root children =>
      cases returned
      simp [contents, contents_combine]

theorem nodeWF_lower_bound {le : α → α → Bool} [Batteries.TotalBLE le]
    (transitive : ∀ {left middle right}, le left middle = true →
      le middle right = true → le left right = true)
    {root : α} {forest : Heap α} (ordered : forest.NodeWF le root) :
    ∀ item ∈ contents forest, le root item = true := by
  induction forest generalizing root with
  | nil => simp [contents]
  | node child children siblings ihc ihs =>
      obtain ⟨before, childrenOrdered, siblingsOrdered⟩ := ordered
      intro item member
      simp only [contents, Multiset.mem_cons, Multiset.mem_add] at member
      rcases member with same | inside | inside
      · subst item; exact before
      · exact transitive before (ihc childrenOrdered item inside)
      · exact ihs siblingsOrdered item inside

theorem head_minimum {le : α → α → Bool} [Batteries.TotalBLE le]
    (transitive : ∀ {left middle right}, le left middle = true →
      le middle right = true → le left right = true)
    {heap : Heap α} (ordered : heap.WF le) {item : α}
    (returned : heap.head? = some item) :
    item ∈ contents heap ∧ ∀ other ∈ contents heap, le item other = true := by
  cases ordered with
  | nil => cases returned
  | node childrenOrdered =>
      cases returned
      constructor
      · simp [contents]
      · intro other member
        simp only [contents, add_zero, Multiset.mem_cons] at member
        rcases member with same | inside
        · subst other
          exact Batteries.TotalBLE.total (a := _) (b := _) |>.elim id id
        · exact nodeWF_lower_bound (le := le) transitive childrenOrdered other inside

theorem deleteMin_lower_bound {le : α → α → Bool} [Batteries.TotalBLE le]
    (transitive : ∀ {left middle right}, le left middle = true →
      le middle right = true → le left right = true)
    {heap rest : Heap α} (ordered : heap.WF le) {item : α}
    (returned : heap.deleteMin le = some (item, rest)) :
    item ∈ contents heap ∧ rest.WF le ∧
      ∀ other ∈ contents rest, le item other = true := by
  have head : heap.head? = some item := by
    rw [← Heap.deleteMin_fst, returned]
    rfl
  have minimum := head_minimum (le := le) transitive ordered head
  refine ⟨minimum.1, ordered.deleteMin returned, ?_⟩
  intro other member
  apply minimum.2 other
  have single : heap.NoSibling := by cases ordered <;> constructor
  rw [contents_deleteMin _ single returned]
  exact Multiset.mem_cons_of_mem member

/-- The head projected to source positions is the independent finite-set
minimum. Payload multiplicity is not erased in the preceding heap laws. -/
theorem head_map_eq_least {size : Nat} (position : α → Fin size)
    {le : α → α → Bool} [Batteries.TotalBLE le]
    (transitive : ∀ {left middle right}, le left middle = true →
      le middle right = true → le left right = true)
    (order : ∀ left right, le left right = true → position left ≤ position right)
    {heap : Heap α} (ordered : heap.WF le) :
    heap.head?.map position =
      PlainBnfDependencyWorklist.least ((contents heap).map position).toFinset := by
  cases head : heap.head? with
  | none =>
      cases heap with
      | nil => simp [contents, PlainBnfDependencyWorklist.least]
      | node => cases head
  | some item =>
      simp only [Option.map_some]
      symm
      apply (PlainBnfDependencyWorklist.least_some_iff _ _).mpr
      have minimum := head_minimum (le := le) transitive ordered head
      constructor
      · simp only [Multiset.mem_toFinset, Multiset.mem_map]
        exact ⟨item, minimum.1, rfl⟩
      · intro other member
        simp only [Multiset.mem_toFinset, Multiset.mem_map] at member
        obtain ⟨payload, inside, rfl⟩ := member
        exact order item payload (minimum.2 payload inside)

open PlainBnfSourceRank

/-- The concrete structural rank order supplies the selection theorem's
order premise once ranked payloads have their finite source coordinates. -/
theorem ranked_head_map_eq_least {size : Nat} (rank : α → Rank)
    (position : α → Fin size)
    (coordinates : ∀ item, value (rank item) = (position item).val)
    {heap : Heap α}
    (ordered : heap.WF (fun left right => rankLE (rank left) (rank right))) :
    heap.head?.map position =
      PlainBnfDependencyWorklist.least ((contents heap).map position).toFinset := by
  let le := fun left right => rankLE (rank left) (rank right)
  let : Batteries.TotalBLE le := ⟨fun {a b} =>
    Batteries.TotalBLE.total (le := rankLE) (a := rank a) (b := rank b)⟩
  apply head_map_eq_least (le := le) position
    (fun first second => rankLE_trans first second) ?_ ordered
  intro left right before
  have values := (rankLE_iff (rank left) (rank right)).mp before
  simpa only [coordinates, Fin.le_def] using values

theorem duplicate_occurrences_survive_merge :
    let item := Rank.one .zero
    let heap : Heap Rank := .node item .nil .nil
    contents (heap.merge rankLE heap) = item ::ₘ item ::ₘ 0 ∧
      contents (heap.merge rankLE heap) ≠ item ::ₘ 0 := by decide

theorem equal_ranks_do_not_identify_payloads :
    let rank := Rank.one .zero
    let left : Heap (Rank × Nat) := .node (rank, 11) .nil .nil
    let right : Heap (Rank × Nat) := .node (rank, 12) .nil .nil
    contents (left.merge (fun a b => rankLE a.1 b.1) right) =
      (rank, 11) ::ₘ (rank, 12) ::ₘ 0 := by decide

theorem merge_drops_forest_siblings_but_combine_preserves_them :
    let first := Rank.one .zero
    let second := Rank.two .zero
    let forest : Heap Rank := .node first .nil (.node second .nil .nil)
    contents forest = first ::ₘ second ::ₘ 0 ∧
      contents (forest.merge rankLE .nil) = first ::ₘ 0 ∧
      contents (forest.combine rankLE) = contents forest := by decide

theorem unordered_root_does_not_satisfy_WF :
    ¬ (Heap.node (Rank.two .zero) (.node (.one .zero) .nil .nil) .nil).WF rankLE := by
  intro ordered
  have minimum := head_minimum (le := rankLE) rankLE_trans ordered rfl
  have wrong := minimum.2 (.one .zero) (by decide)
  change false = true at wrong
  cases wrong

end Mettapedia.GSLT.Parsing.PlainBnfPairingHeapObservation

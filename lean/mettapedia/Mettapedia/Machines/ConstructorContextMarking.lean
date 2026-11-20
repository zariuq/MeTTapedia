import Mettapedia.Machines.ConstructorContextGC

/-!
# Finite marking constructs a closed retained set

Marking follows actual stored holes, including cells without cached summaries.
Its iteration bound is computed from the allocated-address inventory and the
explicit roots. A complete finite inventory and the heap's no-dangling law
prove stabilization; callers do not supply a closed marked set.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ConstructorContextHeap.Collection.Marking

open Mettapedia.Machines.ConstructorContext

universe u v w
variable {Label : Type u} {Value : Type v} {Summary : Type w}

def children (heap : Heap Label Value Summary) (address : Nat) : Finset Nat :=
  match (heap address).bind Cell.hole with
  | some (.cell child) => {child}
  | _ => ∅

theorem mem_children_iff (heap : Heap Label Value Summary) (address child : Nat) :
    child ∈ children heap address ↔
      ∃ cell, heap address = some cell ∧ cell.hole = some (.cell child) := by
  cases found : heap address with
  | none => simp [children, found]
  | some cell =>
      cases hole : cell.hole with
      | none => simp [children, found, hole]
      | some ref =>
          cases ref with
          | resident value => simp [children, found, hole]
          | cell next => simp [children, found, hole, eq_comm]

def advance (heap : Heap Label Value Summary) (seen : Finset Nat) : Finset Nat :=
  seen ∪ seen.biUnion (children heap)

theorem subset_advance (heap : Heap Label Value Summary) (seen : Finset Nat) :
    seen ⊆ advance heap seen := Finset.subset_union_left

theorem stable_iff_closed (heap : Heap Label Value Summary) (seen : Finset Nat) :
    advance heap seen = seen ↔ Closed heap seen := by
  constructor
  · intro stable address member cell found child hole
    rw [← stable]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨address, member, (mem_children_iff heap address child).mpr ⟨cell, found, hole⟩⟩)
  · intro closed
    apply Finset.Subset.antisymm _ (subset_advance heap seen)
    intro child member
    rcases Finset.mem_union.mp member with old | new
    · exact old
    · obtain ⟨address, known, reachable⟩ := Finset.mem_biUnion.mp new
      obtain ⟨cell, found, hole⟩ := (mem_children_iff heap address child).mp reachable
      exact closed address known cell found child hole

def iterate (heap : Heap Label Value Summary) (roots : Finset Nat) : Nat → Finset Nat
  | 0 => roots
  | count + 1 => advance heap (iterate heap roots count)

theorem roots_subset (heap : Heap Label Value Summary) (roots : Finset Nat) (count : Nat) :
    roots ⊆ iterate heap roots count := by
  induction count with
  | zero => exact Finset.Subset.refl _
  | succ count ih => exact ih.trans (subset_advance heap _)

theorem iterate_subset (heap : Heap Label Value Summary) (roots bound : Finset Nat)
    (within : roots ⊆ bound) (closed : Closed heap bound) (count : Nat) :
    iterate heap roots count ⊆ bound := by
  induction count with
  | zero => exact within
  | succ count ih =>
      intro child member
      rcases Finset.mem_union.mp member with old | new
      · exact ih old
      · obtain ⟨address, known, reachable⟩ := Finset.mem_biUnion.mp new
        obtain ⟨cell, found, hole⟩ := (mem_children_iff heap address child).mp reachable
        exact closed address (ih known) cell found child hole

theorem stable_or_card_growth (heap : Heap Label Value Summary) (roots : Finset Nat)
    (count : Nat) :
    advance heap (iterate heap roots count) = iterate heap roots count ∨
      roots.card + count ≤ (iterate heap roots count).card := by
  induction count with
  | zero => exact Or.inr (by simp [iterate])
  | succ count ih =>
      rcases ih with stable | growth
      · exact Or.inl (by simp only [iterate, stable])
      · by_cases stable : advance heap (iterate heap roots (count + 1)) =
            iterate heap roots (count + 1)
        · exact Or.inl stable
        · apply Or.inr
          by_cases previous : advance heap (iterate heap roots count) = iterate heap roots count
          · exact False.elim (stable (by simp only [iterate, previous]))
          · have strict : iterate heap roots count ⊂ advance heap (iterate heap roots count) :=
              (Finset.ssubset_iff_subset_ne).mpr
                ⟨subset_advance heap _, Ne.symm previous⟩
            have larger := Finset.card_lt_card strict
            change roots.card + (count + 1) ≤ (advance heap (iterate heap roots count)).card
            omega

theorem stabilizes (heap : Heap Label Value Summary) (roots bound : Finset Nat)
    (within : roots ⊆ bound) (closed : Closed heap bound) :
    Closed heap (iterate heap roots (bound.card + 1)) := by
  apply (stable_iff_closed heap _).mp
  rcases stable_or_card_growth heap roots (bound.card + 1) with stable | growth
  · exact stable
  · have bounded := Finset.card_le_card
      (iterate_subset heap roots bound within closed (bound.card + 1))
    omega

def mark (heap : Heap Label Value Summary) (inventory roots : Finset Nat) : Finset Nat :=
  iterate heap roots ((inventory ∪ roots).card + 1)

def CompleteInventory (heap : Heap Label Value Summary) (inventory : Finset Nat) : Prop :=
  ∀ address cell, heap address = some cell → address ∈ inventory

theorem mark_closed (heap : Heap Label Value Summary) (inventory roots : Finset Nat)
    (complete : CompleteInventory heap inventory) (allocated : NoDangling heap) :
    Closed heap (mark heap inventory roots) := by
  apply stabilizes heap roots (inventory ∪ roots) Finset.subset_union_right
  intro address _ cell found child hole
  obtain ⟨target, present⟩ := allocated address cell found child hole
  exact Finset.mem_union_left _ (complete child target present)

theorem roots_marked (heap : Heap Label Value Summary) (inventory roots : Finset Nat) :
    roots ⊆ mark heap inventory roots := roots_subset heap roots _

/-- No address beyond those required by the roots and pointer closure is
introduced. The allocated-address inventory controls termination, not liveness. -/
theorem mark_least (heap : Heap Label Value Summary) (inventory roots kept : Finset Nat)
    (within : roots ⊆ kept) (closed : Closed heap kept) :
    mark heap inventory roots ⊆ kept := iterate_subset heap roots kept within closed _

theorem reachable_trans (heap : Heap Label Value Summary) {root : Ref Value}
    {middle target : Nat} (first : Reaches heap root middle)
    (last : Reaches heap (.cell middle) target) : Reaches heap root target := by
  induction first with
  | here _ => exact last
  | next present hole _ ih => exact .next present hole (ih last)

theorem iterate_reachable (heap : Heap Label Value Summary) (roots : Finset Nat)
    (count : Nat) {address : Nat} (marked : address ∈ iterate heap roots count) :
    ∃ root ∈ roots, Reaches heap (.cell root : Ref Value) address := by
  induction count generalizing address with
  | zero => exact ⟨address, marked, .here address⟩
  | succ count ih =>
      rcases Finset.mem_union.mp marked with old | new
      · exact ih old
      · obtain ⟨parent, known, child⟩ := Finset.mem_biUnion.mp new
        obtain ⟨cell, found, hole⟩ := (mem_children_iff heap parent address).mp child
        obtain ⟨root, member, reachable⟩ := ih known
        exact ⟨root, member, reachable_trans heap reachable (.next found hole (.here address))⟩

theorem mark_iff_reachable (heap : Heap Label Value Summary) (inventory roots : Finset Nat)
    (complete : CompleteInventory heap inventory) (allocated : NoDangling heap) (address : Nat) :
    address ∈ mark heap inventory roots ↔
      ∃ root ∈ roots, Reaches heap (.cell root : Ref Value) address := by
  constructor
  · exact iterate_reachable heap roots _
  · rintro ⟨root, member, reachable⟩
    apply reaches_kept heap _ (mark_closed heap inventory roots complete allocated) reachable
    intro child same
    cases same
    exact roots_marked heap inventory roots member

/-- Extra inventory entries change the finite bound, never the retained set. -/
theorem inventory_independent (heap : Heap Label Value Summary)
    (first second roots : Finset Nat) (firstComplete : CompleteInventory heap first)
    (secondComplete : CompleteInventory heap second) (allocated : NoDangling heap) :
    mark heap first roots = mark heap second roots := by
  ext address
  rw [mark_iff_reachable heap first roots firstComplete allocated,
    mark_iff_reachable heap second roots secondComplete allocated]

theorem collected_inventory (heap : Heap Label Value Summary) (inventory roots : Finset Nat)
    (complete : CompleteInventory heap inventory) :
    CompleteInventory (collect heap (mark heap inventory roots)) inventory := by
  intro address cell present
  exact complete address cell ((present_iff heap _ address cell).mp present).2

theorem recollect_marks_same (heap : Heap Label Value Summary) (inventory roots : Finset Nat)
    (complete : CompleteInventory heap inventory) (allocated : NoDangling heap) :
    mark (collect heap (mark heap inventory roots)) inventory roots = mark heap inventory roots := by
  have closed := mark_closed heap inventory roots complete allocated
  have safe := noDangling heap _ allocated closed
  ext address
  rw [mark_iff_reachable _ inventory roots (collected_inventory heap inventory roots complete) safe,
    mark_iff_reachable heap inventory roots complete allocated]
  apply exists_congr
  intro root
  constructor
  · rintro ⟨member, path⟩
    exact ⟨member, reaches_original heap _ path⟩
  · rintro ⟨member, path⟩
    refine ⟨member, reaches_collected heap _ closed path ?_⟩
    intro child same
    cases same
    exact roots_marked heap inventory roots member

theorem publicRead_marked (algebra : SummaryAlgebra Label Value Summary)
    (heap : Heap Label Value Summary) (inventory roots : Finset Nat)
    (complete : CompleteInventory heap inventory) (allocated : NoDangling heap)
    (root : Ref Value) (known : KeepsRoot roots root) (fuel : Nat) :
    publicRead algebra (collect heap (mark heap inventory roots)) fuel root =
      publicRead algebra heap fuel root := by
  apply (publicRead_congr algebra heap (collect heap (mark heap inventory roots)) fuel root ?_).symm
  intro address reachable
  apply (reachable_cells_exact heap _ (mark_closed heap inventory roots complete allocated) ?_ reachable).symm
  intro child same
  exact roots_marked heap inventory roots (known child same)

end Mettapedia.Machines.ConstructorContextHeap.Collection.Marking

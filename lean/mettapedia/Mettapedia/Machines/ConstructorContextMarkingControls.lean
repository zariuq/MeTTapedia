import Mettapedia.Machines.ConstructorContextMarking

set_option autoImplicit false

namespace Mettapedia.Machines.ConstructorContextHeap.Collection.Marking.Controls

private def node (next : Ref Nat) (cache : Option Nat) : Cell Nat Nat Nat :=
  ⟨⟨1, [], []⟩, some next, cache⟩

private def heap : Heap Nat Nat Nat := fun address =>
  if address = 1 then some (node (.cell 2) (some 10))
  else if address = 2 then some (node (.cell 3) (some 9))
  else if address = 3 then some (node (.cell 4) (some 8))
  else if address = 4 then some (node (.resident 7) (some 7))
  else if address = 9 then some (node (.resident 40) (some 40))
  else none

private def inventory : Finset Nat := {1, 2, 3, 4, 9}

private theorem complete : CompleteInventory heap inventory := by
  intro address cell present
  simp only [heap] at present
  split_ifs at present <;> simp_all [inventory]

private theorem allocated : NoDangling heap := by
  intro address cell present child hole
  simp only [heap] at present
  split_ifs at present <;> simp_all [node]
  all_goals
    subst cell
    simp only [Option.some.injEq] at hole
    cases hole <;> exact ⟨_, rfl⟩

theorem chain_is_marked_and_unreachable_cell_removed :
    mark heap inventory {1} = {1, 2, 3, 4} ∧
      (collect heap (mark heap inventory {1})) 9 = none := by decide +kernel

private def cycleHeap : Heap Nat Nat Nat :=
  put heap 4 (node (.cell 2) none)

theorem cycle_marking_terminates_without_unfolding_the_cycle :
    mark cycleHeap inventory {1} = {1, 2, 3, 4} ∧
      Closed cycleHeap (mark cycleHeap inventory {1}) := by
  constructor
  · decide +kernel
  · rw [← stable_iff_closed]
    decide +kernel

private def draftHeap : Heap Nat Nat Nat := put heap 1 (node (.cell 2) none)

theorem draft_cache_does_not_hide_children :
    mark draftHeap inventory {1} = {1, 2, 3, 4} := by decide +kernel

theorem additional_external_root_is_retained :
    mark heap inventory {1, 9} = inventory := by decide +kernel

theorem every_bounded_public_read_is_preserved (fuel : Nat) :
    publicRead ConstructorContextHeap.Controls.addAlgebra
        (collect heap (mark heap inventory {1})) fuel (.cell 1) =
      publicRead ConstructorContextHeap.Controls.addAlgebra heap fuel (.cell 1) :=
  publicRead_marked _ heap inventory {1} complete allocated (.cell 1)
    (by intro address same; cases same; simp) fuel

theorem repeated_collection_recomputes_the_same_live_set :
    mark (collect heap (mark heap inventory {1})) inventory {1} =
      mark heap inventory {1} := recollect_marks_same heap inventory {1} complete allocated

theorem incomplete_inventory_cannot_justify_the_iteration_bound :
    mark heap ∅ {1} = {1, 2, 3} ∧ ¬ Closed heap (mark heap ∅ {1}) := by
  constructor
  · decide +kernel
  · intro closed
    have child := closed 3 (by decide +kernel) (node (.cell 4) (some 8)) rfl 4 rfl
    exact (by decide +kernel : 4 ∉ mark heap ∅ {1}) child

private def zeroHeap : Heap Nat Nat Nat := fun address =>
  if address = 0 then some (node (.cell 1) none)
  else if address = 1 then some (node (.resident 5) (some 5))
  else none

theorem zero_is_an_address : mark zeroHeap {0, 1} {0} = {0, 1} := by decide +kernel

end Mettapedia.Machines.ConstructorContextHeap.Collection.Marking.Controls

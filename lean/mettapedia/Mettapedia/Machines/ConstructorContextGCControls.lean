import Mettapedia.Machines.ConstructorContextGC

set_option autoImplicit false

namespace Mettapedia.Machines.ConstructorContextHeap.Collection.Controls

open Mettapedia.Machines.ConstructorContext

private def node (label : Nat) (next : Ref Nat) (summary : Option Nat) : Cell Nat Nat Nat :=
  ⟨⟨label, [], []⟩, some next, summary⟩

private def heap : Heap Nat Nat Nat := fun address =>
  if address = 1 then some (node 1 (.cell 2) (some 8))
  else if address = 2 then some (node 2 (.resident 5) (some 7))
  else if address = 3 then some (node 40 (.resident 2) (some 42))
  else none

private def kept : Finset Nat := {1, 2}

private theorem closed : Closed heap kept := by
  intro address member cell present child hole
  simp only [kept, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl
  · simp only [heap, ↓reduceIte, Option.some.injEq] at present
    subst cell
    simp only [node, Option.some.injEq, Ref.cell.injEq] at hole
    subst child
    decide +kernel
  · simp [heap, node] at present
    subst cell
    cases hole

theorem collection_really_removes_a_cell :
    heap 3 ≠ none ∧ collect heap kept 3 = none := by decide +kernel

theorem stable_addresses_and_caches_are_retained :
    collect heap kept 1 = some (node 1 (.cell 2) (some 8)) ∧
      collect heap kept 2 = some (node 2 (.resident 5) (some 7)) := by
  constructor <;> rfl

theorem public_observation_is_preserved :
    publicRead ConstructorContextHeap.Controls.addAlgebra (collect heap kept) 2 (.cell 1) =
      some (8, 8) := by
  rw [publicRead_exact ConstructorContextHeap.Controls.addAlgebra heap kept closed [.cell 1]
    (by intro root member; obtain rfl := List.mem_singleton.mp member
        intro address same; cases same; decide +kernel)
    (.cell 1) (List.mem_singleton_self _) 2]
  decide +kernel

theorem externally_held_root_cannot_be_omitted : ¬ KeepsRoot kept (.cell 3 : Ref Nat) := by
  intro retained
  have absent := retained 3 rfl
  exact (by decide : 3 ∉ kept) absent

theorem retaining_one_root_without_its_child_is_not_closed : ¬ Closed heap {1} := by
  intro closed
  have child := closed 1 (by simp) (node 1 (.cell 2) (some 8)) rfl 2 rfl
  exact (by decide : 2 ∉ ({1} : Finset Nat)) child

private def draftHeap : Heap Nat Nat Nat :=
  put heap 1 (node 1 (.cell 2) none)

theorem draft_metadata_does_not_make_a_pointer_disappear : ¬ Closed draftHeap {1} := by
  intro closed
  have child := closed 1 (by simp) (node 1 (.cell 2) none)
    (put_same heap 1 _) 2 rfl
  exact (by decide : 2 ∉ ({1} : Finset Nat)) child

end Mettapedia.Machines.ConstructorContextHeap.Collection.Controls

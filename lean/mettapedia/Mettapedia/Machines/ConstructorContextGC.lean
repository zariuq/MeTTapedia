import Mettapedia.Machines.ConstructorContextHeap

/-!
# Stable-address collection with explicit roots and pointer closure

Collection removes cells outside a finite retained set without renumbering
addresses. Root inclusion and closure under actual stored pointers imply
preservation of every reachable cell and every bounded public read, including
draft cells and cached summaries. The supplied root inventory must include
external owners. A particular runtime's root discovery and marking algorithm
remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ConstructorContextHeap.Collection

open Mettapedia.Machines.ConstructorContext

universe u v w
variable {Label : Type u} {Value : Type v} {Summary : Type w}

def collect (heap : Heap Label Value Summary) (kept : Finset Nat) : Heap Label Value Summary :=
  fun address => if address ∈ kept then heap address else none

def KeepsRoot (kept : Finset Nat) (root : Ref Value) : Prop :=
  ∀ address, root = .cell address → address ∈ kept

/-- Follow pointers regardless of the readiness or presence of a cache. -/
def Closed (heap : Heap Label Value Summary) (kept : Finset Nat) : Prop :=
  ∀ address ∈ kept, ∀ cell, heap address = some cell →
    ∀ child, cell.hole = some (.cell child) → child ∈ kept

theorem retained (heap : Heap Label Value Summary) (kept : Finset Nat)
    {address : Nat} (member : address ∈ kept) : collect heap kept address = heap address :=
  if_pos member

theorem removed (heap : Heap Label Value Summary) (kept : Finset Nat)
    {address : Nat} (outside : address ∉ kept) : collect heap kept address = none :=
  if_neg outside

theorem present_iff (heap : Heap Label Value Summary) (kept : Finset Nat)
    (address : Nat) (cell : Cell Label Value Summary) :
    collect heap kept address = some cell ↔ address ∈ kept ∧ heap address = some cell := by
  by_cases member : address ∈ kept <;> simp [collect, member]

theorem reaches_kept (heap : Heap Label Value Summary) (kept : Finset Nat)
    (closed : Closed heap kept) {root : Ref Value} {address : Nat}
    (reachable : Reaches heap root address) : KeepsRoot kept root → address ∈ kept := by
  induction reachable with
  | here address => exact fun rootKept => rootKept address rfl
  | @next address target cell next present hole tail ih =>
      intro rootKept
      apply ih
      intro child same
      subst next
      exact closed address (rootKept address rfl) cell present child hole

theorem reachable_cells_exact (heap : Heap Label Value Summary) (kept : Finset Nat)
    (closed : Closed heap kept) {root : Ref Value} (rootKept : KeepsRoot kept root)
    {address : Nat} (reachable : Reaches heap root address) :
    collect heap kept address = heap address :=
  retained heap kept (reaches_kept heap kept closed reachable rootKept)

theorem reaches_original (heap : Heap Label Value Summary) (kept : Finset Nat)
    {root : Ref Value} {address : Nat} (reachable : Reaches (collect heap kept) root address) :
    Reaches heap root address := by
  induction reachable with
  | here address => exact .here address
  | next present hole _ ih =>
      exact .next ((present_iff heap kept _ _).mp present).2 hole ih

theorem reaches_collected (heap : Heap Label Value Summary) (kept : Finset Nat)
    (closed : Closed heap kept) {root : Ref Value} {address : Nat}
    (reachable : Reaches heap root address) :
    KeepsRoot kept root → Reaches (collect heap kept) root address := by
  induction reachable with
  | here address => exact fun _ => .here address
  | @next address target cell next present hole tail ih =>
      intro rootKept
      have childKept : KeepsRoot kept next := by
        intro child same
        subst next
        exact closed address (rootKept address rfl) cell present child hole
      exact .next (by rw [retained heap kept (rootKept address rfl)]; exact present) hole (ih childKept)

/-- Collection neither invents a path nor removes a path from a retained root. -/
theorem reaches_iff (heap : Heap Label Value Summary) (kept : Finset Nat)
    (closed : Closed heap kept) {root : Ref Value} (rootKept : KeepsRoot kept root)
    (address : Nat) :
    Reaches (collect heap kept) root address ↔ Reaches heap root address :=
  ⟨reaches_original heap kept, fun reachable => reaches_collected heap kept closed reachable rootKept⟩

theorem noDangling (heap : Heap Label Value Summary) (kept : Finset Nat)
    (allocated : NoDangling heap) (closed : Closed heap kept) : NoDangling (collect heap kept) := by
  intro address cell present child hole
  obtain ⟨member, original⟩ := (present_iff heap kept address cell).mp present
  obtain ⟨result, found⟩ := allocated address cell original child hole
  exact ⟨result, by rw [retained heap kept (closed address member cell original child hole)]; exact found⟩

/-- Public observations use the existing independent reader, not a new view
defined by collection. The whole cell, its hole and its cache are preserved. -/
theorem publicRead_exact (algebra : SummaryAlgebra Label Value Summary)
    (heap : Heap Label Value Summary) (kept : Finset Nat) (closed : Closed heap kept)
    (roots : List (Ref Value)) (allKept : ∀ root ∈ roots, KeepsRoot kept root)
    (root : Ref Value) (visible : root ∈ roots) (fuel : Nat) :
    publicRead algebra (collect heap kept) fuel root = publicRead algebra heap fuel root := by
  apply (publicRead_congr algebra heap (collect heap kept) fuel root ?_).symm
  intro address reachable
  exact (reachable_cells_exact heap kept closed (allKept root visible) reachable).symm

theorem idempotent (heap : Heap Label Value Summary) (kept : Finset Nat) :
    collect (collect heap kept) kept = collect heap kept := by
  funext address
  by_cases member : address ∈ kept <;> simp [collect, member]

end Mettapedia.Machines.ConstructorContextHeap.Collection

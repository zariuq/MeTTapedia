import Mettapedia.Machines.ResourceTraceWork

/-!
# Occurrence tests on a shared, fixed graph

An occurs check asks whether any reachable node is the target variable. Its
observation is Boolean, so repeated paths to a node need not be expanded again.
The heap and target are fixed for one check; bindings may change between checks.
The existing worklist tracer supplies finite-graph traversal and termination.

The list-frontier projection below justifies leaving duplicate pending pointers
on a native stack and discarding them when popped. This concerns graph search,
not the correctness of the native binding dereferencer or pointer lifetimes.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.GraphOccurrence

open ResourceOwnership ResourceOwnership.TraceWork

universe u v
variable {Address : Type} {Value : Type u} {Owner : Type v}
  [LinearOrder Address]

/-- The independent meaning of a positive occurrence test. -/
def Occurs (heap : Heap Address Value) (roots : Roots Owner Address)
    (hit : Address → Bool) : Prop :=
  ∃ address, Live heap roots address ∧ hit address = true

/-- Reuse the executable finite-graph tracer, then short-circuit its visit list. -/
def check (heap : Heap Address Value) (roots : Roots Owner Address)
    (hit : Address → Bool) : Bool :=
  (trace heap roots).expanded.any hit

theorem check_correct (heap : Heap Address Value) (roots : Roots Owner Address)
    (hit : Address → Bool) :
    check heap roots hit = true ↔ Occurs heap roots hit := by
  simp only [check, List.any_eq_true, trace_expanded_iff_live, Occurs]

theorem check_expands_once (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).expanded.Nodup := trace_expanded_nodup heap roots

/-- A hit need not wait for the remaining pending nodes. -/
theorem pending_hit (heap : Heap Address Value) (roots : Roots Owner Address)
    (state : State Address) (invariant : Invariant heap roots state)
    (hit : Address → Bool) (address : Address)
    (pending : address ∈ state.pending) (found : hit address = true) :
    Occurs heap roots hit :=
  ⟨address, invariant.pending_live address pending, found⟩

/-- An exhausted, hit-free traversal excludes every reachable target. -/
theorem exhausted_no_hit (heap : Heap Address Value) (roots : Roots Owner Address)
    (state : State Address) (invariant : Invariant heap roots state)
    (empty : state.pending = ∅) (hit : Address → Bool)
    (absent : ∀ address ∈ state.seen, hit address = false) :
    ¬ Occurs heap roots hit := by
  intro ⟨address, live, found⟩
  have member : address ∈ state.seen := by
    rw [exhausted_seen heap roots state invariant empty, mem_footprint]
    exact live
  have := absent address member
  simp [found] at this

/-- The abstract pending set omits already expanded stack entries. -/
def project (seen : Finset Address) (pending : List Address) : State Address :=
  ⟨seen, pending.toFinset \ seen⟩

/-- Popping a duplicate does not change the abstract frontier. -/
theorem pop_seen (seen : Finset Address) (pending : List Address)
    (address : Address) (member : address ∈ seen) :
    project seen (address :: pending) = project seen pending := by
  unfold project
  congr 1
  ext node
  simp only [List.toFinset_cons, Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨same | old, fresh⟩
    · subst node
      exact False.elim (fresh member)
    · exact ⟨old, fresh⟩
  · intro h
    exact ⟨Or.inr h.1, h.2⟩

/-- Expanding a fresh stack entry is the same graph transition, even with
repeated successor slots or a different order of those slots. -/
theorem push_children (seen : Finset Address) (pending children : List Address)
    (address : Address) :
    project (insert address seen) (children ++ pending) =
      advance (project seen (address :: pending)) address children.toFinset := by
  unfold project advance
  congr 1
  ext node
  simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_sdiff,
    Finset.mem_union, Finset.mem_insert]
  tauto

/-- The existing reachability invariant therefore applies to a stack with
lazy duplicate removal, without requiring sorted or unique pending entries. -/
theorem stack_expansion_invariant (heap : Heap Address Value)
    (roots : Roots Owner Address) (seen : Finset Address)
    (pending children : List Address) (address : Address)
    (invariant : Invariant heap roots (project seen (address :: pending)))
    (fresh : address ∉ seen)
    (references : children.toFinset = successors heap address) :
    Invariant heap roots (project (insert address seen) (children ++ pending)) := by
  rw [push_children, references]
  apply advance_invariant heap roots _ invariant
  simp [project, fresh]

namespace Controls

open ResourceOwnership.Examples

theorem cycle_target_found :
    check cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)) (fun a => a == 2) = true := by
  unfold check trace
  change (run cyclicHeap 3 (initial cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)))).expanded.any
    (fun a => a == 2) = true
  simp only [run, expansion_eq]
  decide

theorem unreachable_target_absent :
    check cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)) (fun a => a == 0) = false := by
  unfold check trace
  change (run cyclicHeap 3 (initial cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)))).expanded.any
    (fun a => a == 0) = false
  simp only [run, expansion_eq]
  decide

/-- Checking only a root misses a target reachable through its children. -/
theorem root_only_is_unsound :
    ([(1 : Fin 3)].any (fun a => a == 2)) = false ∧
      check cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)) (fun a => a == 2) = true := by
  exact ⟨by decide, cycle_target_found⟩

end Controls
end Mettapedia.Machines.GraphOccurrence

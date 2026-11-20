import Mettapedia.Ownership.Interface

/-!
# Bounded references as resource-bearing values

The pointer's footprint and the length carried in its record must agree.
Slicing preserves that relation and cannot widen either lifetime or rights.
These laws apply to stack arrays, arenas and uniquely owned resizable buffers;
allocation/reclamation policy is not part of the view representation.

Native projection and integer-width conversion remain separate obligations.
No checksum, allocator success or unspecified C arithmetic is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership

open Mettapedia.Machines.CMemory.Borrowing

structure BoundedView where
  region : Region
  length : Nat
  writing : Bool
  deriving DecidableEq, Repr

def BoundedView.Coherent (view : BoundedView) : Prop := view.length = view.region.count

def BoundedView.slice (view : BoundedView) (offset count : Nat) : Option BoundedView :=
  if offset ≤ view.length ∧ count ≤ view.length - offset then
    some ⟨instantiateView view.region offset count, count, view.writing⟩
  else none

theorem slice_preserves_contract {view child : BoundedView} {offset count : Nat}
    (coherent : view.Coherent) (step : view.slice offset count = some child) :
    child.Coherent ∧ view.region.Contains child.region ∧ child.writing = view.writing := by
  unfold BoundedView.slice at step
  split at step
  · rename_i bounds
    cases Option.some.inj step
    refine ⟨rfl, instantiateView_contained (Nat.le_refl _) ?_, rfl⟩
    unfold BoundedView.Coherent at coherent
    omega
  · contradiction

/-- A byte access through an admitted view lies in a live allocation.
This combines record coherence, bounds, spatial access and allocation life. -/
theorem admitted_view_index_live {s after : State} (valid : Valid s)
    {id index : Nat} {view : BoundedView}
    (admitted : apply s (.view id view.region view.length view.writing) = some after)
    (bound : index < view.length) :
    ∃ allocation ∈ s.allocations,
      allocation.region.Contains (instantiateView view.region index 1) := by
  obtain ⟨coherent, access⟩ := admitted_view_exact admitted
  have inside : index + 1 ≤ view.region.count := by omega
  have subaccess : Access s.loans id (instantiateView view.region index 1) view.writing :=
    access_subfootprint regionGeometry access (instantiateView_contained (Nat.le_refl _) inside)
  obtain ⟨loan, present, _, contains⟩ := access_has_live_loan subaccess
  obtain ⟨allocation, live, rootBounds⟩ := valid.covered loan present
  exact ⟨allocation, live, Region.contains_trans rootBounds contains⟩

theorem admitted_view_write_excludes_alias {s after : State} (valid : Valid s)
    {id other index length : Nat} {view region : Region} {writing : Bool}
    (admitted : apply s (.view id view length true) = some after)
    (bound : index < length) (different : id ≠ other)
    (reader : Access s.loans other region writing) :
    (instantiateView view index 1).Disjoint region := by
  obtain ⟨coherent, access⟩ := admitted_view_exact admitted
  have inside : index + 1 ≤ view.count := by omega
  have subaccess : Access s.loans id (instantiateView view index 1) true :=
    access_subfootprint regionGeometry access (instantiateView_contained (Nat.le_refl _) inside)
  exact exclusive_access_disjoint valid.ordered different subaccess reader

/-- Every framed caller reference stays subject to the same alias rule after
a checked byte routine receives a view. This is independent of its indexing
algorithm; all accesses must stay within the supplied view. -/
theorem view_call_subaccess {s after : State} {id : Nat} {writing : Bool} {part : Region}
    (passed : passArgument s (.viewed writing) (.loan id) = some after)
    (bounded : ∀ loan ∈ s.loans, loan.id = id → loan.region.Contains part) :
    Access s.loans id part writing := by
  obtain ⟨loan, present, identity, access⟩ := passed_view_has_access passed
  exact access_subfootprint regionGeometry access (bounded loan present identity)

end Mettapedia.Ownership

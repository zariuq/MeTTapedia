import Mettapedia.Machines.ResourceOwnershipOptimality
import Mettapedia.Machines.RememberedSetTrace

/-!
# Minimum safe promotion across a lifetime boundary

Keep the durable region and the full paths of the exported roots. Cells in
that closure but outside the durable region must acquire storage that survives
the boundary. Preserving only each returned outer value does not suffice.

Addresses here are logical identities; movement requires the separate
relocation contract of `ResourceOwnership`. Weight is per cell and does not
include traversal, synchronization, or foreign finalization. A closed durable
region need not be retraced, but a mutable old-to-young edge still needs the
remembered-set contract.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RegionPromotion

open ResourceOwnership ResourceOwnership.Optimality
open Mettapedia.GSLT.Dynamics.StoreReachability (Reach Store)

universe uValue uOwner

variable {Address : Type} {Value : Type uValue} {Owner : Type uOwner}
  [DecidableEq Address] [DecidableEq Owner]

def boundaryRoots (exports : Roots Owner Address) (owner : Owner)
    (durable : Finset Address) : Roots Owner Address :=
  exports ∪ durable.image (Prod.mk owner)

/-- Discover the footprint once, counting shared descendants once. -/
def toPromote (heap : Heap Address Value) (exports : Roots Owner Address)
    (owner : Owner) (durable : Finset Address) : Finset Address :=
  census heap (boundaryRoots exports owner durable) \ durable

/-- The reference graph after the temporary region is released. This is an
observer-level heap, not a physical relocation implementation. -/
noncomputable def publish (heap : Heap Address Value) (exports : Roots Owner Address)
    (owner : Owner) (durable : Finset Address) : Heap Address Value :=
  collect heap (boundaryRoots exports owner durable)

theorem publish_paths (heap : Heap Address Value) (exports : Roots Owner Address)
    (owner : Owner) (durable : Finset Address) :
    SameRootPaths heap (publish heap exports owner durable)
      (boundaryRoots exports owner durable) :=
  collect_same_root_paths heap _

theorem publish_allocated (heap : Heap Address Value) (exports : Roots Owner Address)
    (owner : Owner) (durable : Finset Address)
    (valid : ValidRoots heap (boundaryRoots exports owner durable)) :
    (publish heap exports owner durable).allocated =
      durable ∪ toPromote heap exports owner durable := by
  have included : durable ⊆ census heap (boundaryRoots exports owner durable) := by
    intro a mem
    have root : (owner, a) ∈ boundaryRoots exports owner durable :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ mem)
    exact (mem_census_iff_live heap _ valid a).mpr
      (live_of_root heap _ root (valid _ root))
  rw [publish, allocated_collect, ← census_eq_footprint heap _ valid]
  ext a
  simp only [toPromote, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro member
    by_cases stored : a ∈ durable
    · exact Or.inl stored
    · exact Or.inr ⟨member, stored⟩
  · rintro (stored | ⟨member, _⟩)
    · exact included stored
    · exact member

/-- Any implementation preserving those paths must retain the same support.
The resource budget says where the implementation can have kept it; closure
and the required addresses are conclusions. -/
theorem toPromote_least (heap candidate : Heap Address Value)
    (exports : Roots Owner Address) (owner : Owner) (durable transferred : Finset Address)
    (valid : ValidRoots heap (boundaryRoots exports owner durable))
    (paths : SameRootPaths heap candidate (boundaryRoots exports owner durable))
    (budget : candidate.allocated ⊆ durable ∪ transferred) :
    toPromote heap exports owner durable ⊆ transferred := by
  intro a member
  obtain ⟨reached, notDurable⟩ := Finset.mem_sdiff.mp member
  have sourceFootprint : a ∈ footprint heap (boundaryRoots exports owner durable) := by
    rwa [← census_eq_footprint heap _ valid]
  rcases Finset.mem_union.mp (budget (footprint_subset_candidate heap candidate _ paths
      sourceFootprint)) with stored | copied
  · exact (notDurable stored).elim
  · exact copied

/-- A per-cell materialization charge may account for bytes or another
nonnegative cost instead of counting cells. -/
theorem promotion_charge_le (heap candidate : Heap Address Value)
    (exports : Roots Owner Address) (owner : Owner) (durable transferred : Finset Address)
    (valid : ValidRoots heap (boundaryRoots exports owner durable))
    (paths : SameRootPaths heap candidate (boundaryRoots exports owner durable))
    (budget : candidate.allocated ⊆ durable ∪ transferred)
    (charge : Address → Nat) :
    (∑ a ∈ toPromote heap exports owner durable, charge a) ≤
      ∑ a ∈ transferred, charge a :=
  Finset.sum_le_sum_of_subset (toPromote_least heap candidate exports owner durable transferred
    valid paths budget)

def ClosedRegion (heap : Heap Address Value) (durable : Finset Address) : Prop :=
  ∀ a ∈ durable, heap.dependencies a ⊆ durable

theorem footprint_of_closed_region (heap : Heap Address Value) (owner : Owner)
    (durable : Finset Address) (stored : durable ⊆ heap.allocated)
    (closed : ClosedRegion heap durable) :
    footprint heap (durable.image (Prod.mk owner)) = durable := by
  ext a
  rw [mem_footprint]
  constructor
  · intro live
    induction live with
    | root root =>
        simpa [rootAddresses, Finset.image_image] using root.2
    | @step parent child _ edge ih =>
        obtain ⟨cell, found, childRef⟩ := edge
        exact closed parent ih (by simpa [Heap.dependencies, found] using childRef)
  · intro member
    exact live_of_root heap _ (Finset.mem_image_of_mem _ member) (stored member)

/-- Old objects with no edges into the temporary region add no work to the
export's promotion footprint. -/
theorem toPromote_closed_region (heap : Heap Address Value) (exports : Roots Owner Address)
    (owner : Owner) (durable : Finset Address)
    (valid : ValidRoots heap (boundaryRoots exports owner durable))
    (stored : durable ⊆ heap.allocated) (closed : ClosedRegion heap durable) :
    toPromote heap exports owner durable = footprint heap exports \ durable := by
  rw [toPromote, census_eq_footprint heap _ valid, boundaryRoots, footprint_union,
    footprint_of_closed_region heap owner durable stored closed]
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

/-- A trace through the temporary region only. Its roots are the exported
roots in that region. Edges into durable storage need not be followed. -/
def temporaryStore (heap : Heap Address Value) (exports : Roots Owner Address)
    (durable : Finset Address) : Store Address where
  pointsTo a b := a ∉ durable ∧ b ∉ durable ∧ (heap.toStore exports).pointsTo a b
  root a := a ∉ durable ∧ (heap.toStore exports).root a

omit [DecidableEq Owner] in
theorem temporary_reach_iff (heap : Heap Address Value) (exports : Roots Owner Address)
    (durable : Finset Address) (closed : ClosedRegion heap durable) (address : Address) :
    Reach (temporaryStore heap exports durable) address ↔
      Live heap exports address ∧ address ∉ durable := by
  constructor
  · intro reached
    induction reached with
    | root root => exact ⟨.root root.2, root.1⟩
    | step _ edge ih => exact ⟨.step ih.1 edge.2.2, edge.2.1⟩
  · rintro ⟨live, temporary⟩
    induction live with
    | root root => exact .root ⟨temporary, root⟩
    | @step parent child _ edge ih =>
        obtain ⟨cell, found, childRef⟩ := edge
        have parentTemporary : parent ∉ durable := by
          intro parentDurable
          exact temporary (closed parent parentDurable
            (by simpa [Heap.dependencies, found] using childRef))
        exact .step (ih parentTemporary) ⟨parentTemporary, temporary, cell, found, childRef⟩

/-- Exact promotion can be discovered without traversing old objects if
their published region is already closed. -/
theorem mem_toPromote_iff_temporary_reach (heap : Heap Address Value)
    (exports : Roots Owner Address) (owner : Owner) (durable : Finset Address)
    (valid : ValidRoots heap (boundaryRoots exports owner durable))
    (stored : durable ⊆ heap.allocated) (closed : ClosedRegion heap durable)
    (address : Address) :
    address ∈ toPromote heap exports owner durable ↔
      Reach (temporaryStore heap exports durable) address := by
  rw [toPromote_closed_region heap exports owner durable valid stored closed,
    Finset.mem_sdiff, mem_footprint, temporary_reach_iff heap exports durable closed address]

/-- For a closed older region, the existing minor-trace contract requires
no remembered sources. Mutability alone is not the criterion: an actual
edge across the cut is. -/
theorem barrier_free_iff_closed (heap : Heap Address Value) (durable : Finset Address) :
    RememberedSetTrace.Barrier (heap.toStore (∅ : Roots Unit Address)).pointsTo
      (fun a => a ∈ durable) (fun _ => False) ↔ ClosedRegion heap durable := by
  classical
  constructor
  · intro barrier a mem b depends
    cases found : heap.lookup a with
    | none => simp [Heap.dependencies, found] at depends
    | some cell =>
        by_contra missing
        exact barrier a b ⟨cell, found, by simpa [Heap.dependencies, found] using depends⟩
          mem missing
  · intro closed a b edge mem missing
    obtain ⟨cell, found, reference⟩ := edge
    exact missing (closed a mem (by simpa [Heap.dependencies, found] using reference))

namespace Controls

private def heap : Heap Bool Nat where
  lookup a := some (if a then ⟨17, ∅, 8⟩ else ⟨23, {true}, 8⟩)
  allocated := {false, true}
  allocated_iff := by intro a; cases a <;> simp
  closed := by
    intro a c found b _
    cases b <;> decide

/-- The protected outer cell has a temporary child, even with no new
exports. Keeping the outer cell alone is not a safe handback. -/
theorem protected_outer_cell_needs_child :
    toPromote heap (∅ : Roots Unit Bool) () {false} = {true} := by
  decide +kernel

theorem closed_destination_needs_no_copy :
    toPromote heap ({((), true)} : Roots Unit Bool) () {true} = ∅ := by
  decide +kernel

end Controls
end Mettapedia.Machines.RegionPromotion

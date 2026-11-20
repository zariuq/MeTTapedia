import Mettapedia.Machines.ResourceOwnership
import Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone

/-!
# Existing authority occurrences retain the borrowed resource graph

This connects the existing located lease frontier to the existing owner-root
heap. Handles include provider and generation; roots are not reconstructed
from payload equality. Collection may remove unreachable storage while
preserving all cells and paths reachable from an authorized handle.
The native root tracer and allocator remain implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BorrowedRoots

open Mettapedia.Machines.ResourceOwnership
open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone

variable {Provider Resource Holder Value : Type}
  [DecidableEq Provider] [DecidableEq Resource] [DecidableEq Holder]

def roots (frontier : Frontier Provider Resource Holder) : Roots Holder (Handle Provider Resource) :=
  frontier.toFinset.image fun lease => (lease.holder, lease.handle)

theorem root_of_lease (frontier : Frontier Provider Resource Holder)
    (lease : Lease Provider Resource Holder) (member : lease ∈ frontier) :
    (lease.holder, lease.handle) ∈ roots frontier :=
  Finset.mem_image.mpr ⟨lease, Multiset.mem_toFinset.mpr member, rfl⟩

theorem authorized_iff_lease (frontier : Frontier Provider Resource Holder)
    (holder : Holder) (handle : Handle Provider Resource) :
    Authorized frontier holder handle ↔
      ∃ permission, (⟨handle, holder, permission⟩ : Lease Provider Resource Holder) ∈ frontier := by
  simp only [Authorized, authorizedB, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ((owned | shared) | borrowed)
    · exact ⟨.owned, owned⟩
    · exact ⟨.shared, shared⟩
    · exact ⟨.borrowed, borrowed⟩
  · rintro ⟨permission, member⟩
    cases permission with
    | owned => exact Or.inl (Or.inl member)
    | shared => exact Or.inl (Or.inr member)
    | borrowed => exact Or.inr member

theorem authorized_iff_root (frontier : Frontier Provider Resource Holder)
    (holder : Holder) (handle : Handle Provider Resource) :
    Authorized frontier holder handle ↔ (holder, handle) ∈ roots frontier := by
  rw [authorized_iff_lease]
  constructor
  · rintro ⟨permission, member⟩
    exact root_of_lease frontier ⟨handle, holder, permission⟩ member
  · intro member
    obtain ⟨lease, inside, same⟩ := Finset.mem_image.mp member
    rcases lease with ⟨foundHandle, foundHolder, permission⟩
    simp only [Prod.mk.injEq] at same
    rcases same with ⟨rfl, rfl⟩
    exact ⟨permission, Multiset.mem_toFinset.mp inside⟩

theorem authorized_is_live (heap : Heap (Handle Provider Resource) Value)
    (frontier : Frontier Provider Resource Holder) (valid : ValidRoots heap (roots frontier))
    (holder : Holder) (handle : Handle Provider Resource)
    (authorized : Authorized frontier holder handle) : Live heap (roots frontier) handle := by
  have member := (authorized_iff_root frontier holder handle).mp authorized
  exact live_of_root heap (roots frontier) member (valid (holder, handle) member)

theorem authorized_cell_survives_collection (heap : Heap (Handle Provider Resource) Value)
    (frontier : Frontier Provider Resource Holder) (valid : ValidRoots heap (roots frontier))
    (holder : Holder) (handle : Handle Provider Resource)
    (authorized : Authorized frontier holder handle) :
    (collect heap (roots frontier)).lookup handle = heap.lookup handle :=
  lookup_collect_of_live heap _ (authorized_is_live heap frontier valid holder handle authorized)

theorem authorized_descendant_survives_collection (heap : Heap (Handle Provider Resource) Value)
    (frontier : Frontier Provider Resource Holder) (valid : ValidRoots heap (roots frontier))
    (holder : Holder) (handle address : Handle Provider Resource)
    (authorized : Authorized frontier holder handle)
    (dependency : Live heap ({((), handle)} : Roots Unit (Handle Provider Resource)) address) :
    (collect heap (roots frontier)).lookup address = heap.lookup address := by
  have checked : RequestBorrow.retentionCheck heap (roots frontier) [handle] = true :=
    (RequestBorrow.retentionCheck_iff heap _ _).mpr ⟨valid, by
      intro start member
      have same := List.mem_singleton.mp member
      subst start
      exact authorized_is_live heap frontier valid holder handle authorized⟩
  exact RequestBorrow.retentionCheck_preserves_descendant_cell heap _ [handle] checked
    (List.mem_singleton_self _) dependency

theorem share_gives_real_authority (world : World Provider Resource Holder)
    (lease : Lease Provider Resource Holder) (target : Holder)
    (present : lease ∈ world.frontier) (copyable : lease.permission = .shared) :
    Step world (.share lease target)
      ⟨{lease with holder := target} ::ₘ world.frontier,
        world.history ++ [.share lease target]⟩ ∧
      Authorized ({lease with holder := target} ::ₘ world.frontier) target lease.handle := by
  refine ⟨Step.share world lease target present copyable, ?_⟩
  rw [authorized_iff_lease]
  refine ⟨.shared, ?_⟩
  simp [copyable]

#print axioms authorized_iff_root
#print axioms authorized_cell_survives_collection
#print axioms authorized_descendant_survives_collection
#print axioms share_gives_real_authority

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BorrowedRoots

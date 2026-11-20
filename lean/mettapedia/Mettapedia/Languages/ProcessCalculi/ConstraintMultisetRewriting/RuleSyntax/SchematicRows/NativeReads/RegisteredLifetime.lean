import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BorrowedViews

/-!
# Registration retains an owner, not merely a pointer description

A context may outlive the cursor that first produced a row. Actual shared
lease publication followed by release retains the context's authority and
the complete resource graph. A native registry needs this ownership bridge
or an enclosing lifetime that keeps its original borrow valid.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.RegisteredLifetime

open Mettapedia.Machines.ResourceOwnership
open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone

variable {ProviderID Resource Holder Value : Type}
  [DecidableEq ProviderID] [DecidableEq Resource] [DecidableEq Holder]

def retained (frontier : Frontier ProviderID Resource Holder)
    (lease : Lease ProviderID Resource Holder) (context : Holder) : Frontier ProviderID Resource Holder :=
  ({lease with holder := context} ::ₘ frontier).erase lease

theorem retained_roots_valid (heap : Heap (Handle ProviderID Resource) Value)
    (frontier : Frontier ProviderID Resource Holder) (valid : ValidRoots heap (BorrowedRoots.roots frontier))
    (lease : Lease ProviderID Resource Holder) (present : lease ∈ frontier) (context : Holder) :
    ValidRoots heap (BorrowedRoots.roots (retained frontier lease context)) := by
  intro pair member
  obtain ⟨selected, selectedMember, same⟩ := Finset.mem_image.mp member
  have oldOrCopied := Multiset.mem_of_mem_erase (Multiset.mem_toFinset.mp selectedMember)
  rcases Multiset.mem_cons.mp oldOrCopied with copied | old
  · subst selected
    have allocated := valid (lease.holder, lease.handle) (BorrowedRoots.root_of_lease frontier lease present)
    have address := congrArg Prod.snd same
    simpa only [← address] using allocated
  · have allocated := valid (selected.holder, selected.handle) (BorrowedRoots.root_of_lease frontier selected old)
    have address := congrArg Prod.snd same
    simpa only [← address] using allocated

theorem registered_graph_survives_cursor_close (heap : Heap (Handle ProviderID Resource) Value)
    (frontier : Frontier ProviderID Resource Holder) (valid : ValidRoots heap (BorrowedRoots.roots frontier))
    (lease : Lease ProviderID Resource Holder) (present : lease ∈ frontier) (context : Holder)
    (copyable : lease.permission = .shared) (distinct : context ≠ lease.holder)
    (address : Handle ProviderID Resource)
    (dependency : Live heap ({((), lease.handle)} : Roots Unit (Handle ProviderID Resource)) address) :
    Authorized (retained frontier lease context) context lease.handle ∧
      (collect heap (BorrowedRoots.roots (retained frontier lease context))).lookup address = heap.lookup address := by
  have authorized := BorrowedViews.cloned_owner_survives_original_release frontier lease context copyable distinct
  exact ⟨authorized, BorrowedRoots.authorized_descendant_survives_collection heap _
    (retained_roots_valid heap frontier valid lease present context) context lease.handle address authorized dependency⟩

theorem actual_share_then_release (world : World ProviderID Resource Holder)
    (lease : Lease ProviderID Resource Holder) (present : lease ∈ world.frontier) (context : Holder)
    (copyable : lease.permission = .shared) :
    ∃ middle final, Step world (.share lease context) middle ∧ Step middle (.release lease) final ∧
      final.frontier = retained world.frontier lease context := by
  let middle : World ProviderID Resource Holder :=
    ⟨{lease with holder := context} ::ₘ world.frontier, world.history ++ [.share lease context]⟩
  let final : World ProviderID Resource Holder :=
    ⟨retained world.frontier lease context, middle.history ++ [.release lease]⟩
  exact ⟨middle, final, Step.share world lease context present copyable,
    Step.release middle lease (Multiset.mem_cons_of_mem present), rfl⟩

#print axioms retained_roots_valid
#print axioms registered_graph_survives_cursor_close
#print axioms actual_share_then_release

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.RegisteredLifetime

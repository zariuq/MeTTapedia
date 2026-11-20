import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BorrowedRoots

/-!
# Guarded borrowed readback, collection, cloning and release

The physical graph, generation-stamped view and lease transitions are the
existing ones. A lost lease or mismatched lifetime returns invalidation,
never a completed empty read. Retention and authority are checked separately.
This is a sequential model boundary, not a native allocator or C proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BorrowedViews

open Mettapedia.Machines.ResourceOwnership
open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone

variable {Provider Resource Holder Value : Type}
  [DecidableEq Provider] [DecidableEq Resource] [DecidableEq Holder]

abbrev Address (Provider Resource : Type) := Handle Provider Resource

inductive Reply (Address Value : Type) where
  | rows (observations : List (Option (Address × Cell Address Value)))
  | invalidated

def stamp (handle : Handle Provider Resource) : RequestBorrow.Stamp Provider :=
  ⟨handle.provider, handle.generation⟩

def read (region : RequestBorrow.Region Provider (Address Provider Resource) Value)
    (frontier : Frontier Provider Resource Holder) (holder : Holder)
    (handle : Handle Provider Resource) (paths : List (Address Provider Resource × List (Address Provider Resource))) :
    Reply (Address Provider Resource) Value :=
  if authorizedB frontier holder handle then
    match RequestBorrow.read region ⟨stamp handle, paths⟩ with
    | some observations => .rows observations
    | none => .invalidated
  else .invalidated

theorem read_current (region : RequestBorrow.Region Provider (Address Provider Resource) Value)
    (frontier : Frontier Provider Resource Holder) (holder : Holder)
    (handle : Handle Provider Resource) (paths : List (Address Provider Resource × List (Address Provider Resource)))
    (authorized : Authorized frontier holder handle) (current : stamp handle = region.stamp) :
    read region frontier holder handle paths = .rows (RequestBorrow.observe region.heap paths) := by
  change authorizedB frontier holder handle = true at authorized
  simp only [read, if_pos authorized, RequestBorrow.read, if_pos current]

theorem read_without_authority (region : RequestBorrow.Region Provider (Address Provider Resource) Value)
    (frontier : Frontier Provider Resource Holder) (holder : Holder)
    (handle : Handle Provider Resource) (paths : List (Address Provider Resource × List (Address Provider Resource)))
    (denied : ¬ Authorized frontier holder handle) :
    read region frontier holder handle paths = .invalidated := by
  change ¬ authorizedB frontier holder handle = true at denied
  simp only [read, if_neg denied]

theorem read_wrong_generation (region : RequestBorrow.Region Provider (Address Provider Resource) Value)
    (frontier : Frontier Provider Resource Holder) (holder : Holder)
    (handle : Handle Provider Resource) (paths : List (Address Provider Resource × List (Address Provider Resource)))
    (different : handle.generation ≠ region.stamp.epoch) :
    read region frontier holder handle paths = .invalidated := by
  have stale : stamp handle ≠ region.stamp := fun same => different (congrArg RequestBorrow.Stamp.epoch same)
  by_cases authorized : Authorized frontier holder handle
  · change authorizedB frontier holder handle = true at authorized
    simp only [read, if_pos authorized, RequestBorrow.read, if_neg stale]
  · exact read_without_authority region frontier holder handle paths authorized

theorem read_wrong_provider (region : RequestBorrow.Region Provider (Address Provider Resource) Value)
    (frontier : Frontier Provider Resource Holder) (holder : Holder)
    (handle : Handle Provider Resource) (paths : List (Address Provider Resource × List (Address Provider Resource)))
    (different : handle.provider ≠ region.stamp.identity) :
    read region frontier holder handle paths = .invalidated := by
  have stale : stamp handle ≠ region.stamp := fun same => different (congrArg RequestBorrow.Stamp.identity same)
  by_cases authorized : Authorized frontier holder handle
  · change authorizedB frontier holder handle = true at authorized
    simp only [read, if_pos authorized, RequestBorrow.read, if_neg stale]
  · exact read_without_authority region frontier holder handle paths authorized

theorem read_survives_collection (region : RequestBorrow.Region Provider (Address Provider Resource) Value)
    (frontier : Frontier Provider Resource Holder) (valid : ValidRoots region.heap (BorrowedRoots.roots frontier))
    (holder : Holder) (handle : Handle Provider Resource)
    (paths : List (Address Provider Resource × List (Address Provider Resource)))
    (authorized : Authorized frontier holder handle) (current : stamp handle = region.stamp)
    (covered : ∀ path ∈ paths,
      Live region.heap ({((), handle)} : Roots Unit (Address Provider Resource)) path.1) :
    read {region with heap := collect region.heap (BorrowedRoots.roots frontier)} frontier holder handle paths =
      .rows (RequestBorrow.observe region.heap paths) := by
  change authorizedB frontier holder handle = true at authorized
  simp only [read, if_pos authorized, RequestBorrow.read, if_pos current]
  congr 1
  have checked : RequestBorrow.retentionCheck region.heap (BorrowedRoots.roots frontier) [handle] = true :=
    (RequestBorrow.retentionCheck_iff _ _ _).mpr ⟨valid, by
      intro start member
      have same := List.mem_singleton.mp member
      subst start
      exact BorrowedRoots.authorized_is_live region.heap frontier valid holder handle authorized⟩
  apply List.map_congr_left
  intro path member
  exact walk_collect region.heap (BorrowedRoots.roots frontier)
    (RequestBorrow.retentionCheck_protects_descendants _ _ [handle] checked
      (List.mem_singleton_self _) (covered path member)) path.2

theorem read_after_immutable_growth
    (origin current : RequestBorrow.Region Provider (Address Provider Resource) Value)
    (history : RequestBorrow.History origin current)
    (frontier : Frontier Provider Resource Holder) (holder : Holder)
    (handle : Handle Provider Resource) (paths : List (Address Provider Resource × List (Address Provider Resource)))
    (authorized : Authorized frontier holder handle)
    (issued : stamp handle = origin.stamp) (stillCurrent : stamp handle = current.stamp)
    (allocated : ∀ path ∈ paths, path.1 ∈ origin.heap.allocated) :
    read current frontier holder handle paths = .rows (RequestBorrow.observe origin.heap paths) := by
  change authorizedB frontier holder handle = true at authorized
  unfold read
  rw [if_pos authorized, RequestBorrow.read_exact history _ issued stillCurrent allocated]

theorem cloned_owner_survives_original_release (frontier : Frontier Provider Resource Holder)
    (lease : Lease Provider Resource Holder) (target : Holder)
    (copyable : lease.permission = .shared) (distinct : target ≠ lease.holder) :
    Authorized (({lease with holder := target} ::ₘ frontier).erase lease) target lease.handle := by
  rw [BorrowedRoots.authorized_iff_lease]
  refine ⟨.shared, ?_⟩
  have unequal : ({lease with holder := target} : Lease Provider Resource Holder) ≠ lease := by
    intro same
    exact distinct (congrArg Lease.holder same)
  have member := (Multiset.mem_erase_of_ne unequal).mpr
    (Multiset.mem_cons_self ({lease with holder := target}) frontier)
  simpa only [copyable] using member

#print axioms read_survives_collection
#print axioms read_after_immutable_growth
#print axioms read_wrong_generation
#print axioms read_wrong_provider
#print axioms cloned_owner_survives_original_release

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BorrowedViews

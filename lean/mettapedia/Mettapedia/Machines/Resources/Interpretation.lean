import Mettapedia.Machines.Resources.Jobs
import Mettapedia.Machines.Resources.Certificates
import Mettapedia.Machines.Kernel.DelegationPolicy

/-!
# A product interpretation for memory and persistent jobs

This uses the existing separation-algebra product and exclusive-cell instances.
The authoritative ledger gives each live job one holder. Issued capability
handles are persistent values with a separate current-authorization predicate.
Memory writes require whole permissions; neither ledger validity nor a cached
authority observation supplies that permission.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Resources

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

variable {V : Type}

abbrev JobResource := JobId → Excl Nat
abbrev Resource (V : Type) := MemoryResource V × JobResource

structure World (V : Type) where
  memory : Memory V
  authority : Authority
  jobs : Jobs.Ledger
  heads : Nat → Option AllocationId

def JobValid (ledger : Jobs.Ledger) (r : JobResource) : Prop :=
  FiniteSupport r ∧ ∀ id actor, r id = .own actor → Jobs.Holds ledger actor id

def Interpreted (world : World V) (resource : Resource V) : Prop :=
  MemoryValid world.memory resource.1 ∧ Jobs.Valid world.jobs ∧ JobValid world.jobs resource.2

theorem permit_not_duplicable (a b : Nat) (id : JobId) (left right : JobResource)
    (ownsLeft : left id = .own a) (ownsRight : right id = .own b) : ¬ left ## right := by
  intro separate
  exact Excl.not_separate_own a b (by simpa [ownsLeft, ownsRight] using separate id)

/-- State and resources both change in this rule; unrelated resources retain
their interpretation. Compatibility alone is not a program transition. -/
theorem interpreted_write_preserves_frame {world : World V} {r frame : Resource V}
    (valid : Interpreted world r) (validFrame : Interpreted world frame)
    (separate : r ## frame) (key : AllocationId) (old value : Cell V)
    (whole : r.1 key = Mettapedia.Machines.CMemory.CellPermission.whole (some old)) :
    let after := { world with memory := writeCell world.memory key value }
    let changed := (replacePermission r.1 key value, r.2)
    Interpreted after changed ∧ Interpreted after frame ∧ changed ## frame := by
  obtain ⟨memory, framed, compatible⟩ := write_preserves_frame valid.1 validFrame.1 separate.1 key old value whole
  exact ⟨⟨memory, valid.2⟩, ⟨framed, validFrame.2⟩, ⟨compatible, separate.2⟩⟩

/-- Revocation does not destroy memory or job ownership held by any frame.
Authorization for the next effect is checked in the new authoritative state. -/
theorem interpreted_revoke_preserves_frame (world : World V) (resource : Resource V)
    (target : Nat) (valid : Interpreted world resource) :
    Interpreted { world with authority := revoke world.authority target } resource := valid

theorem transfer_updates_only_named_job {before after : Jobs.Ledger} (actor target : Nat)
    (id other : JobId) (different : other ≠ id)
    (accepted : Jobs.transfer before actor target id = some after) :
    after.entries other = before.entries other := by
  obtain ⟨_, _, _, _, _, rfl⟩ := Jobs.modify_found accepted
  simp [different]

theorem transfer_preserves_job_frame {before after : Jobs.Ledger} (actor target : Nat)
    (id : JobId) (frame : JobResource) (valid : JobValid before frame)
    (unowned : frame id = 0) (accepted : Jobs.transfer before actor target id = some after) :
    JobValid after frame := by
  refine ⟨valid.1, ?_⟩
  intro other holder owned
  have different : other ≠ id := by
    intro same
    subst other
    rw [unowned] at owned
    cases owned
  obtain ⟨entry, found, holds⟩ := valid.2 other holder owned
  exact ⟨entry, (transfer_updates_only_named_job actor target id other different accepted).trans found, holds⟩

/-- The action checks current authority at its linearization boundary. A
historical handle or cached authorization answer cannot bypass this guard. -/
def authorizeAndSpend (world : World V) (actor : Nat) (handle : Handle)
    (id : JobId) : Option (World V) :=
  if MayAct world.authority actor handle then
    (Jobs.spendEffect world.jobs actor id).map fun next => { world with jobs := next }
  else none

theorem effect_requires_current_authority {world after : World V} (actor : Nat)
    (handle : Handle) (id : JobId)
    (accepted : authorizeAndSpend world actor handle id = some after) :
    MayAct world.authority actor handle := by
  classical
  unfold authorizeAndSpend at accepted
  split at accepted
  · assumption
  · cases accepted

theorem revoked_cannot_spend (world : World V) (actor : Nat) (handle : Handle) (id : JobId)
    (current : world.authority.generations handle.resource = handle.generation) :
    authorizeAndSpend { world with authority := revoke world.authority handle.resource } actor handle id = none := by
  classical
  simp [authorizeAndSpend, revoke_blocks_old_action world.authority actor handle current]

def CurrentView (world : World V) (publication : Nat) (allocation : AllocationId)
    (cell : Cell V) : Prop :=
  world.heads publication = some allocation ∧ world.memory allocation = some cell

def publishHead (world : World V) (publication : Nat) (allocation : AllocationId) : World V :=
  { world with heads := Function.update world.heads publication (some allocation) }

theorem publication_preserves_retained_resources (world : World V) (resource : Resource V)
    (publication : Nat) (allocation : AllocationId) (valid : Interpreted world resource) :
    Interpreted (publishHead world publication allocation) resource := valid

theorem different_publication_ends_current_view (world : World V) (publication : Nat)
    (old next : AllocationId) (cell : Cell V) (different : old ≠ next) :
    ¬ CurrentView (publishHead world publication next) publication old cell := by
  rintro ⟨head, _⟩
  have same : next = old := by simpa [publishHead] using head
  exact different same.symm

/-- Capability policy runs inherit the existing confinement theorem. Job
linearity does not turn freely copyable use capabilities into linear values. -/
theorem policy_run_confined {S O : Type} [DecidableEq S] [DecidableEq O]
    (rule : Mettapedia.Machines.Kernel.Delegation.Policy.Rule S O)
    (state : Mettapedia.Machines.Kernel.Delegation.State S O)
    (operations : List (Mettapedia.Machines.Kernel.Delegation.Op S O))
    {actor : S} {target : Mettapedia.Machines.Kernel.Delegation.Target S O} {grant : Bool}
    (held : Mettapedia.Machines.Kernel.Delegation.Holds
      (Mettapedia.Machines.Kernel.Delegation.Policy.run rule state operations) actor target grant) :
    Mettapedia.Machines.Kernel.Delegation.CanHold state actor target grant :=
  Mettapedia.Machines.Kernel.Delegation.Policy.confined rule state operations held

#print axioms interpreted_write_preserves_frame
#print axioms transfer_preserves_job_frame
#print axioms permit_not_duplicable

end Mettapedia.Machines.Resources

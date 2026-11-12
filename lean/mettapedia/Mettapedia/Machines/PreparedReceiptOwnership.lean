import Mettapedia.Machines.PreparedStoreProtocol
import Mettapedia.Machines.Cursor.OwnedLifecycle

/-!
# Footprint-based ownership of prepared-publication receipts

Each live occurrence owns its payload's graph, independently of other
occurrences with equal or shared payloads. Publication removes only the taken
occurrence roots and inserts the made roots. Requested receipt roots are
exported before temporary owners are cancelled. The existing collector
preserves their complete graphs, including sharing and cycles.

The full live-store root set is an invariant, not a traversal required by the
update algorithm. Plain single additions/removals specialize to insert/erase.
This is a resource-bearing payload profile; root discovery, allocation failure
and native correspondence remain implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedReceiptOwnership

open PreparedStoreProtocol ResourceOwnership
open Cursor.OwnedLifecycle

variable {O Address External Value : Type}

inductive Owner (O External : Type) where
  | row (occurrence : O)
  | external (owner : External)
  deriving DecidableEq, Repr

def addresses : Option (Receipt O Address) → List Address
  | none => []
  | some receipt => receipt.taken.map Prod.snd ++ receipt.made.map Prod.snd

theorem record_addresses (label : O → Address) (plan : Plan O Address) (receipt : Receipt O Address)
    (recorded : record label plan = some receipt) :
    addresses (some receipt) = (plan.taken ++ plan.made).map label := by
  have contents := record_exact label plan receipt recorded
  simp [addresses, contents.2.2.2.1, contents.2.2.2.2.1, List.map_map, Function.comp_def]

variable [DecidableEq O] [DecidableEq External] [DecidableEq Address]

def rowRoots (label : O → Address) (rows : List O) : Roots (Owner O External) Address :=
  (rows.map fun occurrence => (Owner.row occurrence, label occurrence)).toFinset

@[simp] theorem mem_rowRoots (label : O → Address) (rows : List O) (occurrence : O) (address : Address) :
    (Owner.row occurrence, address) ∈ rowRoots (External := External) label rows ↔
      occurrence ∈ rows ∧ label occurrence = address := by
  simp [rowRoots, Prod.mk.injEq]

@[simp] theorem external_not_rowRoots (label : O → Address) (rows : List O)
    (owner : External) (address : Address) :
    (Owner.external owner, address) ∉ rowRoots label rows := by
  simp [rowRoots, Prod.mk.injEq]

/-- Only the changed footprint participates in the root update. -/
def patch (label : O → Address) (roots : Roots (Owner O External) Address)
    (plan : Plan O Address) : Roots (Owner O External) Address :=
  (roots \ rowRoots label plan.taken) ∪ rowRoots label plan.made

def deadOwners (dead : Finset External) : Finset (Owner O External) :=
  dead.image Owner.external

/-- The finite-set footprint update realizes the full live-store invariant.
No caller need rebuild that invariant at runtime. -/
theorem patch_store_exact (label : O → Address) (world : World O) (plan : Plan O Address) :
    patch label (rowRoots (External := External) label world.rows) plan =
      rowRoots label (updatedRows world plan) := by
  ext pair
  rcases pair with ⟨owner, address⟩
  cases owner with
  | row occurrence =>
      simp only [patch, Finset.mem_union, Finset.mem_sdiff, mem_rowRoots, updated_membership]
      tauto
  | external owner => simp [patch]

theorem patch_single_append (label : O → Address) (roots : Roots (Owner O External) Address)
    (space : Nat) (occurrence : O) (ticket : Option Nat) :
    patch label roots ⟨space, .append [occurrence], [], ticket⟩ =
      insert (Owner.row occurrence, label occurrence) roots := by
  simp [patch, rowRoots, Plan.taken, Plan.made, Operation.made]

theorem patch_single_take (label : O → Address) (roots : Roots (Owner O External) Address)
    (space : Nat) (keys : List Address) (occurrence : O) (ticket : Option Nat) :
    patch label roots ⟨space, .erase keys, [occurrence], ticket⟩ =
      roots.erase (Owner.row occurrence, label occurrence) := by
  simp [patch, rowRoots, Plan.taken, Plan.made, Operation.made, Finset.sdiff_singleton_eq_erase]

/-- Root publication precedes the one collection in the existing operation.
The semantic world has already reached the primitive publication result. -/
noncomputable def finish (label : O → Address)
    (session : Session (Owner O External) Address Value (State O Address))
    (next : State O Address) (plan : Plan O Address)
    (receipt : Option (Receipt O Address)) (output : External) (dead : Finset External) :
    Session (Owner O External) Address Value (State O Address) :=
  commit { session with roots := patch label session.roots plan, world := next }
    (deadOwners dead) (.external output) (addresses receipt)

theorem finish_world (label : O → Address)
    (session : Session (Owner O External) Address Value (State O Address))
    (next : State O Address) (plan : Plan O Address)
    (receipt : Option (Receipt O Address)) (output : External) (dead : Finset External) :
    (finish label session next plan receipt output dead).world = next := rfl

theorem unrecorded_adds_no_receipt_roots (label : O → Address)
    (session : Session (Owner O External) Address Value (State O Address))
    (next : State O Address) (plan : Plan O Address) (output : External) (dead : Finset External) :
    (finish label session next plan none output dead).roots =
      cancel (patch label session.roots plan) (deadOwners dead) := by
  simp [finish, commit, commitRoots, Cursor.OwnedLifecycle.publish, addresses, answerRoots]

theorem finish_preserves_receipt_graph (label : O → Address)
    (session : Session (Owner O External) Address Value (State O Address))
    (next : State O Address) (plan : Plan O Address)
    (receipt : Option (Receipt O Address)) (output : External) (dead : Finset External)
    (outside : output ∉ dead) (address : Address)
    (live : Live session.heap (answerRoots (Owner.external (O := O) output) (addresses receipt)) address) :
    (finish label session next plan receipt output dead).heap.lookup address = session.heap.lookup address := by
  apply lookup_collect_of_live
  exact answer_graph_live_after_commit session.heap _ (deadOwners dead) (.external output)
    (addresses receipt) (by simpa [deadOwners] using outside) live

theorem patch_mono (label : O → Address) (first second : Roots (Owner O External) Address)
    (plan : Plan O Address) (included : first ⊆ second) : patch label first plan ⊆ patch label second plan := by
  exact Finset.union_subset_union (Finset.sdiff_subset_sdiff included (Finset.Subset.refl _))
    (Finset.Subset.refl _)

theorem finish_preserves_store_graph (label : O → Address)
    (session : Session (Owner O External) Address Value (State O Address))
    (next : State O Address) (plan : Plan O Address)
    (receipt : Option (Receipt O Address)) (output : External) (dead : Finset External)
    (outside : output ∉ dead)
    (rooted : rowRoots label session.world.world.rows ⊆ session.roots)
    (updated : next.world.rows = updatedRows session.world.world plan) (address : Address)
    (live : Live session.heap (rowRoots (External := External) label next.world.rows) address) :
    (finish label session next plan receipt output dead).heap.lookup address = session.heap.lookup address := by
  have included : rowRoots label next.world.rows ⊆ patch label session.roots plan := by
    rw [updated, ← patch_store_exact label session.world.world plan]
    exact patch_mono label _ _ plan rooted
  have retained : rowRoots label next.world.rows ⊆ cancel (patch label session.roots plan) (deadOwners dead) := by
    intro pair member
    apply (mem_cancel _ _ pair).mpr
    refine ⟨included member, ?_⟩
    rcases pair with ⟨owner, location⟩
    cases owner with
    | row occurrence => simp [deadOwners]
    | external owner => exact False.elim (external_not_rowRoots label _ owner location member)
  apply lookup_collect_of_live
  exact outer_graph_live_after_commit session.heap _ (deadOwners dead) (.external output)
    (addresses receipt) (by simpa [deadOwners] using outside) (live_mono session.heap retained live)

/-- Other outside owners keep their graphs across subsequent store updates. -/
theorem finish_preserves_external_graph (label : O → Address)
    (session : Session (Owner O External) Address Value (State O Address))
    (next : State O Address) (plan : Plan O Address)
    (receipt : Option (Receipt O Address)) (output owner : External) (dead : Finset External)
    (outside : output ∉ dead) (survives : owner ∉ dead) (roots : List Address)
    (rooted : answerRoots (.external owner) roots ⊆ session.roots)
    (address : Address) (live : Live session.heap (answerRoots (Owner.external (O := O) owner) roots) address) :
    (finish label session next plan receipt output dead).heap.lookup address = session.heap.lookup address := by
  have included : answerRoots (.external owner) roots ⊆ cancel (patch label session.roots plan) (deadOwners dead) := by
    intro pair member
    have identity := (mem_answerRoots (.external owner) pair.1 roots pair.2).mp member
    apply (mem_cancel _ _ pair).mpr
    constructor
    · apply Finset.mem_union_left
      apply Finset.mem_sdiff.mpr
      refine ⟨rooted member, ?_⟩
      rcases pair with ⟨tag, location⟩
      cases identity.1
      exact external_not_rowRoots label plan.taken owner location
    · rw [identity.1]
      simpa [deadOwners] using survives
  apply lookup_collect_of_live
  exact outer_graph_live_after_commit session.heap _ (deadOwners dead) (.external output)
    (addresses receipt) (by simpa [deadOwners] using outside) (live_mono session.heap included live)

def AllocatedInputs (label : O → Address) (heap : Heap Address Value) (state : State O Address) : Prop :=
  (∀ occurrence ∈ state.world.rows, label occurrence ∈ heap.allocated) ∧
  (∀ plan, state.slot = .pending plan → ∀ occurrence ∈ plan.made, label occurrence ∈ heap.allocated)

theorem committed_payloads_allocated (label : O → Address) (heap : Heap Address Value)
    (state : State O Address) (expected : Option Nat) (receipt : Option (Receipt O Address))
    (inputs : AllocatedInputs label heap state)
    (committed : (PreparedStoreProtocol.publish label expected state).1 = .committed receipt) :
    (∀ occurrence ∈ (PreparedStoreProtocol.publish label expected state).2.world.rows,
      label occurrence ∈ heap.allocated) ∧
    (∀ address ∈ addresses receipt, address ∈ heap.allocated) := by
  obtain ⟨plan, pending, ready, _, recorded, updated⟩ :=
    successful_publication_exact label expected state receipt committed
  constructor
  · intro occurrence member
    rw [updated] at member
    rcases (updated_membership state.world plan occurrence).mp member with old | made
    · exact inputs.1 occurrence old.1
    · exact inputs.2 plan pending occurrence made
  · intro address member
    cases receipt with
    | none => simp [addresses] at member
    | some receipt =>
        rw [record_addresses label plan receipt recorded] at member
        obtain ⟨occurrence, belongs, rfl⟩ := List.mem_map.mp member
        rcases List.mem_append.mp belongs with taken | made
        · exact inputs.1 occurrence (ready_taken_present label state.world plan ready occurrence taken)
        · exact inputs.2 plan pending occurrence made

/-- The real publication determines both the receipt addresses and the root
patch. No independently supplied receipt is treated as proof of a transition. -/
theorem committed_receipt_observation (label : O → Address)
    (session : Session (Owner O External) Address Value (State O Address))
    (expected : Option Nat) (receipt : Option (Receipt O Address))
    (plan : Plan O Address) (pending : session.world.slot = .pending plan)
    (output : External) (dead : Finset External) (outside : output ∉ dead)
    (inputs : AllocatedInputs label session.heap session.world)
    (committed : (PreparedStoreProtocol.publish label expected session.world).1 = .committed receipt) :
    observe (finish label session (PreparedStoreProtocol.publish label expected session.world).2
      plan receipt output dead).heap (addresses receipt) = observe session.heap (addresses receipt) ∧
    rowRoots label (PreparedStoreProtocol.publish label expected session.world).2.world.rows =
      patch label (rowRoots (External := External) label session.world.world.rows) plan := by
  have allocated := (committed_payloads_allocated label session.heap session.world expected receipt inputs committed).2
  obtain ⟨actual, found, _, _, _, updated⟩ :=
    successful_publication_exact label expected session.world receipt committed
  have same : actual = plan := Slot.pending.inj (found.symm.trans pending)
  subst actual
  constructor
  · exact commit_preserves_selected_observation
      { session with
        roots := patch label session.roots plan
        world := (PreparedStoreProtocol.publish label expected session.world).2 }
      (deadOwners dead) (.external output) (addresses receipt)
      (by simpa [deadOwners] using outside) allocated
  · rw [updated, patch_store_exact]

namespace Controls

def address (_ : Nat) : Fin 2 := 0
def world : World Nat := ⟨4, [0, 1], by decide⟩
def plan := build address world (.erase [0]) (some 7)
def state : State Nat (Fin 2) := ⟨world, .pending plan, 7⟩
def publication := PreparedStoreProtocol.publish address (some 7) state
def receipt : Option (Receipt Nat (Fin 2)) :=
  match publication.1 with
  | .committed value => value
  | _ => none
def roots : Roots (Owner Nat Nat) (Fin 2) := rowRoots address world.rows
def exported := commitRoots (patch address roots plan) (deadOwners {99})
  (.external 7) (addresses receipt)
def heap := MutableObservation.Controls.cyclicHeap
def session : Session (Owner Nat Nat) (Fin 2) Nat (State Nat (Fin 2)) :=
  ⟨heap, roots, state⟩

theorem actual_publication_recorded : publication.1 = .committed receipt := by decide

theorem allocated_inputs : AllocatedInputs address heap state := by
  constructor
  · intro occurrence _
    exact Finset.mem_univ _
  · intro pending _ occurrence _
    exact Finset.mem_univ _

theorem actual_receipt_survives_collection :
    observe (finish address session publication.2 plan receipt 7 {99}).heap (addresses receipt) =
      observe heap (addresses receipt) :=
  (committed_receipt_observation address session (some 7) receipt plan rfl 7 {99}
    (by decide) allocated_inputs actual_publication_recorded).1

theorem duplicate_entries_share_the_complete_graph :
    (addresses receipt).length = 2 ∧ exported.card = 1 ∧ (census heap exported).card = 2 := by decide

theorem a_readable_receipt_is_not_a_reservation :
    publication.2.world.rows = [] ∧ (census heap exported).card = 2 ∧
      ¬ Ready address publication.2.world plan := by decide

theorem missing_receipt_ownership_loses_the_graph :
    (addresses receipt).length = 2 ∧
      census heap (cancel (patch address roots plan) (deadOwners ({99} : Finset Nat))) = ∅ := by decide

theorem releasing_the_last_receipt_reclaims_the_cycle :
    census heap (ResourceOwnership.release exported (.external 7)) = ∅ := by decide

/-- This is the root update for a one-occurrence footprint. The key-removal
profile would select both aliases; no one-occurrence admission is asserted here. -/
def oneTaken : Plan Nat (Fin 2) := ⟨4, .erase [0], [0], none⟩

theorem removing_one_occurrence_keeps_a_shared_payload_alive :
    (patch address roots oneTaken).card = 1 ∧
      (census heap (patch address roots oneTaken)).card = 2 := by decide

end Controls

end Mettapedia.Machines.PreparedReceiptOwnership

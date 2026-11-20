import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BorrowedViews
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.OccurrenceKey
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.TakeValidity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.CursorProtocol

/-! # Lifetime controls retain generations, clones, failures and take readiness -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.LifetimeControls

open Mettapedia.Machines.ResourceOwnership
open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone
open Mettapedia.Machines.Cursor

def handle : Handle Nat Nat := ⟨7, 20, 3⟩
def original : Lease Nat Nat Nat := ⟨handle, 1, .shared⟩
def cloned : Lease Nat Nat Nat := ⟨handle, 2, .shared⟩
def shared : Frontier Nat Nat Nat := {original, cloned}

theorem clone_not_pointer_copy :
    Authorized shared 2 handle ∧ ¬ Authorized ({original} : Frontier Nat Nat Nat) 2 handle := by
  simp only [Authorized]
  decide

theorem close_original_keeps_clone :
    ¬ Authorized (shared.erase original) 1 handle ∧ Authorized (shared.erase original) 2 handle := by
  simp only [Authorized]
  decide

theorem close_last_removes_authority : ¬ Authorized ((shared.erase original).erase cloned) 2 handle := by
  simp only [Authorized]
  decide

theorem old_generation_not_revived :
    ¬ Authorized shared 2 ({handle with generation := 4}) := by
  simp only [Authorized]
  decide

def key : OccurrenceKey := ⟨7, 20, 3, 5⟩

theorem same_payload_different_slot_has_different_handle :
    key.encode ≠ ({key with slot := 6}).encode := by decide

theorem changed_view_has_different_handle :
    key.encode ≠ ({key with generation := 4}).encode := by decide

theorem full_origin_survives_authority_conversion :
    OccurrenceKey.ofHandle key.toHandle = key := OccurrenceKey.of_to_handle key

theorem capacity_refusal_does_not_truncate : OccurrenceKey.checked 2 key = none := by decide

def store : StampedSnapshots.Store Nat := StampedSnapshots.add StampedSnapshots.empty 10

theorem canonical_history_is_valid : TakeValidity.Valid store :=
  TakeValidity.add_valid _ TakeValidity.empty_valid 10

theorem borrowed_snapshot_is_not_take_readiness :
    ReadAdmissionProfiles.offers (StampedSnapshots.remove store 0) (StampedSnapshots.start store) = [(0, 10)] ∧
      ReadAdmissionProfiles.current (StampedSnapshots.remove store 0) 0 = none := by decide

def malformed : StampedSnapshots.Store Nat :=
  ⟨1, 1, fun id => if id = 0 then some ⟨10, 0, some 2⟩ else none⟩

theorem future_death_breaks_unqualified_consumption :
    ReadAdmissionProfiles.current (StampedSnapshots.remove malformed 0) 0 = some (0, 10) := by decide

theorem future_death_is_not_a_valid_history : ¬ TakeValidity.Valid malformed := by
  intro valid
  have impossible := (valid 0 ⟨10, 0, some 2⟩ (by decide)).2.2 2 rfl
  norm_num [malformed] at impossible

theorem invalidation_is_not_completed_emptiness :
    (CursorProtocol.Reply.failed .invalidated : CursorProtocol.Reply Nat) ≠ .observed .exhausted := by decide

theorem cancellation_is_not_completed_emptiness :
    (CursorProtocol.Reply.failed .interrupted : CursorProtocol.Reply Nat) ≠ .observed .exhausted := by decide

#print axioms close_original_keeps_clone
#print axioms borrowed_snapshot_is_not_take_readiness
#print axioms future_death_is_not_a_valid_history
#print axioms invalidation_is_not_completed_emptiness

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.LifetimeControls

import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BorrowedViews
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.CursorProtocol

/-!
# Lifetime and interruption checks feed the actual cursor provider

Authority, generation, work permission and allocation availability are
different input facts. Their failures are retained replies, not empty
searches. The permission frontier is the existing lease model; no new
capability discipline is introduced. This profile checks lifetime before
spending work or requesting allocation, without choosing a dialect default.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.Boundary

open Mettapedia.Machines.ResourceOwnership
open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone
open Mettapedia.Machines.Cursor

variable {ProviderID Resource Holder Value : Type}
  [DecidableEq ProviderID] [DecidableEq Resource] [DecidableEq Holder]

def granted (current : RequestBorrow.Stamp ProviderID) (frontier : Frontier ProviderID Resource Holder)
    (holder : Holder) (handle : Handle ProviderID Resource) : Bool :=
  authorizedB frontier holder handle && decide (BorrowedViews.stamp handle = current)

theorem granted_iff (current : RequestBorrow.Stamp ProviderID) (frontier : Frontier ProviderID Resource Holder)
    (holder : Holder) (handle : Handle ProviderID Resource) :
    granted current frontier holder handle = true ↔
      Authorized frontier holder handle ∧ BorrowedViews.stamp handle = current := by
  simp only [granted, Bool.and_eq_true, decide_eq_true_eq, Authorized]

def request (current : RequestBorrow.Stamp ProviderID) (frontier : Frontier ProviderID Resource Holder)
    (holder : Holder) (handle : Handle ProviderID Resource) (reader : Nat)
    (paid allocated : Bool) : CursorProtocol.Request Value :=
  ⟨.read reader, if granted current frontier holder handle then
      if paid then if allocated then none else some .noMemory else some .interrupted
    else some .invalidated⟩

def perform (machine : CursorProtocol.Native Value) (operation : CursorProtocol.Request Value) :
    Σ _ : CursorProtocol.Reply Value, CursorProtocol.Native Value :=
  (CursorProtocol.concrete Value).step (base := ()) (index := ()) machine operation

theorem failure_not_hidden (current : RequestBorrow.Stamp ProviderID) (frontier : Frontier ProviderID Resource Holder)
    (holder : Holder) (handle : Handle ProviderID Resource) (reader : Nat) (paid allocated : Bool)
    (denied : granted current frontier holder handle = false) :
    (request (Value := Value) current frontier holder handle reader paid allocated).failure = some .invalidated := by
  simp only [request, denied, Bool.false_eq_true, if_false]

theorem denied_preserves_cursor (current : RequestBorrow.Stamp ProviderID) (frontier : Frontier ProviderID Resource Holder)
    (holder : Holder) (handle : Handle ProviderID Resource) (reader : Nat) (paid allocated : Bool)
    (denied : granted current frontier holder handle = false) (machine : CursorProtocol.Native Value) :
    (perform machine
      (request current frontier holder handle reader paid allocated)).1 = .failed .invalidated ∧
      (perform machine
        (request current frontier holder handle reader paid allocated)).2 = machine := by
  simp [perform, CursorProtocol.concrete, failure_not_hidden current frontier holder handle reader paid allocated denied]

theorem current_read_is_the_real_step (current : RequestBorrow.Stamp ProviderID)
    (frontier : Frontier ProviderID Resource Holder) (holder : Holder) (handle : Handle ProviderID Resource)
    (reader : Nat) (authorized : Authorized frontier holder handle)
    (live : BorrowedViews.stamp handle = current) (machine : CursorProtocol.Native Value) :
    (perform machine
      (request current frontier holder handle reader true true)).1 =
        .observed (StampedSnapshots.apply machine.val (.read reader)).2 := by
  have permitted := (granted_iff current frontier holder handle).mpr ⟨authorized, live⟩
  simp [perform, CursorProtocol.concrete, request, permitted]

theorem cancelled_preserves_cursor (current : RequestBorrow.Stamp ProviderID)
    (frontier : Frontier ProviderID Resource Holder) (holder : Holder) (handle : Handle ProviderID Resource)
    (reader : Nat) (allowed : granted current frontier holder handle = true) (allocated : Bool)
    (machine : CursorProtocol.Native Value) :
    (perform machine
      (request current frontier holder handle reader false allocated)).1 = .failed .interrupted ∧
      (perform machine
        (request current frontier holder handle reader false allocated)).2 = machine := by
  simp [perform, CursorProtocol.concrete, request, allowed]

#print axioms granted_iff
#print axioms denied_preserves_cursor
#print axioms current_read_is_the_real_step
#print axioms cancelled_preserves_cursor

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.Boundary

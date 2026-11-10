import Mettapedia.Machines.PreparedStoreProtocol

/-!
# Executable counterexamples for prepared-store publication defects

These independent models isolate four failure patterns: copying through stale
dense-selection metadata, repeated physical deletion, retagging before a busy
check, and association by kind/space alone. They are not translations of C.
Each negative control is paired with a result of the corrected protocol.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedStoreProtocol.Controls

def label (occurrence : Nat) : Nat :=
  if occurrence = 0 then 10 else if occurrence = 1 then 20 else if occurrence = 2 then 10 else 30

def denseWorld : World Nat := ⟨7, [0, 1], by decide⟩
def mixedWorld : World Nat := ⟨7, [0, 1, 2], by decide⟩
def start (world : World Nat) : State Nat Nat := ⟨world, .empty, 0⟩

def takeA := (prepare label (.erase [10]) true true (start denseWorld)).2
def planA : Plan Nat Nat := build label denseWorld (.erase [10]) (some 1)
def receiptA : Receipt Nat Nat := ⟨7, 1, .erase, [(0, 10)], []⟩

theorem first_preparation_ready : takeA.slot = .pending planA ∧ Ready label denseWorld planA := by
  decide +kernel

theorem receipt_records_the_actual_take :
    (publish label (some 1) takeA).1 = .committed (some receiptA) ∧
      (publish label (some 1) takeA).2.world.rows = [1] ∧ receiptA.length = 1 := by
  decide +kernel

/-! ## F1: advertised slots that were never recorded -/

structure RawReceipt where
  slots : List (Option Nat)
  advertised : Nat
  deriving DecidableEq, Repr

def RawReceipt.initialized (receipt : RawReceipt) : Bool :=
  decide (receipt.advertised ≤ receipt.slots.length) &&
    (receipt.slots.take receipt.advertised).all Option.isSome

def copyThroughFlags (installed : List Bool) (selected : List Nat) : List (Option Nat) :=
  selected.zipIdx.map fun pair => if installed[pair.2]?.getD false then some pair.1 else none

/-- The producer computed new selection flags but the recorder still consults
the old effect's flags. Publication then overwrites the advertised length. -/
def staleFlagReceipt (oldFlags : List Bool) (selected : List Nat) : RawReceipt :=
  ⟨copyThroughFlags oldFlags selected, selected.length⟩

theorem stale_dense_metadata_advertises_unwritten_slots :
    copyThroughFlags [] [0, 1] = [none, none] ∧
      (staleFlagReceipt [] [0, 1]).advertised = 2 ∧
      (staleFlagReceipt [] [0, 1]).initialized = false := by
  decide

def encodedReceipt (receipt : Receipt Nat Nat) : RawReceipt :=
  ⟨(receipt.taken ++ receipt.made).map (fun pair => some pair.1), receipt.length⟩

/-- A count derived from completed records cannot advertise an unwritten slot. -/
theorem completed_records_are_initialized (receipt : Receipt Nat Nat) :
    (encodedReceipt receipt).initialized = true := by
  have complete (rows : List (Nat × Nat)) :
      (RawReceipt.mk (rows.map (fun pair => some pair.1)) rows.length).initialized = true := by
    simp [RawReceipt.initialized, ← List.map_take]
  simpa only [encodedReceipt, Receipt.length, List.length_append] using
    complete (receipt.taken ++ receipt.made)

def takeTwo := (prepare label (.erase [10, 20]) true true (start denseWorld)).2
def receiptTwo : Receipt Nat Nat := ⟨7, 1, .erase, [(0, 10), (1, 20)], []⟩

theorem corrected_dense_batch_records_both :
    (publish label (some 1) takeTwo).1 = .committed (some receiptTwo) ∧
      receiptTwo.length = 2 ∧ (encodedReceipt receiptTwo).initialized = true ∧
      (publish label (some 1) takeTwo).2.world.rows = [] := by
  decide +kernel

/-! ## F2: repeated requests are not repeated physical writes -/

def sequentialPhysicalTakes : List Nat → List Nat → Bool × List Nat
  | rows, [] => (true, rows)
  | rows, occurrence :: rest =>
      if occurrence ∈ rows then sequentialPhysicalTakes (rows.erase occurrence) rest
      else (false, rows)

theorem repeated_physical_take_fails_after_a_write :
    sequentialPhysicalTakes [0, 1] [0, 0] = (false, [1]) := by decide

def takeRepeated := (prepare label (.erase [10, 10]) true true (start denseWorld)).2

theorem repeated_keys_publish_once :
    (publish label (some 1) takeRepeated).1 = .committed (some receiptA) ∧
      (publish label (some 1) takeRepeated).2.world.rows = [1] := by decide +kernel

def takeCopies := (prepare label (.erase [10, 10]) true true (start mixedWorld)).2
def receiptCopies : Receipt Nat Nat := ⟨7, 1, .erase, [(0, 10), (2, 10)], []⟩

/-- Normalizing requests must not collapse two actual equal-valued rows. -/
theorem equal_payload_copies_remain_two_takes :
    (publish label (some 1) takeCopies).1 = .committed (some receiptCopies) ∧
      receiptCopies.length = 2 ∧ (publish label (some 1) takeCopies).2.world.rows = [1] := by
  decide +kernel

/-! ## F3: writing a tag before checking the slot -/

def retagThenReject (operation : Operation Nat Nat) (state : State Nat Nat) : Preparation × State Nat Nat :=
  match state.slot with
  | .pending plan => (.busy, { state with slot := .pending { plan with operation := operation } })
  | _ => prepare label operation false true state

def pendingAddition := (prepare label (.append [2]) false true (start denseWorld)).2

theorem rejected_retag_changes_pending_operation :
    (retagThenReject (.erase [20]) pendingAddition).1 = .busy ∧
      (retagThenReject (.erase [20]) pendingAddition).2.slot ≠ pendingAddition.slot := by
  decide +kernel

theorem corrected_busy_rejection_keeps_pending_operation :
    (prepare label (.erase [20]) false true pendingAddition).1 = .busy ∧
      (prepare label (.erase [20]) false true pendingAddition).2.slot = pendingAddition.slot ∧
      (publish label none pendingAddition).2.world.rows = [0, 1, 2] := by
  decide +kernel

/-! ## F4: operation kind and space do not identify a preparation -/

def secondStart : State Nat Nat := { takeA with slot := .empty }
def takeB := (prepare label (.erase [20]) true true secondStart).2
def planB : Plan Nat Nat := build label denseWorld (.erase [20]) (some 2)
def receiptB : Receipt Nat Nat := ⟨7, 2, .erase, [(1, 20)], []⟩

def acceptsOnlyKindAndSpace (plan : Plan Nat Nat) (receipt : Receipt Nat Nat) : Bool :=
  decide (plan.space = receipt.space ∧ plan.operation.kind = receipt.kind)

theorem same_kind_space_accepts_the_wrong_record :
    takeB.slot = .pending planB ∧ record label planB = some receiptB ∧
      acceptsOnlyKindAndSpace planA receiptB = true ∧
      receiptB.taken ≠ planA.taken.map (fun occurrence => (occurrence, label occurrence)) := by
  decide +kernel

theorem corrected_association_refuses_swap :
    (publish label (some receiptB.ticket) takeA).1 = .refused .receiptMismatch ∧
      (publish label (some receiptB.ticket) takeA).2.world.rows = denseWorld.rows ∧
      (publish label (some receiptB.ticket) takeA).2.slot = takeA.slot := by
  decide +kernel

/-! ## Ordinary paths and one-shot publication -/

theorem no_receipt_no_ticket_or_record :
    pendingAddition.nextTicket = 0 ∧
      (publish label none pendingAddition).1 = .committed none ∧
      (publish label none pendingAddition).2.nextTicket = 0 := by decide +kernel

theorem replay_cannot_remove_a_second_row :
    let first := publish label (some 1) takeA
    (publish label (some 1) first.2).1 = .refused .notPrepared ∧
      (publish label (some 1) first.2).2.world.rows = [1] := by decide +kernel

theorem capacity_refusal_has_no_ticket_or_write :
    let rejected := prepare label (.append [2]) true false (start denseWorld)
    rejected.1 = .allocationFailed ∧ rejected.2.world.rows = [0, 1] ∧
      rejected.2.nextTicket = 0 ∧ rejected.2.slot = .empty := by decide +kernel

end Mettapedia.Machines.PreparedStoreProtocol.Controls

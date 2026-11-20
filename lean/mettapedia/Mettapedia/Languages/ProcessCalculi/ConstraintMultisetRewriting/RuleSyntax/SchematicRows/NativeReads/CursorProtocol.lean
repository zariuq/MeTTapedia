import Mettapedia.Machines.Cursor.StampedSnapshots
import Mettapedia.Machines.Cursor.Protocol

/-!
# A fallible native reader realizes the existing captured-view protocol

The concrete state is the timestamp/ceiling/position reader machine, not a
copied remainder. The independent reference retains its captured lists.
Every write, clone, rewind and close is the existing event transition.
Explicit preflight failures leave the exact state unchanged and cannot become
exhaustion. The representation map composes with arbitrary adaptive clients.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.CursorProtocol

open Mettapedia.TypeTheory
open Mettapedia.Machines.Cursor

variable (Value : Type)

inductive Failure where
  | invalidated
  | interrupted
  | noMemory
  deriving DecidableEq, Repr

structure Request where
  event : StampedSnapshots.Event Value
  failure : Option Failure

inductive Reply where
  | observed (reply : StampedSnapshots.Reply Value)
  | failed (reason : Failure)
  deriving DecidableEq, Repr

def protocol : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Request Value
  Position _ := Reply Value
  next _ _ := ()

abbrev Native := {machine : StampedSnapshots.Machine Value // StampedSnapshots.ValidReaders machine}

def decode (machine : Native Value) : StampedSnapshots.Reference Value :=
  ⟨machine.val.store, StampedSnapshots.captureAll machine.val⟩

def concrete : Provider (protocol Value) where
  State _ _ := Native Value
  step machine request :=
    match request.failure with
    | some reason => ⟨.failed reason, machine⟩
    | none =>
        let result := StampedSnapshots.apply machine.val request.event
        ⟨.observed result.2, ⟨result.1, StampedSnapshots.valid_apply machine.val machine.property request.event⟩⟩

def reference : Provider (protocol Value) where
  State _ _ := StampedSnapshots.Reference Value
  step machine request :=
    match request.failure with
    | some reason => ⟨.failed reason, machine⟩
    | none =>
        let result := StampedSnapshots.referenceEvent machine request.event
        ⟨.observed result.2, result.1⟩

theorem decode_related (machine : Native Value) : StampedSnapshots.Related machine.val (decode Value machine) :=
  ⟨rfl, rfl, machine.property⟩

def refinement : Hom (concrete Value) (reference Value) where
  map := decode Value
  step machine request := by
    cases failed : request.failure with
    | some reason => simp only [concrete, reference, failed]
    | none =>
        simp only [concrete, reference, failed]
        obtain ⟨related, reply⟩ := StampedSnapshots.event_related machine.val (decode Value machine)
          (decode_related Value machine) request.event
        have state : decode Value
            ⟨(StampedSnapshots.apply machine.val request.event).1,
              StampedSnapshots.valid_apply machine.val machine.property request.event⟩ =
            (StampedSnapshots.referenceEvent (decode Value machine) request.event).1 := by
          exact congrArg₂ StampedSnapshots.Reference.mk related.1 related.2.1
        change (⟨.observed (StampedSnapshots.apply machine.val request.event).2,
          decode Value ⟨(StampedSnapshots.apply machine.val request.event).1,
            StampedSnapshots.valid_apply machine.val machine.property request.event⟩⟩ : Σ _ : Reply Value, StampedSnapshots.Reference Value) = _
        rw [reply, state]
        rfl

variable {Value}

theorem adaptive_client_refines
    {Return : (base : Unit) → Unit → Type}
    (client : Client (P := protocol Value) (Return := Return))
    (sourceCharge : Charge (concrete Value)) (targetCharge : Charge (reference Value))
    (fuel : Nat) (packet : Packet (concrete Value) client ()) :
    (refinement Value).outcome client
        (advance (concrete Value) client sourceCharge fuel packet).2 =
      (advance (reference Value) client targetCharge fuel
        ((refinement Value).packet client packet)).2 :=
  (refinement Value).advance client sourceCharge targetCharge fuel packet

theorem failure_is_not_exhaustion (reason : Failure) :
    (Reply.failed reason : Reply Value) ≠ .observed .exhausted := by
  intro impossible
  cases impossible

theorem exact_request_account
    {Return : (base : Unit) → Unit → Type}
    (client : Client (P := protocol Value) (Return := Return))
    (fuel : Nat) (packet : Packet (concrete Value) client ()) :
    ((advance (concrete Value) client (fun _ _ => 1) fuel packet).1,
        (refinement Value).outcome client
          (advance (concrete Value) client (fun _ _ => 1) fuel packet).2) =
      advance (reference Value) client (fun _ _ => 1) fuel ((refinement Value).packet client packet) :=
  (refinement Value).advance_account client _ _ (by intros; rfl) fuel packet

#print axioms refinement
#print axioms adaptive_client_refines
#print axioms failure_is_not_exhaustion
#print axioms exact_request_account

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.CursorProtocol

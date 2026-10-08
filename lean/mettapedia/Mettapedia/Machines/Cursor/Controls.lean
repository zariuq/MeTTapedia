import Mettapedia.Machines.Cursor.Sequence
import Mettapedia.Machines.Cursor.Composition

/-!
# Executable controls for the cursor algebra

Independent implementations are compared on partial delivery, duplicates,
early stopping, live representation transfer, and a nonterminating client.
Negative controls expose replay and speculative work. An indexed protocol
also makes a pull after terminal exhaustion unrepresentable.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open CategoryTheory
open Sequence

abbrev Answers := fun (_ : Unit) (_ : Unit) => List (Option Nat)

def twoPulls : (protocol Nat).Free Answers () () :=
  Free.node (protocol Nat) () fun first =>
    Free.node (protocol Nat) () fun second =>
      Free.pure (protocol Nat) [first, second]

def onePull : (protocol Nat).Free Answers () () :=
  Free.node (protocol Nat) () fun first => Free.pure (protocol Nat) [first]

def answerClient : Client (P := protocol Nat) (Return := Answers) :=
  CoalgebraicPlans.retainedPlanRealizer

example : advance (tails Nat) answerClient (requested Nat) 3
    ⟨(), twoPulls, [7, 7, 9]⟩ =
    (2, .done ⟨(), [some 7, some 7], [9]⟩) := rfl

example : (sliceHom Nat).outcome answerClient
    (advance (slices Nat) answerClient (fun _ _ => 1) 3
      ⟨(), twoPulls, ⟨#[7, 7, 9], 0, 3⟩⟩).2 =
    .done ⟨(), [some 7, some 7], [9]⟩ := rfl

example : (sliceHom Nat).outcome answerClient
    (advance (slices Nat) answerClient (fun _ _ => 1) 3
      ⟨(), twoPulls, ⟨#[99, 7, 8, 9], 1, 2⟩⟩).2 =
    .done ⟨(), [some 7, some 8], []⟩ := rfl

example : resume (tails Nat) answerClient (requested Nat) 2
    (advance (tails Nat) answerClient (requested Nat) 1
      ⟨(), twoPulls, [7, 8, 9]⟩) =
    (2, .done ⟨(), [some 7, some 8], [9]⟩) := rfl

/-- Restarting the original provider after delivery changes the second answer. -/
def pendingSecond : (protocol Nat).Free Answers () () :=
  Free.node (protocol Nat) () fun second =>
    Free.pure (protocol Nat) [some 7, second]

example : (advance (tails Nat) answerClient (requested Nat) 2
    ⟨(), pendingSecond, [7, 8, 9]⟩).2 ≠
    (advance (tails Nat) answerClient (requested Nat) 2
      ⟨(), pendingSecond, [8, 9]⟩).2 := by
  intro equal
  have values := congrArg (fun outcome => match outcome with
    | .done result => result.2.1
    | .paused _ => []) equal
  change [some 7, some 7] = [some 7, some 8] at values
  norm_num at values

def representations : Bool → Provider (protocol Nat)
  | false => tails Nat
  | true => slices Nat

def representationHom (backend : Bool) : Hom (representations backend) (tails Nat) :=
  match backend with
  | false => Hom.id _
  | true => sliceHom Nat

def promote : Offer (familyProvider representations) := fun value _ =>
  match value with
  | ⟨false, items⟩ => some ⟨true, ⟨items.toArray, 0, items.length⟩⟩
  | ⟨true, _⟩ => none

example : choose promote (base := ()) (index := ())
    ⟨true, ⟨#[7, 8, 9], 1, 2⟩⟩ () = ⟨true, ⟨#[7, 8, 9], 1, 2⟩⟩ := rfl

def replayOffer : Offer (tails Nat) := fun _ _ => some [7, 8, 9]

example : ¬ SoundOffer (Hom.id (tails Nat)) replayOffer := by
  intro claimed
  have wrong := claimed (base := ()) (index := ()) [8, 9] [7, 8, 9] () rfl
  change [7, 8, 9] = [8, 9] at wrong
  norm_num at wrong

theorem promote_sound :
    SoundOffer (familyHom representations (tails Nat) representationHom) promote := by
  intro base index state next request offered
  rcases state with ⟨backend, state⟩
  cases backend with
  | false =>
      have equal : (⟨true, ⟨state.toArray, 0, state.length⟩⟩ :
          (familyProvider representations).State base index) = next := Option.some.inj offered
      rw [← equal]
      simp [familyHom, representationHom, sliceHom, Hom.id]
      change state.take state.length = state
      exact List.take_length
  | true => simp [promote] at offered

def switched := switchingProvider (familyProvider representations) promote

example : (switchingHom (familyHom representations (tails Nat) representationHom)
      promote promote_sound).outcome answerClient
    (advance switched answerClient (fun _ _ => 1) 2
      ⟨(), pendingSecond, ⟨false, [8, 9]⟩⟩).2 =
    .done ⟨(), [some 7, some 8], [9]⟩ := rfl

/-- Speculation is real work: one requested element can load three. -/
example : (advance (prefetched Nat 2) answerClient (loaded Nat 2) 2
    ⟨(), onePull, ⟨[], [7, 8, 9, 10], by decide⟩⟩).1 = 3 := rfl

example : (advance (tails Nat) answerClient (requested Nat) 2
    ⟨(), onePull, [7, 8, 9, 10]⟩).1 = 1 := rfl

example : (prefetchHom Nat 2).outcome answerClient
    (advance (prefetched Nat 2) answerClient (loaded Nat 2) 2
      ⟨(), onePull, ⟨[], [7, 8, 9, 10], by decide⟩⟩).2 =
    .done ⟨(), [some 7], [8, 9, 10]⟩ := rfl

/-- This client keeps requesting even after exhaustion. The scheduler must
retain it, never label its empty replies as client completion. -/
def forever : Client (P := protocol Nat) (Return := fun _ _ => Empty) where
  V _ _ := Nat
  str := fun _ _ => ↾(fun count => ⟨.inr (), fun _ => count + 1⟩)

theorem forever_pauses (budget count : Nat) :
    advance (tails Nat) forever (fun _ _ => 1) budget (base := ()) ⟨(), count, []⟩ =
      (budget, .paused ⟨(), count + budget, []⟩) := by
  induction budget generalizing count with
  | zero => simp [advance]
  | succ budget ih =>
      change (1 + (advance (tails Nat) forever (fun _ _ => 1) budget
          (base := ()) ⟨(), count + 1, []⟩).1,
        (advance (tails Nat) forever (fun _ _ => 1) budget
          (base := ()) ⟨(), count + 1, []⟩).2) = _
      dsimp only [forever, protocol] at ih ⊢
      rw [ih]
      simp [Nat.add_comm, Nat.add_left_comm]

inductive Mode where
  | active
  | closed

def terminalProtocol : IndexedPolynomial Unit (fun _ => Mode) where
  Shape _ mode := match mode with | .active => Unit | .closed => Empty
  Position {_ index} _ := match index with | .active => Option Nat | .closed => Empty
  next {_ index} _ reply := match index with
    | .active => match reply with | none => .closed | some _ => .active
    | .closed => reply.elim

def terminalProvider : Provider terminalProtocol where
  State _ mode := match mode with | .active => List Nat | .closed => Unit
  step {_ index} state request := match index with
    | .active => match state with
      | [] => ⟨none, ()⟩
      | first :: rest => ⟨some first, rest⟩
    | .closed => request.elim

example : IsEmpty (terminalProtocol.Shape () .closed) := by
  change IsEmpty Empty
  infer_instance

example : terminalProvider.step (base := ()) (index := .active) [] () =
    ⟨none, ()⟩ := rfl

end Mettapedia.Machines.Cursor.Controls

namespace Mettapedia.Machines.Cursor.PrimitiveProgram.Controls

open Mettapedia.GSLT.Logic.AbstractSeparationLogic

inductive Operation where
  | record (bit : Bool)
  | refuse

/-- Result family shared by the record/fault comparison controls. -/
def response : Operation → Type
  | .record _ => Unit
  | .refuse => Empty

/-- Complete record/fault transition, including the performed update on refusal. -/
def transition (history : List Bool) : (op : Operation) →
    List Bool × Except Unit (response op)
  | .record bit => (history ++ [bit], .ok ())
  | .refuse => (history ++ [false], .error ())

/-- Positive operation-count meter used by the record/fault controls. -/
def expense (_ : List Bool) : Operation → Nat
  | .record _ => 2
  | .refuse => 3

/-- A retained two-operation client for split/resume comparisons. -/
def twoRecords : Prog Operation response Nat :=
  .call (.record true) fun _ => .call (.record false) fun _ => .ret 7

private def oneRecord (bit : Bool) : Prog Operation response Nat :=
  .call (.record bit) fun _ => .ret 7

/-- An inspection cut retains the actual next operation and its performed
state change; it does not reconstruct a fresh program. -/
theorem first_cut_keeps_next_operation_and_history :
    let result := advance (provider transition) (client Operation response Nat Unit)
      (charge expense transition) 1 (base := PUnit.unit) ⟨PUnit.unit, .ok twoRecords, []⟩
    (result.1, readOutcome transition result.2) =
      (2, (.inr (.ok (.call (.record false) fun _ => .ret 7)), [true])) := rfl

/-- One additional inspection of a return leaf costs no primitive work. -/
theorem completion_keeps_history_and_actual_charge :
    let result := advance (provider transition) (client Operation response Nat Unit)
      (charge expense transition) 3 (base := PUnit.unit) ⟨PUnit.unit, .ok twoRecords, []⟩
    (result.1, readOutcome transition result.2) = (4, (.inl (.ok 7), [true, false])) := rfl

/-- Resuming the retained packet executes the suffix once, using the common
cursor's law rather than a separate scheduling model. -/
theorem split_does_not_replay_recording :
    resume (provider transition) (client Operation response Nat Unit)
      (charge expense transition) 2 (base := PUnit.unit)
      (advance (provider transition) (client Operation response Nat Unit)
        (charge expense transition) 1 (base := PUnit.unit) ⟨PUnit.unit, .ok twoRecords, []⟩) =
    advance (provider transition) (client Operation response Nat Unit)
      (charge expense transition) 3 (base := PUnit.unit) ⟨PUnit.unit, .ok twoRecords, []⟩ :=
  (advance_add (provider transition) (client Operation response Nat Unit)
    (charge expense transition) 1 2 (base := PUnit.unit) _).symm

/-- An empty success response type remains usable through an explicit fault
reply, with the provider's performed world change still retained. -/
theorem fault_keeps_performed_world_and_charge :
    let result := advance (provider transition) (client Operation response Nat Unit)
      (charge expense transition) 2
      ⟨PUnit.unit, .ok (.call .refuse Empty.elim), []⟩
    (result.1, readOutcome transition result.2) = (3, (.inl (.error ()), [false])) := rfl

/-- Equal answers with different histories are distinct outcomes. -/
theorem equal_answers_do_not_erase_history :
    readOutcome transition
        (advance (provider transition) (client Operation response Nat Unit)
          (charge expense transition) 2 ⟨PUnit.unit, .ok (oneRecord true), []⟩).2 ≠
      readOutcome transition
        (advance (provider transition) (client Operation response Nat Unit)
          (charge expense transition) 2 ⟨PUnit.unit, .ok (oneRecord false), []⟩).2 := by
  intro equal
  have sameHistory := congrArg Prod.snd equal
  change [true] = [false] at sameHistory
  cases sameHistory

/-- Reaching a return leaf with no remaining inspections is still suspended;
inspection exhaustion is not fabricated completion. -/
theorem a_paused_return_is_not_a_completed_answer :
    readOutcome transition
        (advance (provider transition) (client Operation response Nat Unit)
          (charge expense transition) 2 ⟨PUnit.unit, .ok twoRecords, []⟩).2 ≠
      (.inl (.ok 7), [true, false]) := by
  intro equal
  have sameStatus := congrArg Prod.fst equal
  change Sum.inr (Except.ok (Prog.ret 7)) = Sum.inl (Except.ok 7) at sameStatus
  cases sameStatus

/-- The independent action declares the whole history update, not just the
returned value. Refusal has no safe success execution. -/
private def action : (op : Operation) → Action (List Bool) (response op)
  | .record bit => ⟨fun _ => True, fun before _ after => after = before ++ [bit]⟩
  | .refuse => ⟨fun _ => False, fun _ value _ => Empty.elim value⟩

/-- The concrete provider discharges its local independent action contract. -/
theorem transition_realizes_action : ProviderSound action transition := by
  intro history operation safe
  cases operation with
  | record bit => exact ⟨(), history ++ [bit], rfl, rfl⟩
  | refuse => exact False.elim safe

/-- Deliberately faulty provider retaining replies while omitting record updates. -/
def omitRecords (history : List Bool) : (op : Operation) →
    List Bool × Except Unit (response op)
  | .record _ => (history, .ok ())
  | .refuse => (history ++ [false], .error ())

/-- Keeping an answer while omitting a performed update violates the local
realization law; whole-state preservation is a substantive obligation. -/
theorem lost_recording_is_not_a_realization : ¬ ProviderSound action omitRecords := by
  intro claimed
  obtain ⟨value, following, stepLaw, permitted⟩ :=
    claimed [] (.record true) trivial
  cases value
  have sameWorld := congrArg Prod.fst stepLaw
  change [] = following at sameWorld
  change following = [] ++ [true] at permitted
  rw [← sameWorld] at permitted
  cases permitted

/-- Both providers still print the same successful answer. -/
theorem lost_recording_preserves_the_plain_answer :
    (readOutcome transition
      (advance (provider transition) (client Operation response Nat Unit)
        (charge expense transition) 2 ⟨PUnit.unit, .ok (oneRecord true), []⟩).2).1 =
    (readOutcome omitRecords
      (advance (provider omitRecords) (client Operation response Nat Unit)
        (charge expense omitRecords) 2 ⟨PUnit.unit, .ok (oneRecord true), []⟩).2).1 := rfl

end Mettapedia.Machines.Cursor.PrimitiveProgram.Controls

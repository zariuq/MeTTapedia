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

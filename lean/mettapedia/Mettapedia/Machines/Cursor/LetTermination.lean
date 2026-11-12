import Mettapedia.Machines.StoreAndDemand.FirstAnswer

/-!
# Hoisting also has termination, fault and budget obligations

The existing resumable producer protocol distinguishes values, exhaustion,
raised faults and ongoing progress. An inner let is not requested when no
candidate reaches it. Evaluating an outer let before an empty candidate
source must still process its producer, including faults or divergence.

The examples count producer requests, not dialect fuel or elapsed time.
The producer state below is its internal progress state; there is no mutable
user store hidden behind a supposedly pure function.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetTermination

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open _root_.CategoryTheory
open Mettapedia.Machines.StoreAndDemand

abbrev Reply := FirstAnswer.Reply Nat String
abbrev Result := FirstAnswer.Result Nat String
abbrev P := FirstAnswer.protocol Nat String

def noCandidates : Client (P := P) (Return := fun _ _ => Result) where
  V _ _ := Unit
  str := fun _ _ => ↾(fun _ => ⟨.inl .exhausted, nofun⟩)

/-- Every outer choice enters an empty candidate body. The client continues
until the code exhausts, raises, or is interrupted; it does not stop at the
first discarded value. -/
def discardReply : Reply → Option Result
  | .progress | .answer _ => none
  | .exhausted => some .exhausted
  | .raised fault => some (.raised fault)
  | .interrupted => some .interrupted

def outerEmpty : Client (P := P) (Return := fun _ _ => Result) where
  V _ _ := Option Result
  str := fun _ _ => ↾(fun control => match control with
    | some result => ⟨.inl result, nofun⟩
    | none => ⟨.inr (), discardReply⟩)

def innerStart (step : Nat → Reply × Nat) (state : Nat) :
    Packet (FirstAnswer.provider step) noCandidates () := ⟨(), (), state⟩

def outerStart (step : Nat → Reply × Nat) (state : Nat) :
    Packet (FirstAnswer.provider step) outerEmpty () := ⟨(), none, state⟩

theorem unreached_code_is_not_polled (step : Nat → Reply × Nat) (state extra : Nat) :
    advance (FirstAnswer.provider step) noCandidates (fun _ _ => 1) (extra + 1)
        (innerStart step state) =
      (0, .done ⟨(), .exhausted, state⟩) := rfl

def NoAnswer (step : Nat → Reply × Nat) : Prop :=
  ∀ state value after, step state ≠ (.answer value, after)

def faulting (state : Nat) : Reply × Nat := (.raised "bad-value", state)

theorem faulting_has_at_most_one_answer : NoAnswer faulting := by
  intro state value after
  simp [faulting]

theorem hoisting_can_expose_an_unreached_fault :
    advance (FirstAnswer.provider faulting) outerEmpty (fun _ _ => 1) 2
        (outerStart faulting 0) = (1, .done ⟨(), .raised "bad-value", (0 : Nat)⟩) ∧
      advance (FirstAnswer.provider faulting) noCandidates (fun _ _ => 1) 1
        (innerStart faulting 0) = (0, .done ⟨(), .exhausted, (0 : Nat)⟩) := by constructor <;> rfl

def endless (state : Nat) : Reply × Nat := (.progress, state + 1)

theorem endless_has_at_most_one_answer : NoAnswer endless := by
  intro state value after
  simp [endless]

/-- Every finite prefix remains unfinished. Absence of multiple successful
answers is not totality or permission to run the code before it is reached. -/
theorem hoisted_endless_code_stays_pending (state budget : Nat) :
    advance (FirstAnswer.provider endless) outerEmpty (fun _ _ => 1) budget
      (outerStart endless state) =
        (budget, .paused (outerStart endless (state + budget))) := by
  induction budget generalizing state with
  | zero => simp [advance, outerStart]
  | succ budget ih =>
      change (1 + (advance (FirstAnswer.provider endless) outerEmpty (fun _ _ => 1) budget
        (outerStart endless (state + 1))).1,
        (advance (FirstAnswer.provider endless) outerEmpty (fun _ _ => 1) budget
          (outerStart endless (state + 1))).2) = _
      rw [ih]
      simp [Nat.add_comm, Nat.add_left_comm]

def singletonCode : Nat → Reply × Nat
  | 0 => (.answer 7, 1)
  | state + 1 => (.exhausted, state + 1)

theorem total_singleton_eventually_finishes :
    advance (FirstAnswer.provider singletonCode) outerEmpty (fun _ _ => 1) 3
      (outerStart singletonCode 0) = (2, .done ⟨(), .exhausted, (1 : Nat)⟩) := rfl

theorem even_total_singletons_can_add_work :
    (advance (FirstAnswer.provider singletonCode) outerEmpty (fun _ _ => 1) 3
      (outerStart singletonCode 0)).1 = 2 ∧
    (advance (FirstAnswer.provider singletonCode) noCandidates (fun _ _ => 1) 1
      (innerStart singletonCode 0)).1 = 0 := by decide

/-- Equal completed results do not imply identical finite work cutoffs. -/
theorem total_singleton_budget_boundary_differs :
    (advance (FirstAnswer.provider singletonCode) outerEmpty (fun _ _ => 1) 1
      (outerStart singletonCode 0)).2 =
        .paused ⟨(), none, (1 : Nat)⟩ ∧
    (advance (FirstAnswer.provider singletonCode) noCandidates (fun _ _ => 1) 1
      (innerStart singletonCode 0)).2 = .done ⟨(), .exhausted, (0 : Nat)⟩ := by constructor <;> rfl

end Mettapedia.Machines.Cursor.LetTermination

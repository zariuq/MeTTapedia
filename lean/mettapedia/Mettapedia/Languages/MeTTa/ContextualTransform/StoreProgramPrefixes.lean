import Mettapedia.Languages.MeTTa.ContextualTransform.ConcreteStorePrograms
import Mettapedia.Machines.Cursor.ReadOnlyQuery

/-!
# Resumable store interpretations and explicit accounts

The actual ordered-store backend and the independent source service are
providers of the existing cursor protocol. Their checked local square gives
the same bounded outcome, residual control, reached world and reply history.
Equal declared tariffs additionally give equal accumulated accounts.

The cursor's fuel counts protocol inspections; its tariff counts declared
operation charges. Neither is silently identified with native instruction
counts, memory usage, wall time, or CeTTa's current fuel instrumentation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.StoreProgramPrefixes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Machines
open ReadOnlyQuery (Program Reads)
open Cursor.ReadOnlyQuery (client)
open Cursor.ReadOnlyQuery
open AdaptiveStorePrograms
open PeTTaStoreSelection (atomFrames)

variable {O : Type} [DecidableEq O] (label : O → Atom)
  (knowledge : EquationStore Atom) (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge)
  (allocation : Allocation label)

def simulation : Cursor.Hom
    (Sampled.provider (target label knowledge consistent allocation))
    (Sampled.provider AdaptiveStorePrograms.source) where
  map saved := (decode label saved.1, saved.2)
  step saved command := by
    rcases saved with ⟨state, reads⟩
    have same := service_square label knowledge consistent allocation state command
    simp only [Sampled.provider]
    rw [same]

/-- Exact bounded correspondence retains paused control as well as completed
answers. No provider work runs when the inspection budget is zero. -/
theorem prefix_exact {Answer : Type} (price : Command → Nat) (fuel : Nat)
    (program : Program Command Reply Answer) (state : State O) (reads : Reads Command Reply) :
    let observed := Sampled.advance (target label knowledge consistent allocation)
      price fuel program state reads
    (observed.1, (simulation label knowledge consistent allocation).outcome client observed.2) =
      Sampled.advance AdaptiveStorePrograms.source price fuel program (decode label state) reads := by
  exact (simulation label knowledge consistent allocation).advance_account client
    (Sampled.charge _ price) (Sampled.charge _ price) (fun _ _ => rfl) fuel _

/-- A saved computation transfers its already paid account and resumes its
actual continuation. It does not restart the source program. -/
theorem resume_exact {Answer : Type} (price : Command → Nat) (fuel : Nat)
    (previous : Nat × Cursor.Outcome
      (Sampled.provider (target label knowledge consistent allocation))
      (client (Answer := Answer)) PUnit.unit) :
    let resumed := Sampled.resume (target label knowledge consistent allocation) price fuel previous
    (resumed.1, (simulation label knowledge consistent allocation).outcome client resumed.2) =
      Sampled.resume AdaptiveStorePrograms.source price fuel
        (previous.1, (simulation label knowledge consistent allocation).outcome client previous.2) := by
  exact (simulation label knowledge consistent allocation).resume_account client
    (Sampled.charge _ price) (Sampled.charge _ price) (fun _ _ => rfl) fuel previous

theorem decoded_world {Answer : Type}
    (outcome : Cursor.Outcome (Sampled.provider (target label knowledge consistent allocation))
      (client (Answer := Answer)) PUnit.unit) :
    (Sampled.savedState AdaptiveStorePrograms.source
      ((simulation label knowledge consistent allocation).outcome client outcome)).1 =
      decode label (Sampled.savedState (target label knowledge consistent allocation) outcome).1 := by
  cases outcome with
  | paused packet => rcases packet with ⟨⟨⟩, program, state, reads⟩; rfl
  | done finished => rcases finished with ⟨⟨⟩, answer, state, reads⟩; rfl

theorem recorded_history {Answer : Type}
    (outcome : Cursor.Outcome (Sampled.provider (target label knowledge consistent allocation))
      (client (Answer := Answer)) PUnit.unit) :
    Sampled.recorded AdaptiveStorePrograms.source
        ((simulation label knowledge consistent allocation).outcome client outcome) =
      Sampled.recorded (target label knowledge consistent allocation) outcome := by
  cases outcome with
  | paused packet => rcases packet with ⟨⟨⟩, program, state, reads⟩; rfl
  | done finished => rcases finished with ⟨⟨⟩, answer, state, reads⟩; rfl

theorem completion_status {Answer : Type}
    (outcome : Cursor.Outcome (Sampled.provider (target label knowledge consistent allocation))
      (client (Answer := Answer)) PUnit.unit) :
    Sampled.completed? AdaptiveStorePrograms.source
        ((simulation label knowledge consistent allocation).outcome client outcome) =
      Sampled.completed? (target label knowledge consistent allocation) outcome := by
  cases outcome with
  | paused packet => rcases packet with ⟨⟨⟩, program, state, reads⟩; rfl
  | done finished => rcases finished with ⟨⟨⟩, answer, state, reads⟩; rfl

theorem split_without_replay {Answer : Type} (price : Command → Nat) (first second : Nat)
    (program : Program Command Reply Answer) (state : State O) (reads : Reads Command Reply) :
    Sampled.advance (target label knowledge consistent allocation) price (first + second) program state reads =
      Sampled.resume (target label knowledge consistent allocation) price second
        (Sampled.advance (target label knowledge consistent allocation) price first program state reads) :=
  Sampled.advance_split _ _ _ _ _ _ _

/-- The account is exactly the sum of prices of the requests actually
executed, including repeats, even if the computation is still paused. -/
theorem prefix_account {Answer : Type} (price : Command → Nat) (fuel : Nat)
    (program : Program Command Reply Answer) (state : State O) :
    let observed := Sampled.advance (target label knowledge consistent allocation) price fuel program state []
    ((Sampled.recorded (target label knowledge consistent allocation) observed.2).map
      (fun entry => price entry.1)).sum = observed.1 := by
  simpa using Sampled.actual_read_invoice (target label knowledge consistent allocation)
    price fuel program state []

namespace Controls

open ConcreteStorePrograms

def backend := target ConcreteStorePrograms.label ConcreteStorePrograms.knowledge
  ConcreteStorePrograms.consistent ConcreteStorePrograms.allocation

def cut := Sampled.advance backend (fun _ => 1) 2 adaptive initial []
def finished := Sampled.resume backend (fun _ => 1) 3 cut

theorem cut_keeps_effect_and_pending_work :
    cut.1 = 2 ∧ Sampled.completed? backend cut.2 = none ∧
      decode ConcreteStorePrograms.label (Sampled.savedState backend cut.2).1 =
        [.symbol "a", .symbol "b", .symbol "a"] := by
  decide +kernel

theorem resume_finishes_without_repeating_append :
    finished.1 = 4 ∧
      (Sampled.completed? backend finished.2).map (fun result => result.answer) = some expected ∧
      decode ConcreteStorePrograms.label (Sampled.savedState backend finished.2).1 = [.symbol "b"] := by
  decide +kernel

/-- Charging four operations and observing their terminal result need not
consume the same number of scheduler inspections. -/
theorem charge_is_not_inspection_budget :
    (Sampled.advance backend (fun _ => 1) 4 adaptive initial []).1 = 4 ∧
      Sampled.completed? backend (Sampled.advance backend (fun _ => 1) 4 adaptive initial []).2 = none ∧
      (Sampled.completed? backend (Sampled.advance backend (fun _ => 1) 5 adaptive initial []).2).isSome = true := by
  decide +kernel

end Controls
end Mettapedia.Languages.MeTTa.ContextualTransform.StoreProgramPrefixes

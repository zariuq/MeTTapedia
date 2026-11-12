import Mettapedia.Machines.ImmediateStorePublication
import Mettapedia.Machines.Cursor.QueryCore

/-!
# Immediate publication through suspended adaptive clients

The provider map erases private receipt state while retaining the actual
reply-indexed continuation, reached world and ordered history. The existing
cursor account is used unchanged. Equal declared operation tariffs give equal
accounts; this result does not price the internal administrative work erased
by the immediate implementation or assert equal machine instructions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ImmediateStorePrefixes

open ImmediateStorePublication
open ReadOnlyQuery (Program Reads)
open Cursor.ReadOnlyQuery (client)
open Cursor.ReadOnlyQuery

variable {O Key : Type} [DecidableEq O] [DecidableEq Key]
  (label : O → Key) (recording : Bool)

def simulation : Cursor.Hom
    (Sampled.provider (staged label recording true))
    (Sampled.provider (immediate label)) where
  map saved := (saved.1.1, saved.2)
  step saved command := by
    rcases saved with ⟨ledger, reads⟩
    have same := staged_fuses label recording true ledger command (fun _ => rfl)
    simp only [Sampled.provider]
    rw [same]

theorem prefix_exact {Answer : Type} (price : Request O Key → Nat) (fuel : Nat)
    (program : Program (Request O Key) Reply Answer) (ledger : Ledger O)
    (reads : Reads (Request O Key) Reply) :
    let result := Sampled.advance (staged label recording true) price fuel program ledger reads
    (result.1, (simulation label recording).outcome client result.2) =
      Sampled.advance (immediate label) price fuel program ledger.1 reads :=
  (simulation label recording).advance_account client
    (Sampled.charge _ price) (Sampled.charge _ price) (fun _ _ => rfl) fuel _

theorem resume_exact {Answer : Type} (price : Request O Key → Nat) (fuel : Nat)
    (previous : Nat × Cursor.Outcome (Sampled.provider (staged label recording true))
      (client (Answer := Answer)) PUnit.unit) :
    let result := Sampled.resume (staged label recording true) price fuel previous
    (result.1, (simulation label recording).outcome client result.2) =
      Sampled.resume (immediate label) price fuel
        (previous.1, (simulation label recording).outcome client previous.2) :=
  (simulation label recording).resume_account client
    (Sampled.charge _ price) (Sampled.charge _ price) (fun _ _ => rfl) fuel previous

theorem retained_world {Answer : Type}
    (result : Cursor.Outcome (Sampled.provider (staged label recording true))
      (client (Answer := Answer)) PUnit.unit) :
    (Sampled.savedState (immediate label)
      ((simulation label recording).outcome client result)).1 =
      (Sampled.savedState (staged label recording true) result).1.1 := by
  cases result with
  | paused packet => rcases packet with ⟨⟨⟩, program, ledger, reads⟩; rfl
  | done finished => rcases finished with ⟨⟨⟩, answer, ledger, reads⟩; rfl

theorem completion_status {Answer : Type}
    (result : Cursor.Outcome (Sampled.provider (staged label recording true))
      (client (Answer := Answer)) PUnit.unit) :
    Sampled.completed? (immediate label) ((simulation label recording).outcome client result) =
      Sampled.completed? (staged label recording true) result := by
  cases result with
  | paused packet => rcases packet with ⟨⟨⟩, program, ledger, reads⟩; rfl
  | done finished => rcases finished with ⟨⟨⟩, answer, ledger, reads⟩; rfl

namespace Controls

open ImmediateStorePublication.Controls

def cut := Sampled.advance (staged id true true) (fun _ => 1) 1
  appendThenRefuse (emptyWorld, 0) []

def resumed := Sampled.resume (staged id true true) (fun _ => 1) 2 cut

theorem cut_retains_the_first_write :
    (Sampled.savedState (staged id true true) cut.2).1.1.rows = [3] ∧
      (Sampled.savedState (staged id true true) cut.2).1.2 = 1 ∧
      Sampled.completed? (staged id true true) cut.2 = none := by decide

theorem resume_does_not_repeat_it :
    (Sampled.savedState (staged id true true) resumed.2).1.1.rows = [3] ∧
      (Sampled.savedState (staged id true true) resumed.2).1.2 = 1 ∧
      (Sampled.completed? (staged id true true) resumed.2).map (·.answer) =
        some (.committed, .preparationFailed .invalidRequest) ∧
      resumed.1 = 2 := by decide

end Controls

end Mettapedia.Machines.ImmediateStorePrefixes

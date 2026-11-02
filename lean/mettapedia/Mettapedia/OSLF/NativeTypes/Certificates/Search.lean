import Mettapedia.OSLF.NativeTypes.Certificates.Coding

/-!
# Fair resumable search for finite native derivation certificates

Natural-number code enumeration is complete by the constructive certificate
codec. A fresh result is emitted only after the original judgment checker accepts it.
Running out of work retains a cursor and asserts no refutation. The discovery
bound depends on the complete encoded bit length, including all rule payloads.

`Scheduled` separates the loop from its candidate stream. Sound resumption
requires `State.Valid`; discovery uses an accepted stream position.
Concrete schedules supply their codec and coverage law.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.Search

universe u

variable {P : Presentation.{u}}

structure State (P : Presentation.{u}) where
  cursor : Nat
  found : Option (Tree P)

def initial : State P := ⟨0, none⟩

def State.Valid [DecidableEq P.Judgment] (judgment : P.Judgment) (state : State P) : Prop :=
  ∀ certificate, state.found = some certificate → certificate.check judgment = true

namespace Scheduled
variable [DecidableEq P.Judgment]

def step (schedule : Nat → Option (Tree P)) (judgment : P.Judgment) (state : State P) : State P :=
  match state.found with
  | some _ => state
  | none =>
      match schedule state.cursor with
      | none => ⟨state.cursor + 1, none⟩
      | some certificate =>
          if certificate.check judgment then ⟨state.cursor + 1, some certificate⟩
          else ⟨state.cursor + 1, none⟩

@[simp] def run (schedule : Nat → Option (Tree P)) (judgment : P.Judgment) : Nat → State P → State P
  | 0, state => state
  | budget + 1, state => run schedule judgment budget (step schedule judgment state)

variable (schedule : Nat → Option (Tree P))

theorem run_add (judgment : P.Judgment) (first second : Nat) (state : State P) :
    run schedule judgment (first + second) state = run schedule judgment second (run schedule judgment first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih =>
      simp only [Nat.succ_add, run, ih]

theorem run_settled (judgment : P.Judgment) (budget : Nat) (state : State P)
    (certificate : Tree P) (settled : state.found = some certificate) :
    run schedule judgment budget state = state := by
  induction budget with
  | zero => rfl
  | succ budget ih => simpa only [run, step, settled] using ih

theorem step_valid (judgment : P.Judgment) (state : State P)
    (valid : state.Valid judgment) : (step schedule judgment state).Valid judgment := by
  cases stored : state.found with
  | some old => simpa only [step, stored] using valid
  | none =>
      cases decoded : schedule state.cursor with
      | none => simp [step, stored, decoded, State.Valid]
      | some candidate =>
          by_cases accepted : candidate.check judgment = true <;>
            simp [step, stored, decoded, accepted, State.Valid]

theorem run_valid (judgment : P.Judgment) (budget : Nat) (state : State P)
    (valid : state.Valid judgment) : (run schedule judgment budget state).Valid judgment := by
  induction budget generalizing state with
  | zero => exact valid
  | succ budget ih => exact ih (step schedule judgment state) (step_valid schedule judgment state valid)

theorem step_cursor (judgment : P.Judgment) (state : State P)
    (unresolved : state.found = none) : (step schedule judgment state).cursor = state.cursor + 1 := by
  cases decoded : schedule state.cursor <;> simp [step, unresolved, decoded]
  split <;> rfl

theorem run_sound (judgment : P.Judgment) (budget : Nat) (certificate : Tree P)
    (found : (run schedule judgment budget initial).found = some certificate) :
    ∃ derivation : P.Derivation judgment, Tree.erase derivation = certificate := by
  apply (Tree.check_exact certificate judgment).mp
  exact run_valid schedule judgment budget initial (by intro certificate impossible; cases impossible)
    certificate found

/-- Discovery depends on an accepted candidate at a supplied stream position;
no completeness assumption is made about the rest of the schedule. -/
theorem step_at (judgment : P.Judgment) (state : State P) (certificate : Tree P)
    (unresolved : state.found = none) (present : schedule state.cursor = some certificate)
    (accepted : certificate.check judgment = true) :
    (step schedule judgment state).found = some certificate := by
  simp only [step, unresolved, present, accepted, if_true]

theorem complete_from_at (judgment : P.Judgment) (certificate : Tree P)
    (accepted : certificate.check judgment = true) (position : Nat)
    (present : schedule position = some certificate) (budget : Nat) (state : State P)
    (before : state.cursor ≤ position) (sufficient : position < state.cursor + budget) :
    ∃ result, (run schedule judgment budget state).found = some result := by
  induction budget generalizing state with
  | zero => omega
  | succ budget ih =>
      cases stored : state.found with
      | some result =>
          exact ⟨result, by rw [run_settled schedule judgment (budget + 1) state result stored]; exact stored⟩
      | none =>
          by_cases atCertificate : state.cursor = position
          · have found := step_at schedule judgment state certificate stored
              (by simpa only [atCertificate] using present) accepted
            exact ⟨certificate, by rw [run, run_settled schedule judgment budget _ certificate found]; exact found⟩
          · have nextCursor := step_cursor schedule judgment state stored
            exact ih (step schedule judgment state) (by omega) (by omega)

end Scheduled

variable [Encodable P.Rule] [DecidableEq P.Judgment]

def step (judgment : P.Judgment) (state : State P) : State P :=
  Scheduled.step (Encodable.decode (α := Tree P)) judgment state

def run (judgment : P.Judgment) : Nat → State P → State P :=
  Scheduled.run (Encodable.decode (α := Tree P)) judgment

def search (judgment : P.Judgment) (budget : Nat) : State P := run judgment budget initial

theorem run_add (judgment : P.Judgment) (first second : Nat) (state : State P) :
    run judgment (first + second) state = run judgment second (run judgment first state) :=
  Scheduled.run_add (Encodable.decode (α := Tree P)) judgment first second state

theorem run_settled (judgment : P.Judgment) (budget : Nat) (state : State P)
    (certificate : Tree P) (settled : state.found = some certificate) :
    run judgment budget state = state :=
  Scheduled.run_settled (Encodable.decode (α := Tree P)) judgment budget state certificate settled

theorem step_valid (judgment : P.Judgment) (state : State P)
    (valid : state.Valid judgment) : (step judgment state).Valid judgment :=
  Scheduled.step_valid (Encodable.decode (α := Tree P)) judgment state valid

theorem run_valid (judgment : P.Judgment) (budget : Nat) (state : State P)
    (valid : state.Valid judgment) : (run judgment budget state).Valid judgment :=
  Scheduled.run_valid (Encodable.decode (α := Tree P)) judgment budget state valid

theorem search_sound (judgment : P.Judgment) (budget : Nat) (certificate : Tree P)
    (found : (search judgment budget).found = some certificate) :
    ∃ derivation : P.Derivation judgment, Tree.erase derivation = certificate :=
  Scheduled.run_sound (Encodable.decode (α := Tree P)) judgment budget certificate found

theorem step_cursor (judgment : P.Judgment) (state : State P)
    (unresolved : state.found = none) : (step judgment state).cursor = state.cursor + 1 :=
  Scheduled.step_cursor (Encodable.decode (α := Tree P)) judgment state unresolved

theorem step_at_encoded (judgment : P.Judgment) (state : State P) (certificate : Tree P)
    (unresolved : state.found = none) (cursor : state.cursor = Encodable.encode certificate)
    (accepted : certificate.check judgment = true) :
    (step judgment state).found = some certificate :=
  Scheduled.step_at (Encodable.decode (α := Tree P)) judgment state certificate unresolved
    (by simpa only [cursor] using Tree.decode_encode certificate) accepted

theorem complete_from (judgment : P.Judgment) (certificate : Tree P)
    (accepted : certificate.check judgment = true) (budget : Nat) (state : State P)
    (before : state.cursor ≤ Encodable.encode certificate)
    (sufficient : Encodable.encode certificate < state.cursor + budget) :
    ∃ result, (run judgment budget state).found = some result :=
  Scheduled.complete_from_at (Encodable.decode (α := Tree P)) judgment certificate accepted _
    (Tree.decode_encode certificate) budget state before sufficient

theorem discover_within_wire_bound (judgment : P.Judgment) (certificate : Tree P)
    (accepted : certificate.check judgment = true) :
    ∃ result, (search judgment (Tree.discoveryBound (Tree.wireSize certificate))).found = some result :=
  complete_from judgment certificate accepted _ initial (Nat.zero_le _)
    (by simpa only [initial, Nat.zero_add] using Tree.code_lt_discoveryBound certificate)

theorem stable_conclusion (judgment : P.Judgment) (budget extra : Nat) (certificate : Tree P)
    (found : (search judgment budget).found = some certificate) :
    search judgment (budget + extra) = search judgment budget := by
  exact (run_add judgment budget extra initial).trans
    (run_settled judgment extra (search judgment budget) certificate found)

end Mettapedia.OSLF.NativeTypes.Certificates.Search

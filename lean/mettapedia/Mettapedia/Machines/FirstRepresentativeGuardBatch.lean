import Mettapedia.Machines.OrderedInsertGuardBatch

/-!
# Guard keys distinct from the complete consumer row

Two rows can name the same membership guard while carrying different effect
arguments. An ordered plan can still be exact if it retains the first actual
row and every present-branch row, rather than replacing them by the guard key.
This widens the key-only region without granting permission to reorder rows.

The guard set changes only by inserting the selected row's key on successful
completion. Faults retain the actual partial state. Source enumeration order
and complete row capture remain native admission obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.FirstRepresentativeGuardBatch

open GuardedConsumerProjection (Completion)
open OrderedInsertGuardBatch (State Receipt Token done prepend)

variable {Row Key World Answer Event Fault : Type} [DecidableEq Key]

abbrev Branch (Row Key World Answer Event Fault : Type) :=
  Row → State Key World → Receipt Key World Answer Event Fault

abbrev SuccessfulInsert (key : Row → Key) (branch : Branch Row Key World Answer Event Fault) : Prop :=
  ∀ row state, key row ∉ state.seen → (branch row state).completion = .complete →
    (branch row state).state.seen = insert (key row) state.seen

def sequential (key : Row → Key) (fresh : Branch Row Key World Answer Event Fault)
    (present : Row → State Key World → List Answer × List Event) :
    List Row → State Key World → Receipt Key World Answer Event Fault
  | [], state => done state
  | row :: rest, state =>
      if key row ∈ state.seen then
        let observed := present row state
        prepend ⟨state, observed.1, observed.2, .complete⟩ (sequential key fresh present rest state)
      else
        let first := fresh row state
        match first.completion with
        | .complete => prepend first (sequential key fresh present rest first.state)
        | _ => first

def plan (key : Row → Key) : List Row → Finset Key → List (Token Row)
  | [], _ => []
  | row :: rest, seen =>
      if key row ∈ seen then .present row :: plan key rest seen
      else .fresh row :: plan key rest (insert (key row) seen)

def execute (fresh : Branch Row Key World Answer Event Fault)
    (present : Row → State Key World → List Answer × List Event) :
    List (Token Row) → State Key World → Receipt Key World Answer Event Fault
  | [], state => done state
  | .present row :: rest, state =>
      let observed := present row state
      prepend ⟨state, observed.1, observed.2, .complete⟩ (execute fresh present rest state)
  | .fresh row :: rest, state =>
      let first := fresh row state
      match first.completion with
      | .complete => prepend first (execute fresh present rest first.state)
      | _ => first

/-- Effects may read row fields absent from the guard key. Exactness comes
from retaining the complete selected occurrence, not from treating rows as
interchangeable merely because their guard keys agree. -/
theorem planned_refines (key : Row → Key) (fresh : Branch Row Key World Answer Event Fault)
    (present : Row → State Key World → List Answer × List Event)
    (insertLaw : SuccessfulInsert key fresh) (rows : List Row) (state : State Key World) :
    execute fresh present (plan key rows state.seen) state = sequential key fresh present rows state := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih =>
      by_cases held : key row ∈ state.seen
      · simp only [plan, sequential, if_pos held, execute, ih]
      · simp only [plan, sequential, if_neg held, execute]
        cases outcome : (fresh row state).completion with
        | complete =>
            have published := insertLaw row state held outcome
            rw [← published, ih]
        | fault reason => rfl
        | unavailable => rfl

namespace Controls

def fresh (row : Nat × Nat) (state : State Nat (List Nat)) : Receipt Nat (List Nat) Nat Nat Nat :=
  ⟨⟨insert row.1 state.seen, state.world ++ [row.2]⟩, [row.2], [row.1], .complete⟩

def present (_ : Nat × Nat) (_ : State Nat (List Nat)) : List Nat × List Nat := ([], [])

theorem law : SuccessfulInsert Prod.fst fresh := by intro row state _ _; rfl

theorem first_full_row_matters :
    (execute fresh present (plan Prod.fst [(7, 10), (7, 20)] ∅) ⟨∅, []⟩).answers = [10] ∧
    (execute fresh present (plan Prod.fst [(7, 20), (7, 10)] ∅) ⟨∅, []⟩).answers = [20] := by decide

theorem all_present_rows_can_still_answer :
    (execute fresh (fun row _ => ([row.2], []))
      (plan Prod.fst [(7, 10), (7, 20)] ∅) ⟨∅, []⟩).answers = [10, 20] := by decide

end Controls

#print axioms planned_refines
#print axioms Controls.first_full_row_matters

end Mettapedia.Machines.FirstRepresentativeGuardBatch

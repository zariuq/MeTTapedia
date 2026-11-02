import Mettapedia.Machines.GuardedConsumerProjection

/-!
# Ordered batching for insert-on-absence guards

A successful fresh branch publishes its own guard key, without changing
other guard keys. Its other effects and answers are arbitrary and ordered.
A pure planning pass records fresh/present tokens for every candidate; the
executor then runs the fresh branches in their original order. Present
tokens remain, because their branch may emit answers. Failure stops execution
and retains the branch's actual partial state, not the planner's final set.

This is not arbitrary effect commutation. A key must retain the complete
consumer information, and the successful guard-set contract is a separate
admission requirement. The earlier projection theorem supplies a finite
capture of binding coordinates; it does not alone justify deduplication.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedInsertGuardBatch

open GuardedConsumerProjection (Completion)

variable {Key World Answer Event Fault : Type} [DecidableEq Key]

structure State (Key World : Type) where
  seen : Finset Key
  world : World
  deriving DecidableEq

structure Receipt (Key World Answer Event Fault : Type) where
  state : State Key World
  answers : List Answer
  events : List Event
  completion : Completion Fault
  deriving DecidableEq

abbrev Branch (Key World Answer Event Fault : Type) :=
  Key → State Key World → Receipt Key World Answer Event Fault

abbrev SuccessfulInsert (branch : Branch Key World Answer Event Fault) : Prop :=
  ∀ key state, key ∉ state.seen → (branch key state).completion = .complete →
    (branch key state).state.seen = insert key state.seen

def done (state : State Key World) : Receipt Key World Answer Event Fault :=
  ⟨state, [], [], .complete⟩

def prepend (first later : Receipt Key World Answer Event Fault) : Receipt Key World Answer Event Fault :=
  { later with answers := first.answers ++ later.answers, events := first.events ++ later.events }

/-- Reference: each guard reads the state left by the preceding branch. -/
def sequential (fresh : Branch Key World Answer Event Fault)
    (present : Key → State Key World → List Answer × List Event) :
    List Key → State Key World → Receipt Key World Answer Event Fault
  | [], state => done state
  | key :: rest, state =>
      if key ∈ state.seen then
        let observed := present key state
        prepend ⟨state, observed.1, observed.2, .complete⟩ (sequential fresh present rest state)
      else
        let first := fresh key state
        match first.completion with
        | .complete => prepend first (sequential fresh present rest first.state)
        | _ => first

inductive Token (Key : Type) where
  | fresh (key : Key)
  | present (key : Key)
  deriving DecidableEq

/-- Only the planner's private set advances here; no world effect occurs. -/
def plan : List Key → Finset Key → List (Token Key)
  | [], _ => []
  | key :: rest, seen =>
      if key ∈ seen then .present key :: plan rest seen
      else .fresh key :: plan rest (insert key seen)

def execute (fresh : Branch Key World Answer Event Fault)
    (present : Key → State Key World → List Answer × List Event) :
    List (Token Key) → State Key World → Receipt Key World Answer Event Fault
  | [], state => done state
  | .present key :: rest, state =>
      let observed := present key state
      prepend ⟨state, observed.1, observed.2, .complete⟩ (execute fresh present rest state)
  | .fresh key :: rest, state =>
      let first := fresh key state
      match first.completion with
      | .complete => prepend first (execute fresh present rest first.state)
      | _ => first

/-- Full refinement includes failure and unavailable outcomes, the actual
partial state, every answer occurrence, and the ordered effect trace. -/
theorem planned_refines (fresh : Branch Key World Answer Event Fault)
    (present : Key → State Key World → List Answer × List Event)
    (insertLaw : SuccessfulInsert fresh) (keys : List Key) (state : State Key World) :
    execute fresh present (plan keys state.seen) state = sequential fresh present keys state := by
  induction keys generalizing state with
  | nil => rfl
  | cons key rest ih =>
      by_cases held : key ∈ state.seen
      · simp only [plan, sequential, if_pos held, execute, ih]
      · simp only [plan, sequential, if_neg held, execute]
        cases outcome : (fresh key state).completion with
        | complete =>
            have published := insertLaw key state held outcome
            rw [← published, ih]
        | fault reason => rfl
        | unavailable => rfl

def resume (fresh : Branch Key World Answer Event Fault)
    (present : Key → State Key World → List Answer × List Event)
    (suffix : List Key) (first : Receipt Key World Answer Event Fault) :
    Receipt Key World Answer Event Fault :=
  match first.completion with
  | .complete => prepend first (sequential fresh present suffix first.state)
  | _ => first

/-- Batches can be cut at any candidate boundary without changing authored
order; a stopped prefix does not execute the later batch. -/
theorem sequential_append (fresh : Branch Key World Answer Event Fault)
    (present : Key → State Key World → List Answer × List Event)
    (first later : List Key) (state : State Key World) :
    sequential fresh present (first ++ later) state =
      resume fresh present later (sequential fresh present first state) := by
  induction first generalizing state with
  | nil => simp [sequential, resume, prepend, done]
  | cons key rest ih =>
      simp only [List.cons_append, sequential]
      by_cases held : key ∈ state.seen
      · simp only [if_pos held]
        rw [ih]
        cases result : sequential fresh present rest state with
        | mk final answers events stop =>
            cases stop <;> simp [resume, prepend, List.append_assoc]
      · simp only [if_neg held]
        cases result : fresh key state with
        | mk final answers events stop =>
            cases stop with
            | complete =>
                simp only
                rw [ih]
                cases tail : sequential fresh present rest final with
                | mk last tailAnswers tailEvents tailStop =>
                    cases tailStop <;> simp [resume, prepend, List.append_assoc]
            | fault reason => rfl
            | unavailable => rfl

theorem present_repetition (fresh : Branch Key World Answer Event Fault)
    (present : Key → State Key World → List Answer × List Event)
    (key : Key) (state : State Key World) (held : key ∈ state.seen) (n : Nat) :
    (sequential fresh present (List.replicate n key) state).state = state ∧
    (sequential fresh present (List.replicate n key) state).completion = .complete ∧
    (sequential fresh present (List.replicate n key) state).answers.length =
      n * (present key state).1.length := by
  induction n with
  | zero => simp [sequential, done]
  | succ n ih =>
      simp only [List.replicate_succ, sequential, if_pos held, prepend,
        List.length_append, ih.1, ih.2.1, ih.2.2]
      simp [Nat.succ_mul, Nat.add_comm]

/-- A grouped visit has one fresh answer contribution, followed by the
present-branch contribution for every remaining occurrence. -/
theorem fresh_repetition_count (fresh : Branch Key World Answer Event Fault)
    (present : Key → State Key World → List Answer × List Event)
    (insertLaw : SuccessfulInsert fresh) (key : Key) (state : State Key World)
    (absent : key ∉ state.seen) (completed : (fresh key state).completion = .complete) (n : Nat) :
    (sequential fresh present (List.replicate (n + 1) key) state).answers.length =
      (fresh key state).answers.length + n * (present key (fresh key state).state).1.length := by
  have held : key ∈ (fresh key state).state.seen := by
    rw [insertLaw key state absent completed]
    exact Finset.mem_insert_self _ _
  have rest := (present_repetition fresh present key (fresh key state).state held n).2.2
  simp [List.replicate_succ, sequential, absent, completed, prepend, rest]

namespace Controls

def fresh (key : Nat) (state : State Nat Nat) : Receipt Nat Nat Nat Nat Nat :=
  ⟨⟨insert key state.seen, state.world + 2⟩, [key, key], [key], .complete⟩

def present (_ : Nat) (_ : State Nat Nat) : List Nat × List Nat := ([], [])

theorem fresh_law : SuccessfulInsert fresh := by intro key state _ _; rfl

theorem duplicates_inside_a_branch_are_not_deduplicated :
    (execute fresh present (plan [7, 7] ∅) ⟨∅, 0⟩).answers = [7, 7] ∧
    (execute fresh present (plan [7, 7] ∅) ⟨∅, 0⟩).state.world = 2 := by decide

theorem present_answers_still_count :
    (execute fresh (fun _ _ => ([99], [])) (plan [7, 7] ∅) ⟨∅, 0⟩).answers = [7, 7, 99] := by decide

def fails (key : Nat) (state : State Nat Nat) : Receipt Nat Nat Nat Nat Nat :=
  ⟨⟨state.seen, state.world + 1⟩, [], [key], .fault 3⟩

theorem planning_does_not_publish_future_keys_after_failure :
    (execute fails present (plan [7, 8] ∅) ⟨∅, 0⟩).state = ⟨∅, 1⟩ ∧
    (execute fails present (plan [7, 8] ∅) ⟨∅, 0⟩).events = [7] := by decide

def ordered (key : Nat) (state : State Nat Nat) : Receipt Nat Nat Nat Nat Nat :=
  ⟨⟨insert key state.seen, 10 * state.world + key⟩, [], [key], .complete⟩

theorem effects_cannot_be_reordered :
    (execute ordered present (plan [1, 2] ∅) ⟨∅, 0⟩).state.world = 12 ∧
    (execute ordered present (plan [2, 1] ∅) ⟨∅, 0⟩).state.world = 21 := by decide

end Controls

#print axioms planned_refines
#print axioms sequential_append
#print axioms fresh_repetition_count

end Mettapedia.Machines.OrderedInsertGuardBatch

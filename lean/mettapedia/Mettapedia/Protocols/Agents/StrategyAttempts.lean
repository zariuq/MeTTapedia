import Mathlib.Tactic

/-!
# The effect broker's command attempts

A batch the broker admitted under a ticket is open for its turn. Before each of
its commands runs, the command is recorded in the ledger as attempted, at the
batch's next position; the ledger records an attempt `(ticket, position)` at
most once and refuses a repeat. A command whose attempt the ledger refused (or
could not record) does not run: the batch fails there, and its position does
not move. A command of a turn without an open batch runs unrecorded. A
command's receipt names the batch's last attempt.

Invariants proved here:
* every command that ran under a ticket had its attempt recorded before it ran;
* a refused attempt runs nothing and changes nothing;
* a command of another turn is not recorded;
* after `n` commands of a fresh batch ran, its attempts are positions
  `0, …, n - 1`, in order, with no gap and no repeat;
* a receipt names the attempt of the command that ran last.

The counterexample advances the position on a refused attempt: the batch's next
command is then recorded at a position after a gap, and a receipt names an
attempt that was never recorded.

This is an abstract contract, not a refinement proof of
`src/strategy_attempts_cetta.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.StrategyAttempts

/-- The open batch: its turn, its ticket and its next position. -/
structure Batch where
  turn : ℕ
  ticket : ℕ
  next : ℕ
  deriving DecidableEq

/-- A command that ran: under an attempt `(ticket, position)`, or unrecorded. -/
inductive Ran
  | recorded (ticket position : ℕ)
  | unrecorded (turn : ℕ)
  deriving DecidableEq

structure State where
  ledger : List (ℕ × ℕ)
  batch : Option Batch
  ran : List Ran
  failed : Bool
  deriving DecidableEq

/-- The ledger records an attempt once. -/
def record (l : List (ℕ × ℕ)) (t p : ℕ) : Option (List (ℕ × ℕ)) :=
  if (t, p) ∈ l then none else some (l ++ [(t, p)])

def openBatch (s : State) (turn ticket : ℕ) : State := { s with batch := some ⟨turn, ticket, 0⟩ }

/-- One command of `turn` is dispatched. -/
def dispatch (s : State) (turn : ℕ) : State :=
  match s.batch with
  | none => { s with ran := s.ran ++ [.unrecorded turn] }
  | some b =>
    if b.turn ≠ turn then { s with ran := s.ran ++ [.unrecorded turn] }
    else match record s.ledger b.ticket b.next with
      | none => { s with failed := true }
      | some l => { s with ledger := l, batch := some { b with next := b.next + 1 },
                           ran := s.ran ++ [.recorded b.ticket b.next] }

/-- The attempt a receipt of `turn` names: the batch's last. -/
def attempt (s : State) (turn : ℕ) : Option (ℕ × ℕ) :=
  match s.batch with
  | none => none
  | some b => if b.turn = turn ∧ 0 < b.next then some (b.ticket, b.next - 1) else none

/-- Every command that ran under a ticket had its attempt recorded. -/
def recordedBeforeRunning (s : State) : Prop :=
  ∀ t p, Ran.recorded t p ∈ s.ran → (t, p) ∈ s.ledger

theorem dispatch_keeps_recorded (s : State) (turn : ℕ) (h : recordedBeforeRunning s) :
    recordedBeforeRunning (dispatch s turn) := by
  intro t p hr
  unfold dispatch at hr ⊢
  cases hb : s.batch with
  | none =>
    simp only [hb, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | hr
    · exact h t p hr
    · cases hr
  | some b =>
    simp only [hb] at hr ⊢
    split_ifs at hr ⊢ with ht
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | hr
      · exact h t p hr
      · cases hr
    · unfold record at hr ⊢
      split_ifs at hr ⊢ with hm
      · exact h t p hr
      · simp only [List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with hr | hr
        · exact Or.inl (h t p hr)
        · cases hr; exact Or.inr rfl

theorem refused_runs_nothing (s : State) (b : Batch) (hb : s.batch = some b) (turn : ℕ) (ht : b.turn = turn)
    (hm : (b.ticket, b.next) ∈ s.ledger) :
    dispatch s turn = { s with failed := true } := by
  simp [dispatch, hb, ht, record, hm]

theorem other_turn_unrecorded (s : State) (b : Batch) (hb : s.batch = some b) (turn : ℕ) (ht : b.turn ≠ turn) :
    (dispatch s turn).ledger = s.ledger ∧ (dispatch s turn).batch = s.batch := by
  simp [dispatch, hb, ht]

/-- Dispatching `n` commands of the batch's turn. -/
def dispatchN (s : State) (turn : ℕ) : ℕ → State
  | 0 => s
  | n + 1 => dispatch (dispatchN s turn n) turn

/-- A fresh ticket's batch records positions `0, …, n - 1`, in order. -/
theorem fresh_batch_positions (s : State) (turn ticket : ℕ) (hf : ∀ p, (ticket, p) ∉ s.ledger) (n : ℕ) :
    (dispatchN (openBatch s turn ticket) turn n).ledger = s.ledger ++ (List.range n).map (fun p => (ticket, p)) ∧
    (dispatchN (openBatch s turn ticket) turn n).batch = some ⟨turn, ticket, n⟩ := by
  induction n with
  | zero => simp [dispatchN, openBatch]
  | succ n ih =>
    obtain ⟨hl, hb⟩ := ih
    have hnot : (ticket, n) ∉ (dispatchN (openBatch s turn ticket) turn n).ledger := by
      rw [hl]; simp only [List.mem_append, List.mem_map, List.mem_range, not_or, not_exists, not_and]
      exact ⟨hf n, fun p hp h => by simp at h; omega⟩
    have hstep : dispatchN (openBatch s turn ticket) turn (n + 1)
        = { dispatchN (openBatch s turn ticket) turn n with
              ledger := (dispatchN (openBatch s turn ticket) turn n).ledger ++ [(ticket, n)],
              batch := some ⟨turn, ticket, n + 1⟩,
              ran := (dispatchN (openBatch s turn ticket) turn n).ran ++ [.recorded ticket n] } := by
      simp [dispatchN, dispatch, hb, record, hnot]
    rw [hstep]
    refine ⟨?_, rfl⟩
    simp [hl, List.range_succ]

/-- A receipt names the attempt of the command that ran last. -/
theorem receipt_names_the_last_attempt (s : State) (turn ticket : ℕ) (hf : ∀ p, (ticket, p) ∉ s.ledger) (n : ℕ) :
    attempt (dispatchN (openBatch s turn ticket) turn (n + 1)) turn = some (ticket, n) := by
  unfold attempt
  rw [(fresh_batch_positions s turn ticket hf (n + 1)).2]
  simp

/-! ## Counterexample: the position moves on a refused attempt -/

def dispatchAdvancing (s : State) (turn : ℕ) : State :=
  match s.batch with
  | none => s
  | some b =>
    if b.turn ≠ turn then s
    else match record s.ledger b.ticket b.next with
      | none => { s with batch := some { b with next := b.next + 1 } }
      | some l => { s with ledger := l, batch := some { b with next := b.next + 1 },
                           ran := s.ran ++ [.recorded b.ticket b.next] }

/-- Ticket 3's attempt at position 0 already exists (a replayed batch). -/
def replayed : State := ⟨[(3, 0)], some ⟨5, 3, 0⟩, [], false⟩

theorem checked_refusal_fails_and_names_nothing :
    dispatch replayed 5 = { replayed with failed := true } ∧ attempt (dispatch replayed 5) 5 = none := by
  decide +kernel

/-- The advancing dispatcher's receipt names attempt (3, 0), which this batch
never recorded: the replayed attempt's result would be overwritten. -/
theorem advancing_receipt_names_an_unrecorded_attempt :
    attempt (dispatchAdvancing replayed 5) 5 = some (3, 0) ∧ (dispatchAdvancing replayed 5).ran = [] := by
  decide +kernel

end Mettapedia.Protocols.Agents.StrategyAttempts

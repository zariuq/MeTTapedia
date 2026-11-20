import Mathlib.Data.List.TakeDrop

/-!
# Loans of ordered occurrences

A producer may advance to expose an item before the consumer commits it.
The pending item remains the first occurrence of the logical suffix.
This uses an abstract cursor and terminal observation, including for the
ordinary consumer that never reads ahead.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.OrderedReturnLoans

variable {Cursor Item Cause : Type}

def first (suffix : List Item × Cause) : Except Cause (Item × (List Item × Cause)) :=
  match suffix.1 with
  | [] => .error suffix.2
  | item :: later => .ok (item, later, suffix.2)

structure Read (Cursor Item Cause : Type) where
  position : Cursor → Nat
  view : Cursor → List Item × Cause
  pull : Cursor → Except Cause (Item × Cursor)
  exactView : ∀ cursor, (pull cursor).map (fun (item, next) => (item, view next)) = first (view cursor)
  advancePosition : ∀ {cursor next item}, pull cursor = .ok (item, next) →
    position next = position cursor + 1

variable (reader : Read Cursor Item Cause)

theorem Read.pulled_view {cursor next : Cursor} {item : Item} (pull : reader.pull cursor = .ok (item, next)) :
    reader.view cursor = (item :: (reader.view next).1, (reader.view next).2) := by
  have exactView := reader.exactView cursor
  rw [pull] at exactView
  cases seen : reader.view cursor with
  | mk rows cause =>
    rw [seen] at exactView
    cases rows with
    | nil => simp [first, Except.map] at exactView
    | cons head rest =>
      change Except.ok (item, reader.view next) = Except.ok (head, rest, cause) at exactView
      obtain ⟨rfl, same⟩ := Prod.mk.inj (Except.ok.inj exactView)
      rw [same]

theorem Read.stopped_view {cursor : Cursor} {cause : Cause} (pull : reader.pull cursor = .error cause) :
    reader.view cursor = ([], cause) := by
  have exactView := reader.exactView cursor
  rw [pull] at exactView
  cases seen : reader.view cursor with
  | mk rows ending =>
    rw [seen] at exactView
    cases rows with
    | nil =>
      change (Except.error cause : Except Cause (Item × (List Item × Cause))) = Except.error ending at exactView
      rw [Except.error.inj exactView]
    | cons head rest => simp [first, Except.map] at exactView

def Read.take : Nat → Cursor → List Item × Cursor
  | 0, cursor => ([], cursor)
  | demand + 1, cursor =>
    match reader.pull cursor with
    | .error _ => ([], cursor)
    | .ok (item, next) =>
      let later := take demand next
      (item :: later.1, later.2)

theorem Read.take_exact (demand : Nat) (cursor : Cursor) :
    let result := reader.take demand cursor
    result.1 = (reader.view cursor).1.take demand ∧
      reader.view result.2 = ((reader.view cursor).1.drop demand, (reader.view cursor).2) ∧
      reader.position result.2 = reader.position cursor + result.1.length := by
  induction demand generalizing cursor with
  | zero => simp [Read.take]
  | succ demand ih =>
    cases pulled : reader.pull cursor with
    | error cause => simp [Read.take, pulled, reader.stopped_view pulled]
    | ok result =>
      obtain ⟨item, next⟩ := result
      obtain ⟨prefixEq, suffixEq, positionEq⟩ := ih next
      simp only [Read.take, pulled, reader.pulled_view pulled, List.take_succ_cons,
        List.drop_succ_cons, List.length_cons]
      exact ⟨congrArg (List.cons item) prefixEq, suffixEq, by
        rw [positionEq, reader.advancePosition pulled]
        omega⟩

structure Loan (Cursor Item : Type) where
  backing : Cursor
  pending : Option Item

def Loan.idle (cursor : Cursor) : Loan Cursor Item := ⟨cursor, none⟩

def position (loan : Loan Cursor Item) : Nat :=
  reader.position loan.backing - loan.pending.toList.length

def remaining (loan : Loan Cursor Item) : List Item × Cause :=
  (loan.pending.toList ++ (reader.view loan.backing).1, (reader.view loan.backing).2)

def borrow (loan : Loan Cursor Item) : Except Cause (Item × Loan Cursor Item) :=
  match loan.pending with
  | some item => .ok (item, loan)
  | none => (reader.pull loan.backing).map (fun (item, next) => (item, ⟨next, some item⟩))

def commit (loan : Loan Cursor Item) (authority : Bool) (offered : Nat) :
    Option Item × Loan Cursor Item :=
  if authority && offered == position reader loan then
    match loan.pending with
    | none => (none, loan)
    | some item => (some item, .idle loan.backing)
  else (none, loan)

inductive Related (cursor : Cursor) : Loan Cursor Item → Prop where
  | idle : Related cursor (.idle cursor)
  | held {item next} (h : reader.pull cursor = .ok (item, next)) : Related cursor ⟨next, some item⟩

theorem Related.position {cursor : Cursor} {loan : Loan Cursor Item} (rel : Related reader cursor loan) :
    position reader loan = reader.position cursor := by
  cases rel with
  | idle => simp [OrderedReturnLoans.position, Loan.idle]
  | held pulled => simp [OrderedReturnLoans.position, reader.advancePosition pulled]

theorem Related.remaining {cursor : Cursor} {loan : Loan Cursor Item} (rel : Related reader cursor loan) :
    remaining reader loan = reader.view cursor := by
  cases rel with
  | idle => simp [OrderedReturnLoans.remaining, Loan.idle]
  | held pulled => exact (reader.pulled_view pulled).symm

theorem reborrow (backing : Cursor) (item : Item) :
    borrow reader ⟨backing, some item⟩ = .ok (item, ⟨backing, some item⟩) := rfl

theorem borrow_exact {cursor : Cursor} {loan : Loan Cursor Item} (rel : Related reader cursor loan) :
    borrow reader loan = (reader.pull cursor).map (fun (item, next) => (item, ⟨next, some item⟩)) := by
  cases rel with
  | idle => rfl
  | held pulled => simp [borrow, pulled, Except.map]

theorem refusal_keeps_loan (loan : Loan Cursor Item) (offered : Nat) :
    commit reader loan false offered = (none, loan) := by simp [commit]

theorem stale_offer_keeps_loan (loan : Loan Cursor Item) (authority : Bool) (offered : Nat)
    (stale : offered ≠ position reader loan) : commit reader loan authority offered = (none, loan) := by
  simp [commit, stale]

theorem commit_exact {cursor next : Cursor} {item : Item}
    (pulled : reader.pull cursor = .ok (item, next)) :
    commit reader ⟨next, some item⟩ true (reader.position cursor) = (some item, Loan.idle next) := by
  have held : Related reader cursor ⟨next, some item⟩ := .held pulled
  simp [commit, held.position]

def deliver : Nat → Loan Cursor Item → List Item × Loan Cursor Item
  | 0, loan => ([], loan)
  | budget + 1, loan =>
    match borrow reader loan with
    | .error _ => ([], loan)
    | .ok (_, pending) =>
      match commit reader pending true (position reader loan) with
      | (none, kept) => ([], kept)
      | (some item, next) =>
        let later := deliver budget next
        (item :: later.1, later.2)

theorem deliver_refines {cursor : Cursor} {loan : Loan Cursor Item} (related : Related reader cursor loan)
    (budget : Nat) :
    (deliver reader budget loan).1 = (reader.take budget cursor).1 ∧
      Related reader (reader.take budget cursor).2 (deliver reader budget loan).2 := by
  induction budget generalizing loan cursor with
  | zero => exact ⟨rfl, related⟩
  | succ budget ih =>
    cases observed : reader.pull cursor with
    | error cause =>
      simp [deliver, borrow_exact reader related, observed, Except.map, Read.take, related]
    | ok answer =>
      obtain ⟨item, next⟩ := answer
      obtain ⟨same, after⟩ := ih (Related.idle (reader := reader) (cursor := next))
      simp [deliver, borrow_exact reader related, observed, Except.map, Read.take, related.position,
        commit_exact reader observed, same, after]

theorem ordered_prefix {cursor : Cursor} {loan : Loan Cursor Item} (rel : Related reader cursor loan)
    (budget : Nat) :
    let outcome := deliver reader budget loan
    outcome.1 = (remaining reader loan).1.take budget ∧
      remaining reader outcome.2 = ((remaining reader loan).1.drop budget, (remaining reader loan).2) := by
  obtain ⟨sent, next⟩ := deliver_refines reader rel budget
  rw [rel.remaining]
  exact ⟨sent.trans (reader.take_exact budget cursor).1, next.remaining.trans (reader.take_exact budget cursor).2.1⟩

def listReader (Item Cause : Type) : Read (Nat × List Item × Cause) Item Cause where
  position := Prod.fst
  view := Prod.snd
  pull := fun (position, rest, cause) => match rest with
    | [] => .error cause
    | item :: later => .ok (item, position + 1, later, cause)
  exactView := by rintro ⟨_, rows, _⟩; cases rows <;> rfl
  advancePosition := by
    rintro ⟨_, rows, _⟩ next item seen
    cases rows <;> cases seen
    rfl

namespace Controls

private def testReader := listReader Nat String
private def cursor : Nat × List Nat × String := (0, [7, 7, 9], "interrupted")

theorem ordered_duplicates_and_stop_survive :
    let step := deliver testReader 2 (Loan.idle cursor)
    step.1 = [7, 7] ∧ remaining testReader step.2 = ([9], "interrupted") := by decide +kernel

theorem stale_commit_cannot_drop_pending_item :
    let pending : Loan (Nat × List Nat × String) Nat := ⟨(1, [7, 9], "interrupted"), some 7⟩
    (commit testReader pending true 1).1 = none ∧ remaining testReader (commit testReader pending true 1).2 =
      ([7, 7, 9], "interrupted") := by decide +kernel

end Controls

end Mettapedia.Machines.Cursor.OrderedReturnLoans

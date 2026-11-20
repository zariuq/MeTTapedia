import Mettapedia.Machines.Cursor.OrderedReturnLoans
import Mettapedia.Machines.CMemory.SpatialLoans

/-!
# Guarded transfer of ordered returns

A receiver observes a binding version and a cursor together. An exclusive
loan protects this observation from writes to the same cell during a
transfer. The accepted prefix is committed once, and a refused installation
leaves the producer's pending occurrence available.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.GuardedOrderedReturns

open OrderedReturnLoans
open Mettapedia.Machines.CMemory.Borrowing

variable {Cell Cursor Item Cause Stamp : Type} [DecidableEq Cell] [DecidableEq Stamp]

structure Receiver (Stamp Cursor : Type) where
  version : Stamp
  cursor : Cursor

structure Write (Cell Stamp Cursor : Type) where
  actor : Nat
  cell : Cell
  binding : Receiver Stamp Cursor

def Write.apply (directory : Cell → Receiver Stamp Cursor)
    (write : Write Cell Stamp Cursor) : Cell → Receiver Stamp Cursor :=
  Function.update directory write.cell write.binding

omit [DecidableEq Stamp] in
theorem protected_receiver (loans : List (LoanOf (Finset Cell))) (ordered : OrderedIn loans)
    (owner : Nat) (cell : Cell) (custody : AccessIn (finiteGeometry Cell) loans owner {cell} true)
    (initial : Cell → Receiver Stamp Cursor) (writes : List (Write Cell Stamp Cursor))
    (permitted : ∀ write ∈ writes, write.actor ≠ owner ∧
      AccessIn (finiteGeometry Cell) loans write.actor {write.cell} true) :
    (writes.foldl Write.apply initial) cell = initial cell := by
  induction writes generalizing initial with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨different, access⟩ := permitted first (by simp)
    have separate := exclusive_access_disjoint_in (finiteGeometry Cell) ordered different access custody
    have outside : cell ≠ first.cell := by
      intro same
      exact Finset.disjoint_left.mp separate (by simp [same]) (Finset.mem_singleton_self cell)
    rw [List.foldl_cons, ih _ (fun write member => permitted write (by simp [member])),
      Write.apply, Function.update_of_ne outside]

variable (reader : Read Cursor Item Cause)

def accepts (receiver : Receiver Stamp Cursor) (valid : Bool) (version : Stamp) (offered : Nat) : Bool :=
  valid && decide (version = receiver.version) && decide (offered = reader.position receiver.cursor)

def transfer (directory : Cell → Receiver Stamp Cursor) (cell : Cell)
    (valid : Bool) (version : Stamp) (offered budget : Nat) :
    Option (List Item) × (Cell → Receiver Stamp Cursor) :=
  let receiver := directory cell
  if accepts reader receiver valid version offered then
    let taken := reader.take budget receiver.cursor
    (some taken.1, Function.update directory cell { receiver with cursor := taken.2 })
  else (none, directory)

theorem transfer_at_protected_receiver (loans : List (LoanOf (Finset Cell))) (ordered : OrderedIn loans)
    (owner : Nat) (cell : Cell) (custody : AccessIn (finiteGeometry Cell) loans owner {cell} true)
    (initial : Cell → Receiver Stamp Cursor) (writes : List (Write Cell Stamp Cursor))
    (permitted : ∀ write ∈ writes, write.actor ≠ owner ∧
      AccessIn (finiteGeometry Cell) loans write.actor {write.cell} true)
    (valid : Bool) (version : Stamp) (offered budget : Nat) :
    let live := writes.foldl Write.apply initial
    transfer reader live cell valid version offered budget =
      if accepts reader (initial cell) valid version offered then
        let taken := reader.take budget (initial cell).cursor
        (some taken.1, Function.update live cell { initial cell with cursor := taken.2 })
      else (none, live) := by
  have kept := protected_receiver loans ordered owner cell custody initial writes permitted
  simp only [transfer, kept]

theorem refused_preserves_directory (directory : Cell → Receiver Stamp Cursor) (cell : Cell)
    (version : Stamp) (offered budget : Nat) :
    transfer reader directory cell false version offered budget = (none, directory) := by
  simp [transfer, accepts]

theorem settles_pending (directory : Cell → Receiver Stamp Cursor) (cell : Cell)
    (valid : Bool) (version : Stamp) (offered : Nat)
    {producer pending : Loan Cursor Item} {item : Item}
    (related : Related reader (directory cell).cursor producer)
    (loaned : borrow reader producer = .ok (item, pending)) :
    let sent := transfer reader directory cell valid version offered 1
    let settled := commit reader pending sent.1.isSome offered
    sent.1 = settled.1.map (fun result => [result]) ∧
      Related reader (sent.2 cell).cursor settled.2 ∧
      (sent.1 = none → sent.2 = directory ∧ settled.2 = pending) := by
  rw [borrow_exact reader related] at loaned
  cases pulled : reader.pull (directory cell).cursor with
  | error cause => simp [pulled, Except.map] at loaned
  | ok result =>
    obtain ⟨answer, next⟩ := result
    simp only [pulled, Except.map, Except.ok.injEq, Prod.mk.injEq] at loaned
    obtain ⟨rfl, rfl⟩ := loaned
    by_cases accepted : accepts reader (directory cell) valid version offered = true
    · have atPosition : offered = reader.position (directory cell).cursor := by
        simp [accepts] at accepted
        exact accepted.2
      simp only [transfer, accepted, if_true, Read.take, pulled, Function.update_self,
        Option.isSome_some]
      rw [atPosition, commit_exact reader pulled]
      exact ⟨rfl, .idle, fun h => by cases h⟩
    · simp only [transfer, if_neg accepted, Option.isSome_none, refusal_keeps_loan, Option.map_none]
      exact ⟨trivial, .held pulled, fun _ => ⟨trivial, trivial⟩⟩

theorem installed_prefix (directory : Cell → Receiver Stamp Cursor) (cell : Cell)
    (valid : Bool) (version : Stamp) (offered budget : Nat)
    {items : List Item} {after : Cell → Receiver Stamp Cursor}
    (accepted : transfer reader directory cell valid version offered budget = (some items, after)) :
    items = (reader.view (directory cell).cursor).1.take budget ∧
      reader.position (after cell).cursor = offered + items.length ∧
      reader.view (after cell).cursor =
        ((reader.view (directory cell).cursor).1.drop budget, (reader.view (directory cell).cursor).2) := by
  unfold transfer at accepted
  dsimp only at accepted
  split at accepted
  · rename_i authorized
    have positioned : offered = reader.position (directory cell).cursor := by
      simp [accepts] at authorized
      exact authorized.2
    have itemsEq := Option.some.inj (Prod.mk.inj accepted).1
    have directoryEq := (Prod.mk.inj accepted).2
    subst items
    subst after
    simp only [Function.update_self]
    rw [positioned]
    obtain ⟨sent, suffix, advanced⟩ := reader.take_exact budget (directory cell).cursor
    exact ⟨sent, advanced, suffix⟩
  · cases (Prod.mk.inj accepted).1

theorem installed_nonempty_prefix_cannot_replay (directory : Cell → Receiver Stamp Cursor)
    (cell : Cell) (valid : Bool) (version : Stamp) (offered budget : Nat)
    {items : List Item} {after : Cell → Receiver Stamp Cursor}
    (accepted : transfer reader directory cell valid version offered budget = (some items, after))
    (nonempty : items ≠ []) (again : Bool) (current : Stamp) (anotherBudget : Nat) :
    transfer reader after cell again current offered anotherBudget = (none, after) := by
  have moved := (installed_prefix reader directory cell valid version offered budget accepted).2.1
  have positive := List.length_pos_iff.mpr nonempty
  have stale : offered ≠ reader.position (after cell).cursor := by omega
  simp [transfer, accepts, stale]

namespace Controls

private def testReader := listReader Nat String
private def directory : Unit → Receiver Nat (Nat × List Nat × String) :=
  fun _ => ⟨2, (0, [7, 7, 9], "cancelled")⟩

theorem accepted_occurrence_advances_the_receiver :
    let sent := transfer testReader directory () true 2 0 1
    sent.1 = some [7] ∧ (sent.2 ()).cursor = (1, [7, 9], "cancelled") := by decide +kernel

theorem stale_version_refuses_without_consumption :
    let sent := transfer testReader directory () true 1 0 1
    sent.1 = none ∧ (sent.2 ()).cursor = (0, [7, 7, 9], "cancelled") := by decide +kernel

end Controls

end Mettapedia.Machines.Cursor.GuardedOrderedReturns

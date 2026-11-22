import Mettapedia.OSLF.NativeTypes.Certificates.FiniteTree
import Mettapedia.Data.List.BlockIndex

/-!
# Checked sharing of finite rule evidence

Rows refer to earlier rows by position. Every premise slot is checked against
its independent rule judgment, including repeated slots. A successful decoder
constructs an ordinary derivation in the original presentation. Sharing does
not identify operational events.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.Shared

open Mettapedia.TypeTheory

universe u
variable {P : Presentation.{u}}

structure Row (P : Presentation.{u}) where
  rule : P.Rule
  references : Fin (P.premises rule).length → Nat

abbrev Entry (P : Presentation.{u}) := Sigma P.Derivation

variable [DecidableEq P.Judgment]

def lookup? (table : List (Entry P)) (position : Nat) (wanted : P.Judgment) :
    Option (P.Derivation wanted) :=
  match table[position]? with
  | none => none
  | some ⟨actual, tree⟩ => if same : actual = wanted then some (same ▸ tree) else none

/-- Independent row validity checks only referenced judgments and earlier-row
bounds. It is not a global derivability premise. -/
def ValidRow (table : List P.Judgment) (row : Row P) : Prop :=
  ∀ position, table[row.references position]? = some ((P.premises row.rule).get position)

def allFin? : {n : Nat} → (F : Fin n → Type u) → ((position : Fin n) → Option (F position)) →
    Option ((position : Fin n) → F position)
  | 0, _, _ => some (fun position => nomatch position)
  | n + 1, F, select => do
      let first ← select 0
      let rest ← allFin? (fun position : Fin n => F position.succ) (fun position => select position.succ)
      pure (Fin.cases first rest)

theorem allFin?_some {n : Nat} {F : Fin n → Type u} {select : (position : Fin n) → Option (F position)}
    {values : (position : Fin n) → F position}
    (found : allFin? F select = some values) (position : Fin n) : select position = some (values position) := by
  induction n with
  | zero => exact Fin.elim0 position
  | succ n ih =>
      unfold allFin? at found
      obtain ⟨first, atFirst, later⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨rest, atRest, same⟩ := Option.bind_eq_some_iff.mp later
      cases Option.some.inj same
      cases position using Fin.cases with
      | zero => exact atFirst
      | succ position => exact ih atRest position

theorem allFin?_complete {n : Nat} {F : Fin n → Type u} {select : (position : Fin n) → Option (F position)}
    (present : ∀ position, (select position).isSome = true) : (allFin? F select).isSome = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have head := present 0
      have tail := ih (fun position => present position.succ)
      cases first : select 0 with
      | none => rw [first] at head; cases head
      | some value =>
          cases rest : allFin? (fun position : Fin n => F position.succ) (fun position => select position.succ) with
          | none => rw [rest] at tail; cases tail
          | some values =>
              simp only [allFin?, first, rest]
              rfl

def decodeRow? (table : List (Entry P)) (row : Row P) : Option (Entry P) := do
  let children ← allFin? (fun position => P.Derivation ((P.premises row.rule).get position))
    (fun position => lookup? table (row.references position) ((P.premises row.rule).get position))
  pure ⟨P.conclusion row.rule, .node ⟨row.rule, rfl⟩ (fun position => children position.down)⟩

def decodeFrom? (table : List (Entry P)) : List (Row P) → Option (List (Entry P))
  | [] => some table
  | row :: rest => do
      let entry ← decodeRow? table row
      decodeFrom? (table ++ [entry]) rest

structure Certificate (P : Presentation.{u}) where
  rows : List (Row P)
  root : Nat

def reconstruct? (certificate : Certificate P) (wanted : P.Judgment) : Option (P.Derivation wanted) := do
  let table ← decodeFrom? [] certificate.rows
  lookup? table certificate.root wanted

def check (certificate : Certificate P) (wanted : P.Judgment) : Bool :=
  (reconstruct? certificate wanted).isSome

theorem accepted_original (certificate : Certificate P) (wanted : P.Judgment)
    (accepted : check certificate wanted = true) :
    ∃ derivation : P.Derivation wanted, reconstruct? certificate wanted = some derivation ∧
      Tree.check (Tree.erase derivation) wanted = true := by
  cases found : reconstruct? certificate wanted with
  | none => simp only [check, found, Option.isSome_none] at accepted; cases accepted
  | some tree => exact ⟨tree, rfl, Tree.check_erase tree⟩

/-! ## Direct checking with a judgment-only table -/

/-- Inspect the actual premise slots in order, stopping at the first refused
reference. The second component counts performed slot checks, including a
failing slot. It does not price list lookup or judgment equality. -/
def inspectPremises (table : List P.Judgment) (row : Row P) :
    List (Fin (P.premises row.rule).length) → Bool × Nat
  | [] => (true, 0)
  | position :: rest =>
      if table[row.references position]? = some ((P.premises row.rule).get position) then
        let later := inspectPremises table row rest
        (later.1, later.2 + 1)
      else (false, 1)

def inspectRow (table : List P.Judgment) (row : Row P) : Bool × Nat :=
  inspectPremises table row (List.finRange (P.premises row.rule).length)

/-- Actual execution data of the plain-table checker. No derivation, proof
function or expanded certificate is stored in the returned table. -/
structure JudgmentCheck (P : Presentation.{u}) where
  table : Option (List P.Judgment)
  rows : Nat
  premiseChecks : Nat

/-- Every row is validated before appending its literal conclusion. A bad
unused row refuses as it does in the original reconstruction checker. -/
def inspectRows (table : List P.Judgment) : List (Row P) → JudgmentCheck P
  | [] => ⟨some table, 0, 0⟩
  | row :: rest =>
      let inspected := inspectRow table row
      if inspected.1 then
        let later := inspectRows (table ++ [P.conclusion row.rule]) rest
        ⟨later.table, later.rows + 1, inspected.2 + later.premiseChecks⟩
      else ⟨none, 1, inspected.2⟩

/-- Static inventory of the certificate's premise occurrences. Unlike the
performed counter, it includes slots after a refusal. -/
def premiseSlots (rows : List (Row P)) : Nat :=
  (rows.map (fun row => (P.premises row.rule).length)).sum

private def inspectPremisesAt (lookup : Nat → Option P.Judgment) (row : Row P) :
    List (Fin (P.premises row.rule).length) → Bool × Nat
  | [] => (true, 0)
  | position :: rest =>
      if lookup (row.references position) = some ((P.premises row.rule).get position) then
        let later := inspectPremisesAt lookup row rest
        (later.1, later.2 + 1)
      else (false, 1)

private theorem inspectPremisesAt_eq (lookup : Nat → Option P.Judgment)
    (table : List P.Judgment) (agrees : ∀ index, lookup index = table[index]?)
    (row : Row P) (positions : List (Fin (P.premises row.rule).length)) :
    inspectPremisesAt lookup row positions = inspectPremises table row positions := by
  induction positions with
  | nil => rfl
  | cons position rest ih =>
      simp only [inspectPremisesAt, inspectPremises, agrees, ih]

private def readTape (atRow : Nat → Option (Row P)) (cutoff index : Nat) : Option P.Judgment :=
  if index < cutoff then (atRow index).map (fun row => P.conclusion row.rule) else none

omit [DecidableEq P.Judgment] in
private theorem readTape_append (past remaining : List (Row P))
    (atRow : Nat → Option (Row P)) (faithful : ∀ index, atRow index = (past ++ remaining)[index]?)
    (index : Nat) :
    readTape atRow past.length index = (past.map (fun row => P.conclusion row.rule))[index]? := by
  by_cases inside : index < past.length
  · simp only [readTape, if_pos inside, faithful, List.getElem?_append_left inside, List.getElem?_map]
  · simp only [readTape, if_neg inside, List.getElem?_map,
      List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt inside), Option.map_none]

private def checkRowsOnTape (atRow : Nat → Option (Row P)) (root : Nat) (wanted : P.Judgment)
    (rowsDone slotsDone : Nat) : List (Row P) → Bool × Nat × Nat
  | [] => (decide ((atRow root).map (fun row => P.conclusion row.rule) = some wanted),
      rowsDone, slotsDone + 1)
  | row :: rest =>
      let inspected := inspectPremisesAt (readTape atRow rowsDone) row
        (List.finRange (P.premises row.rule).length)
      if inspected.1 then
        checkRowsOnTape atRow root wanted (rowsDone + 1) (slotsDone + inspected.2) rest
      else (false, rowsDone + 1, slotsDone + inspected.2)

private theorem checkRowsOnTape_correct (root : Nat) (wanted : P.Judgment)
    (atRow : Nat → Option (Row P)) (checked : List (Row P)) (slots : Nat) (rows : List (Row P))
    (faithful : ∀ index, atRow index = (checked ++ rows)[index]?) :
    checkRowsOnTape atRow root wanted checked.length slots rows =
      let result := inspectRows (checked.map (fun row => P.conclusion row.rule)) rows
      match result.table with
      | none => (false, checked.length + result.rows, slots + result.premiseChecks)
      | some final => (decide (final[root]? = some wanted),
          checked.length + result.rows, slots + (result.premiseChecks + 1)) := by
  induction rows generalizing checked slots with
  | nil =>
      simp only [checkRowsOnTape, inspectRows, faithful, List.append_nil, List.getElem?_map, Nat.add_zero]
  | cons row rest ih =>
      rw [checkRowsOnTape, inspectRows]
      let concluded := checked.map (fun row => P.conclusion row.rule)
      have localResult :
          inspectPremisesAt (readTape atRow checked.length)
            row (List.finRange (P.premises row.rule).length) = inspectRow concluded row :=
        inspectPremisesAt_eq _ concluded (readTape_append checked _ atRow faithful) row _
      simp only [localResult]
      by_cases accepted : (inspectRow concluded row).1 = true
      · simp only [show checked.map _ = concluded from rfl, if_pos accepted]
        have continued := ih (checked ++ [row]) (slots + (inspectRow concluded row).2)
          (fun index => by
            simpa only [List.append_assoc, List.singleton_append] using faithful index)
        simp only [List.length_append, List.length_singleton,
          List.map_append, List.map_singleton] at continued
        rw [continued]
        cases (inspectRows (concluded ++ [P.conclusion row.rule]) rest).table <;>
          simp [concluded, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · simp [show checked.map _ = concluded from rfl, if_neg accepted]

private def tapeEntry (rows : List (Row P)) (blocks : List (List (Row P))) (index : Nat) :
    Option (Row P) :=
  if index < 32 then rows[index]? else Mettapedia.Data.List.BlockIndex.read 32 blocks index

omit [DecidableEq P.Judgment] in
private theorem tapeEntry_fromList (rows : List (Row P)) (index : Nat) :
    tapeEntry rows (Mettapedia.Data.List.BlockIndex.fromList 32 rows) index = rows[index]? := by
  simp [tapeEntry, Mettapedia.Data.List.BlockIndex.read_fromList]

/-- The certificate's rows supply their declared conclusions. The cutoff
limits premise lookups to the verified prefix. The index shares suffixes of
the original rows, and the first block is read directly. -/
def checkJudgmentsWithWork (certificate : Certificate P) (wanted : P.Judgment) : Bool × Nat × Nat :=
  let rows := certificate.rows
  let blocks := Mettapedia.Data.List.BlockIndex.fromList 32 rows
  checkRowsOnTape (tapeEntry rows blocks) certificate.root wanted 0 0 rows

/-- The prefix-checked implementation gives the original work result, including
every checked slot and refusal at the first invalid row. -/
theorem checkJudgmentsWithWork_eq_inspectRows (certificate : Certificate P) (wanted : P.Judgment) :
    checkJudgmentsWithWork certificate wanted =
      let inspected := inspectRows [] certificate.rows
      match inspected.table with
      | none => (false, inspected.rows, inspected.premiseChecks)
      | some table => (decide (table[certificate.root]? = some wanted),
          inspected.rows, inspected.premiseChecks + 1) := by
  have correct := checkRowsOnTape_correct certificate.root wanted
    (tapeEntry certificate.rows (Mettapedia.Data.List.BlockIndex.fromList 32 certificate.rows))
    [] 0 certificate.rows (tapeEntry_fromList certificate.rows)
  simp only [List.map_nil, List.length_nil, Nat.zero_add] at correct
  simp only [checkJudgmentsWithWork, correct]

private def checkRowsIndexed (root : Nat) (wanted : P.Judgment)
    (table : Array P.Judgment) (rowsDone slotsDone : Nat) :
    List (Row P) → Bool × Nat × Nat
  | [] => (decide (table[root]? = some wanted), rowsDone, slotsDone + 1)
  | row :: rest =>
      let inspected := inspectPremisesAt (fun index => table[index]?) row (List.finRange (P.premises row.rule).length)
      if inspected.1 then
        checkRowsIndexed root wanted (table.push (P.conclusion row.rule))
          (rowsDone + 1) (slotsDone + inspected.2) rest
      else (false, rowsDone + 1, slotsDone + inspected.2)

private theorem checkRowsIndexed_eq (root : Nat) (wanted : P.Judgment)
    (table : Array P.Judgment) (rowsDone slotsDone : Nat) (rows : List (Row P)) :
    checkRowsIndexed root wanted table rowsDone slotsDone rows =
      let result := inspectRows table.toList rows
      match result.table with
      | none => (false, rowsDone + result.rows, slotsDone + result.premiseChecks)
      | some final => (decide (final[root]? = some wanted),
          rowsDone + result.rows, slotsDone + (result.premiseChecks + 1)) := by
  induction rows generalizing table rowsDone slotsDone with
  | nil => simp only [checkRowsIndexed, inspectRows, Array.getElem?_toList, Nat.add_zero]
  | cons row rest ih =>
      have localResult :
          inspectPremisesAt (fun index => table[index]?) row (List.finRange (P.premises row.rule).length) =
            inspectRow table.toList row :=
        inspectPremisesAt_eq _ _ (fun _ => Array.getElem?_toList.symm) row _
      simp only [checkRowsIndexed, inspectRows, localResult]
      by_cases accepted : (inspectRow table.toList row).1 = true
      · simp only [if_pos accepted, ih, Array.toList_push]
        cases (inspectRows (table.toList ++ [P.conclusion row.rule]) rest).table <;>
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · simp [if_neg accepted]


private def checkJudgmentsWithIndex (certificate : Certificate P) (wanted : P.Judgment) :
    Bool × Nat × Nat :=
  checkRowsIndexed certificate.root wanted #[] 0 0 certificate.rows

/-- Runtime compilation can use direct indexing. The equality covers the
first refusing slot and both work counters, including a failed root lookup. -/
@[csimp] theorem checkJudgmentsWithWork_eq_indexed :
    @checkJudgmentsWithWork = @checkJudgmentsWithIndex := by
  funext presentation equality certificate wanted
  simp only [checkJudgmentsWithWork_eq_inspectRows, checkJudgmentsWithIndex, checkRowsIndexed_eq,
    Nat.zero_add]

def checkJudgments (certificate : Certificate P) (wanted : P.Judgment) : Bool :=
  (checkJudgmentsWithWork certificate wanted).1

section Controls

private def testPresentation : Presentation :=
  ⟨Bool, Bool, id, fun rule => if rule then [false, false] else []⟩

private instance : DecidableEq testPresentation.Judgment := Bool.decEq

private def repeatedPremise : Certificate testPresentation :=
  ⟨[⟨false, fun _ => 0⟩, ⟨true, fun _ => 0⟩], 1⟩

private def futurePremise : Certificate testPresentation :=
  ⟨[⟨true, fun _ => 1⟩, ⟨false, fun _ => 0⟩], 1⟩

example : checkJudgmentsWithWork repeatedPremise true = (true, 2, 3) := by decide +kernel

example : checkJudgmentsWithWork futurePremise false = (false, 1, 1) := by decide +kernel

end Controls

end Mettapedia.OSLF.NativeTypes.Certificates.Shared

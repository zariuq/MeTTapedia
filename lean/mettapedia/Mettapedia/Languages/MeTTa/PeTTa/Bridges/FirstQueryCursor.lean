import Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulQuerySource
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Resumable first-query witnesses over a complete captured domain

The worker probes one source row per transition and stops at its first match.
Its independent reference is the existing complete occurrence scan. A pause
retains the unvisited rows and their original offset; it is not absence.

The ledger counts row probes, not term-unification instructions or source
evaluator fuel. Input capture, open-fact admission, roots and revision validity
remain separate obligations. This module does not evaluate arbitrary bodies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FirstQueryCursor

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open SpaceSemantics FlatQueryRelationCompilation

abbrev Cursor := Nat × List Atom
abbrev Verdict := Option (Nat × Subst)

def machine (bindings : Subst) (pattern : Atom) : Machine Cursor Empty Verdict Empty where
  step state := some <| match state.2 with
    | [] => .finish none
    | row :: rest => match matchValue bindings pattern row with
      | none => .silent (state.1 + 1, rest)
      | some bound => .finish (some (state.1, bound))

def reference (bindings : Subst) (pattern : Atom) (state : Cursor) : Verdict :=
  (sourceScan bindings pattern state.1 state.2).head?

theorem complete (bindings : Subst) (pattern : Atom) (start : Nat) (rows : List Atom) :
    (machine bindings pattern).run (rows.length + 1) (start, rows) =
      ([], .finished (reference bindings pattern (start, rows))) := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rest ih =>
      cases matched : matchValue bindings pattern row with
      | none => simpa [machine, Machine.run, reference, sourceScan, matched] using ih (start + 1)
      | some bound => simp [machine, Machine.run, reference, sourceScan, matched]

theorem finished_exact (bindings : Subst) (pattern : Atom) (fuel start : Nat)
    (rows : List Atom) (result : Verdict)
    (finished : (machine bindings pattern).run fuel (start, rows) = ([], .finished result)) :
    result = reference bindings pattern (start, rows) := by
  induction fuel generalizing start rows with
  | zero => cases finished
  | succ fuel ih =>
      cases rows with
      | nil => simpa [machine, Machine.run, reference, sourceScan, eq_comm] using finished
      | cons row rest =>
          cases matched : matchValue bindings pattern row with
          | none =>
              have later : (machine bindings pattern).run fuel (start + 1, rest) = ([], .finished result) := by
                simpa [machine, Machine.run, matched] using finished
              simpa [reference, sourceScan, matched] using ih (start + 1) rest later
          | some bound => simpa [machine, Machine.run, reference, sourceScan, matched, eq_comm] using finished

theorem exhausted_cursor (bindings : Subst) (pattern : Atom) (fuel start offset : Nat)
    (rows rest : List Atom)
    (paused : (machine bindings pattern).run fuel (start, rows) = ([], .exhausted (offset, rest))) :
    offset = start + fuel ∧ rest = rows.drop fuel ∧ fuel ≤ rows.length := by
  induction fuel generalizing start rows with
  | zero =>
      have same : (start, rows) = (offset, rest) := by simpa [Machine.run] using paused
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      simp
  | succ fuel ih =>
      cases rows with
      | nil => simp [machine, Machine.run] at paused
      | cons row rows =>
          cases matched : matchValue bindings pattern row with
          | some bound => simp [machine, Machine.run, matched] at paused
          | none =>
              have later : (machine bindings pattern).run fuel (start + 1, rows) = ([], .exhausted (offset, rest)) := by
                simpa [machine, Machine.run, matched] using paused
              obtain ⟨position, remaining, bound⟩ := ih (start + 1) rows later
              exact ⟨by omega, by simpa using remaining, by simpa using Nat.succ_le_succ bound⟩

theorem resume_exact (bindings : Subst) (pattern : Atom) (first second : Nat)
    (state residual : Cursor)
    (paused : (machine bindings pattern).run first state = ([], .exhausted residual)) :
    (machine bindings pattern).run (first + second) state = (machine bindings pattern).run second residual := by
  simpa using (machine bindings pattern).established_and_pending first second state residual [] paused

def probePrice (state : Cursor) : Nat := if state.2.isEmpty then 0 else 1

theorem probes_bounded (bindings : Subst) (pattern : Atom) (fuel start : Nat) (rows : List Atom) :
    (machine bindings pattern).spent probePrice fuel (start, rows) ≤ rows.length := by
  induction fuel generalizing start rows with
  | zero => simp [Machine.spent]
  | succ fuel ih =>
      cases rows with
      | nil => simp [machine, Machine.spent, probePrice]
      | cons row rest =>
          cases matched : matchValue bindings pattern row with
          | none => simpa [machine, Machine.spent, probePrice, matched, Nat.add_comm] using Nat.succ_le_succ (ih (start + 1) rest)
          | some bound => simp [machine, Machine.spent, probePrice, matched]

theorem missed_probes_exact (bindings : Subst) (pattern : Atom) (fuel start : Nat) (rows : List Atom)
    (missed : (machine bindings pattern).run fuel (start, rows) = ([], .finished none)) :
    (machine bindings pattern).spent probePrice fuel (start, rows) = rows.length := by
  induction fuel generalizing start rows with
  | zero => cases missed
  | succ fuel ih =>
      cases rows with
      | nil => simp [machine, Machine.spent, probePrice]
      | cons row rest =>
          cases matched : matchValue bindings pattern row with
          | some bound => simp [machine, Machine.run, matched] at missed
          | none =>
              have later : (machine bindings pattern).run fuel (start + 1, rest) = ([], .finished none) := by
                simpa [machine, Machine.run, matched] using missed
              calc
                (machine bindings pattern).spent probePrice (fuel + 1) (start, row :: rest) =
                    1 + (machine bindings pattern).spent probePrice fuel (start + 1, rest) := by
                      simp [machine, Machine.spent, probePrice, matched]
                _ = (row :: rest).length := by rw [ih (start + 1) rest later]; simp [Nat.add_comm]

theorem found_probe_offset (bindings : Subst) (pattern : Atom) (fuel start offset : Nat)
    (rows : List Atom) (bound : Subst)
    (found : (machine bindings pattern).run fuel (start, rows) = ([], .finished (some (offset, bound)))) :
    start + (machine bindings pattern).spent probePrice fuel (start, rows) = offset + 1 := by
  induction fuel generalizing start rows with
  | zero => cases found
  | succ fuel ih =>
      cases rows with
      | nil => simp [machine, Machine.run] at found
      | cons row rest =>
          cases matched : matchValue bindings pattern row with
          | none =>
              have later : (machine bindings pattern).run fuel (start + 1, rest) =
                  ([], .finished (some (offset, bound))) := by simpa [machine, Machine.run, matched] using found
              have total := ih (start + 1) rest later
              simpa [machine, Machine.spent, probePrice, matched, Nat.add_assoc] using total
          | some accepted =>
              have same : (start, accepted) = (offset, bound) := by
                simpa [machine, Machine.run, matched] using found
              have position : start = offset := congrArg Prod.fst same
              simp [machine, Machine.spent, probePrice, matched, position]

theorem scan_answers (bindings : Subst) (pattern template : Atom) (start : Nat) (rows : List Atom) :
    (sourceScan bindings pattern start rows).map (fun answer => applySubst answer.2 template) =
      rows.filterMap (fun row => (matchValue bindings pattern row).map (fun bound => applySubst bound template)) := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rest ih =>
      cases matched : matchValue bindings pattern row <;> simp [sourceScan, matched, ih]

theorem query_first (pattern template : Atom) (rows : List Atom) :
    (query rows pattern template).head? =
      (reference [] pattern (0, rows)).map (fun answer => applySubst answer.2 template) := by
  rw [query, ← scan_answers [] pattern template 0 rows]
  simp [reference]

theorem absent_iff (bindings : Subst) (pattern : Atom) (start : Nat) (rows : List Atom) :
    reference bindings pattern (start, rows) = none ↔
      ∀ row ∈ rows, matchValue bindings pattern row = none := by
  induction rows generalizing start with
  | nil => simp [reference, sourceScan]
  | cons row rest ih =>
      cases matched : matchValue bindings pattern row with
      | none => simpa [reference, sourceScan, matched] using ih (start + 1)
      | some bound => simp [reference, sourceScan, matched]

namespace Controls

def pattern : Atom := .expression [.symbol "sat", .grounded (.int 1), .var "x"]
def row (formula state : Int) : Atom := .expression [.symbol "sat", .grounded (.int formula), .grounded (.int state)]
def rows : List Atom := [row 2 9, row 1 7, row 1 8]
def answer : Verdict := some (1, [("x", .grounded (.int 7))])

theorem paused_miss_keeps_the_unvisited_hit :
    (machine [] pattern).run 1 (0, rows) = ([], .exhausted (1, [row 1 7, row 1 8])) := by
  have miss : matchValue [] pattern (row 2 9) = none := by decide +kernel
  simp [machine, Machine.run, rows, miss]

theorem first_hit_stops_before_the_last_row :
    (machine [] pattern).run 2 (0, rows) = ([], .finished answer) ∧
      (machine [] pattern).spent probePrice 20 (0, rows) = 2 := by
  have miss : matchValue [] pattern (row 2 9) = none := by decide +kernel
  have hit : matchValue [] pattern (row 1 7) = some [("x", .grounded (.int 7))] := by decide +kernel
  simp [machine, Machine.run, Machine.spent, probePrice, rows, miss, hit, answer]

theorem empty_domain_still_needs_completion :
    (machine [] pattern).run 0 (0, []) = ([], .exhausted (0, [])) ∧
      (machine [] pattern).run 1 (0, []) = ([], .finished none) := ⟨rfl, rfl⟩

theorem reordered_rows_can_change_first_binding :
    reference [] pattern (0, [row 1 7, row 1 8]) ≠ reference [] pattern (0, [row 1 8, row 1 7]) := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FirstQueryCursor

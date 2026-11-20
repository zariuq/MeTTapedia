import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Evaluator

/-!
# Bounded table replay and explicit certificate errors

`drive` spends a budget on successful table transitions. It distinguishes
an irreducible retained row from an exhausted row that still has a table
transition. The generic driver chooses the first available schema; result
completeness requires a separate determinism theorem for the chosen program.

`checkAt` validates a supplied rule index separately. An invalid index and a
rule mismatch reject that proposal, rather than refuting the program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table

open NamesOnTheStep (Expr)
open RuleSyntax.Machines (unknowns RootStep)

def next? (schemas : List Schema) (row : Expr) : Option Expr := (successors schemas row).head?

theorem next?_mem {schemas : List Schema} {row result : Expr} (found : next? schemas row = some result) :
    result ∈ successors schemas row := by
  cases values : successors schemas row with
  | nil => simp [next?, values] at found
  | cons first rest =>
      have same : first = result := by simpa [next?, values] using found
      rw [← same]
      exact List.mem_cons_self

theorem next?_none_iff (schemas : List Schema) (row : Expr) :
    next? schemas row = none ↔ successors schemas row = [] := by
  cases values : successors schemas row <;> simp [next?, values]

inductive Result where
  | stopped (row : Expr)
  | exhausted (row : Expr)

def Result.row : Result → Expr
  | .stopped row | .exhausted row => row

def drive (schemas : List Schema) : Nat → Expr → Result
  | 0, row =>
      match next? schemas row with
      | none => .stopped row
      | some _ => .exhausted row
  | remaining + 1, row =>
      match next? schemas row with
      | none => .stopped row
      | some after => drive schemas remaining after

inductive Proposal where
  | result (row : Expr)
  | badIndex
  | mismatch

def checkAt (schemas : List Schema) (index : Nat) (row : Expr) : Proposal :=
  match schemas[index]? with
  | none => .badIndex
  | some schema =>
      match applySchema schema row with
      | none => .mismatch
      | some result => .result result

theorem checkAt_sound {schemas : List Schema} {index : Nat} {row result : Expr}
    (accepted : checkAt schemas index row = .result result) : RootStep schemas row result := by
  unfold checkAt at accepted
  cases selected : schemas[index]? with
  | none => simp [selected] at accepted
  | some schema =>
      cases matched : applySchema schema row with
      | none => simp [selected, matched] at accepted
      | some produced =>
          have same : produced = result := by simpa [selected, matched] using accepted
          subst same
          obtain ⟨assignment, left, right⟩ := applySchema_sound matched
          exact ⟨schema, List.mem_of_getElem? selected, assignment, left, right⟩

/-- A stopped result is an actual normal row of the inspected table. -/
theorem stopped_is_normal {schemas : List Schema} {budget : Nat} {row final : Expr}
    (stopped : drive schemas budget row = .stopped final) : next? schemas final = none := by
  induction budget generalizing row with
  | zero =>
      cases selected : next? schemas row with
      | none =>
          have same : row = final := by simpa [drive, selected] using stopped
          exact same ▸ selected
      | some after => simp [drive, selected] at stopped
  | succ budget ih =>
      cases selected : next? schemas row with
      | none =>
          have same : row = final := by simpa [drive, selected] using stopped
          simpa only [same] using selected
      | some after => exact ih (by simpa [drive, selected] using stopped)

/-- Exhaustion retains a row for which the same executable table still
offers a continuation. It is not a no-match verdict. -/
theorem exhausted_has_next {schemas : List Schema} {budget : Nat} {row final : Expr}
    (exhausted : drive schemas budget row = .exhausted final) : ∃ after, next? schemas final = some after := by
  induction budget generalizing row with
  | zero =>
      cases selected : next? schemas row with
      | none => simp [drive, selected] at exhausted
      | some after =>
          have same : row = final := by simpa [drive, selected] using exhausted
          exact ⟨after, same ▸ selected⟩
  | succ budget ih =>
      cases selected : next? schemas row with
      | none => simp [drive, selected] at exhausted
      | some after => exact ih (by simpa [drive, selected] using exhausted)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.checkAt_sound
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.stopped_is_normal
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.exhausted_has_next

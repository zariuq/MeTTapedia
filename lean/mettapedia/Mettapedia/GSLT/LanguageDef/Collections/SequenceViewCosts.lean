import Mettapedia.GSLT.LanguageDef.Collections.CellSequenceHosting
import Mettapedia.GSLT.LanguageDef.Collections.DirectSequenceArray
import Mettapedia.GSLT.Core.OperationalRealizationAccounts
import Mettapedia.Machines.SharedPrependCost

/-!
# Operational costs are indexed by the sequence interface

The existing finite-sequence source is realized by array slices and by cell
walks. The public results agree, while the existing transition account reads
different numbers of authentic target transitions. No cost is inferred from
the mathematical value or from equality of observations.

The cost unit here is one declared target transition: an array operation,
a cell inspection, or a cursor advance. DirectSequenceArray separately
justifies backing-array access without reference slice extraction.
Encoding, allocation,
cache behavior and elapsed time are not included in that unit. Materializing
a representation is a separate operation, accounted in SequenceViewSwitching.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.SequenceViewCosts

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.GSLTHosting
open CArray0SequenceHosting
open CellSequenceHosting

variable {α : Type}

inductive Interface where
  | cells
  | array
  deriving DecidableEq, Repr

/-- Invoke the selected operational interface for one request. The actual
worker GSLT remains explicit; a choice is not an additional evaluator. -/
def invocation (view : Interface) (operation : SequenceOp) (values : List α)
    (answer : SequenceObservation α) : Prop :=
  match view with
  | .cells => ProducesObservation (CellSequenceHosting.targetObject α)
      (compile (.request operation values)) answer
  | .array => ProducesObservation (DirectSequenceArray.target α)
      (compileTerm (.request operation values)) answer

theorem invocation_exact (view : Interface) (operation : SequenceOp) (values : List α)
    (answer : SequenceObservation α) :
    invocation view operation values answer ↔
      ProducesObservation (sourceObject α) (.request operation values) answer := by
  cases view with
  | cells => exact CellSequenceHosting.hosting_exact _ _
  | array => exact DirectSequenceArray.hosting_exact _ _

/-- Semantic selection may depend on the operation and value. Profitability
and the cost of performing selection require their own account. -/
theorem every_policy_preserves_answers (policy : SequenceOp → List α → Interface)
    (operation : SequenceOp) (values : List α) (answer : SequenceObservation α) :
    invocation (policy operation values) operation values answer ↔
      ProducesObservation (sourceObject α) (.request operation values) answer :=
  invocation_exact _ _ _ _

def sourcePath (operation : SequenceOp) (values : List α) :
    ExecutionPath (sequenceGSLT α) (.request operation values) (.done operation values) :=
  .cons ⟨SequenceStep.run operation values⟩ (.refl _)

def cellWork (operation : SequenceOp) (values : List α) : Nat :=
  (CellSequenceHosting.realization.mapRoute (sourcePath operation values)).length

def arrayWork (operation : SequenceOp) (values : List α) : Nat :=
  (CArray0SequenceHosting.realization.mapRoute (sourcePath operation values)).length

theorem cellWork_is_block_account (operation : SequenceOp) (values : List α) :
    Multiplicative.ofAdd (cellWork operation values) =
      CellSequenceHosting.realization.blockAccount.of (sourcePath operation values) := rfl

theorem arrayWork_is_block_account (operation : SequenceOp) (values : List α) :
    Multiplicative.ofAdd (arrayWork operation values) =
      CArray0SequenceHosting.realization.blockAccount.of (sourcePath operation values) := rfl

theorem lookupPath_length (index : Nat) (cells : Cell α) :
    (lookupPath index cells).length = min (index + 1) ((elements cells).length + 1) := by
  induction cells generalizing index with
  | stop ending => simp [lookupPath, Route.length, elements, Layouts.Cells.abs]
  | cell x xs ih =>
      cases index with
      | zero => simp [lookupPath, Route.length, elements, Layouts.Cells.abs]
      | succ index =>
          change (lookupPath index xs).length + 1 =
            min (index + 1 + 1) ((elements xs).length + 1 + 1)
          have tail := ih index
          omega

theorem countPath_length (accumulator : Nat) (cells : Cell α) :
    (countPath accumulator cells).length = (elements cells).length + 1 := by
  induction cells generalizing accumulator with
  | stop ending => rfl
  | cell x xs ih =>
      change (countPath (accumulator + 1) xs).length + 1 = (elements xs).length + 1 + 1
      have tail := ih (accumulator + 1)
      omega

theorem cellWork_at (index : Nat) (values : List α) :
    cellWork (.at index) values = min (index + 1) (values.length + 1) := by
  change ((lookupPath index (ofList values)).append (.refl _)).length = _
  rw [Route.length_append, lookupPath_length, ofList_elements]
  rfl

theorem cellWork_length (values : List α) : cellWork .length values = values.length + 1 := by
  change ((countPath 0 (ofList values)).append (.refl _)).length = _
  rw [Route.length_append, countPath_length, ofList_elements]
  rfl

theorem cellWork_first (values : List α) : cellWork .first values = 1 := by
  cases values <;> rfl

theorem cellWork_rest (values : List α) : cellWork .rest values = 1 := by
  cases values <;> rfl

theorem arrayWork_eq_one (operation : SequenceOp) (values : List α) :
    arrayWork operation values = 1 := rfl

/-- No extra execution stage is required merely to share a source contract. -/
theorem direct_first_and_rest (values : List α) :
    cellWork .first values = arrayWork .first values ∧
      cellWork .rest values = arrayWork .rest values := by
  simp [cellWork_first, cellWork_rest, arrayWork_eq_one]

theorem valid_lookup_cost (index : Nat) (values : List α) (inside : index < values.length) :
    cellWork (.at index) values = index + 1 := by
  rw [cellWork_at, Nat.min_eq_left (by omega)]

/-- Even on the same operation and value, no fixed factor bounds all cell
lookup paths by the selected direct array-load path. -/
theorem lookup_gap_unbounded (factor : Nat) :
    ∃ values : List Nat,
      factor * arrayWork (.at factor) values < cellWork (.at factor) values := by
  refine ⟨List.replicate (factor + 1) 0, ?_⟩
  simp [arrayWork_eq_one, cellWork_at]

/-- The opposite preference is witnessed by the independently established
shared-prepend protocol: copying a shared flat buffer can be arbitrarily
more expensive than retaining a cell tail. This uses that protocol's own
copy/claim account, not the lookup transition count above. -/
theorem shared_prepend_prefers_cells (factor : Nat) :
    ∃ count : Nat,
      factor * (Mettapedia.Machines.SharedPrependCost.sharedChunked count).2 <
        (Mettapedia.Machines.SharedPrependCost.sharedFlat count).2 := by
  refine ⟨4 * factor + 1, ?_⟩
  exact Mettapedia.Machines.SharedPrependCost.sharedFlat_exceeds factor (4 * factor + 1)
    (by omega)

namespace Controls

example : cellWork (.at 4095) (List.replicate 4096 (0 : Nat)) = 4096 := by
  rw [cellWork_at, List.length_replicate]
  omega

example : arrayWork (.at 4095) (List.replicate 4096 (0 : Nat)) = 1 := rfl

example : cellWork .rest (List.replicate 4096 (0 : Nat)) = 1 := cellWork_rest _

/-- A same-value result cannot hide an invented answer from an actual path. -/
theorem wrong_answer_not_produced :
    ¬ ProducesObservation (CellSequenceHosting.targetObject Nat)
      (compile (.request (.at 0) [1])) (.element 2) := by
  rintro ⟨⟨last, path, observed⟩⟩
  have conserved := CellSequenceHosting.invariant.executionPath_eq path
  have result := observation_has_meaning observed
  have expected := conserved.trans result
  change meaning (compile (.request (.at 0) [1])) = .element 2 at expected
  rw [meaning_compile] at expected
  norm_num [sequenceSem] at expected

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.SequenceViewCosts

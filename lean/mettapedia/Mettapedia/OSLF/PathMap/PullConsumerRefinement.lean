import Mathlib.Data.List.Defs

/-!
# Pull-consumer refinement for counted PathMap rows

The materializing evaluator first reconstructs every visible row and then
applies a consumer.  The direct backend path feeds the same row occurrences to
the consumer one at a time and may stop once demand is satisfied.

This module proves the observation laws needed by the implemented consumers:

* full collapse/materialization and ordered space transfer;
* fold and count;
* existence/`once` and finite-prefix/`select`;
* `collapse`-then-`superpose`, including producer-error suppression;
* the internal `Empty` sentinel consumes no demand.

The direct definitions recurse over the physical row stream.  Their oracle
counterparts first build a visible list with `List.filterMap`; the equalities
are therefore refinement proofs between distinct execution shapes, not
definitional aliases.
-/

namespace Mettapedia.OSLF.PathMap.PullConsumerRefinement

variable {Row State Error Value Result : Type}

/-! ## Visible-row consumers -/

/-- `none` is the backend's internal no-result sentinel; `some row` is one
logical occurrence. -/
def materialize (rows : List (Option Row)) : List Row :=
  rows.filterMap id

/-- Direct full readback, skipping sentinels before publishing a row. -/
def pullMaterialize : List (Option Row) → List Row
  | [] => []
  | none :: rest => pullMaterialize rest
  | some row :: rest => row :: pullMaterialize rest

/-- Direct full readback equals materialization, with identical occurrence
order and multiplicity. -/
theorem pullMaterialize_eq_materialize (rows : List (Option Row)) :
    pullMaterialize rows = materialize rows := by
  induction rows with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [pullMaterialize, materialize, ih]

/-- A one-pass left fold over visible physical rows. -/
def pullFold (step : State → Row → State) : State → List (Option Row) → State
  | state, [] => state
  | state, none :: rest => pullFold step state rest
  | state, some row :: rest => pullFold step (step state row) rest

/-- Pull-folding is exactly folding the materialized occurrence list. -/
theorem pullFold_eq_materializedFold (step : State → Row → State)
    (state : State) (rows : List (Option Row)) :
    pullFold step state rows = (materialize rows).foldl step state := by
  induction rows generalizing state with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [pullFold, materialize, ih]

/-- Count visible occurrences without reconstructing a result bag. -/
def pullCount : List (Option Row) → Nat
  | [] => 0
  | none :: rest => pullCount rest
  | some _ :: rest => pullCount rest + 1

/-- Direct counted-fold and materialized length agree exactly. -/
theorem pullCount_eq_materializedLength (rows : List (Option Row)) :
    pullCount rows = (materialize rows).length := by
  induction rows with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [pullCount, materialize, ih]

/-- Consume at most `demand` visible rows.  Sentinels do not decrement demand. -/
def pullPrefix : Nat → List (Option Row) → List Row
  | 0, _ => []
  | _ + 1, [] => []
  | demand + 1, none :: rest => pullPrefix (demand + 1) rest
  | demand + 1, some row :: rest => row :: pullPrefix demand rest

/-- Prefix pulling equals taking a prefix after full materialization. -/
theorem pullPrefix_eq_materializedTake (demand : Nat)
    (rows : List (Option Row)) :
    pullPrefix demand rows = (materialize rows).take demand := by
  induction rows generalizing demand with
  | nil => cases demand <;> rfl
  | cons item rest ih =>
      cases demand with
      | zero => rfl
      | succ demand =>
          cases item <;> simp [pullPrefix, materialize, ih]

/-- Existence is the one-row demand specialization. -/
def pullExists (rows : List (Option Row)) : Bool :=
  !(pullPrefix 1 rows).isEmpty

/-- Direct existence agrees with testing the materialized bag. -/
theorem pullExists_eq_materialized (rows : List (Option Row)) :
    pullExists rows = !(materialize rows).isEmpty := by
  rw [pullExists, pullPrefix_eq_materializedTake]
  cases materialize rows <;> rfl

/-- Ordered space transfer appends precisely the visible occurrence stream. -/
def pullTransfer (destination : List Row) (rows : List (Option Row)) : List Row :=
  destination ++ pullMaterialize rows

/-- Direct transfer agrees with transfer through the materialized tuple. -/
theorem pullTransfer_eq_materialized (destination : List Row)
    (rows : List (Option Row)) :
    pullTransfer destination rows = destination ++ materialize rows := by
  simp [pullTransfer, pullMaterialize_eq_materialize]

/-! ## Collapse followed by superpose -/

/-- Physical producer rows distinguish the internal empty sentinel, producer
errors, and ordinary branch values. -/
inductive ProducerRow (Error Value : Type) where
  | empty
  | error (error : Error)
  | value (value : Value)
deriving DecidableEq, Repr

/-- The externally observed branch result. -/
inductive Observation (Error Result : Type) where
  | error (error : Error)
  | value (result : Result)
deriving DecidableEq, Repr

def sourceErrors : List (ProducerRow Error Value) → List Error
  | [] => []
  | .empty :: rest => sourceErrors rest
  | .error error :: rest => error :: sourceErrors rest
  | .value _ :: rest => sourceErrors rest

def sourceValues : List (ProducerRow Error Value) → List Value
  | [] => []
  | .empty :: rest => sourceValues rest
  | .error _ :: rest => sourceValues rest
  | .value value :: rest => value :: sourceValues rest

/-- The materializing oracle: collapse suppresses producer errors whenever at
least one ordinary source value exists, then superpose evaluates values in
source order.  When every visible source row is an error, all error
occurrences are retained in source order. -/
def materializedSuperpose
    (eval : Value → List (Observation Error Result))
    (rows : List (ProducerRow Error Value)) : List (Observation Error Result) :=
  if (sourceValues rows).isEmpty then
    (sourceErrors rows).map Observation.error
  else
    (sourceValues rows).flatMap eval

/-- State accumulated by the one-pass implementation. -/
structure SuperposeScan (Error Result : Type) where
  producerErrors : List Error
  branchResults : List (Observation Error Result)
  sawValue : Bool

/-- One physical pass.  Producer errors are buffered; ordinary values are
evaluated immediately and establish that the buffered errors are suppressed. -/
def scanSuperpose
    (eval : Value → List (Observation Error Result)) :
    List (ProducerRow Error Value) → SuperposeScan Error Result
  | [] => ⟨[], [], false⟩
  | .empty :: rest => scanSuperpose eval rest
  | .error error :: rest =>
      let tail := scanSuperpose eval rest
      ⟨error :: tail.producerErrors, tail.branchResults, tail.sawValue⟩
  | .value value :: rest =>
      let tail := scanSuperpose eval rest
      ⟨tail.producerErrors, eval value ++ tail.branchResults, true⟩

@[simp] theorem scanSuperpose_errors
    (eval : Value → List (Observation Error Result))
    (rows : List (ProducerRow Error Value)) :
    (scanSuperpose eval rows).producerErrors = sourceErrors rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases row <;> simp [scanSuperpose, sourceErrors, ih]

@[simp] theorem scanSuperpose_results
    (eval : Value → List (Observation Error Result))
    (rows : List (ProducerRow Error Value)) :
    (scanSuperpose eval rows).branchResults = (sourceValues rows).flatMap eval := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases row <;> simp [scanSuperpose, sourceValues, ih]

@[simp] theorem scanSuperpose_sawValue
    (eval : Value → List (Observation Error Result))
    (rows : List (ProducerRow Error Value)) :
    (scanSuperpose eval rows).sawValue = !(sourceValues rows).isEmpty := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases row <;> simp [scanSuperpose, sourceValues, ih]

/-- The direct fused consumer selects its buffered error or evaluated-value
observation only after the one physical pass finishes. -/
def pullSuperpose
    (eval : Value → List (Observation Error Result))
    (rows : List (ProducerRow Error Value)) : List (Observation Error Result) :=
  let scan := scanSuperpose eval rows
  if scan.sawValue then scan.branchResults
  else scan.producerErrors.map Observation.error

/-- Pulling through collapse/superpose is observation-equivalent to
materializing the collapse tuple first. -/
theorem pullSuperpose_eq_materialized
    (eval : Value → List (Observation Error Result))
    (rows : List (ProducerRow Error Value)) :
    pullSuperpose eval rows = materializedSuperpose eval rows := by
  simp only [pullSuperpose, scanSuperpose_sawValue, scanSuperpose_results,
    scanSuperpose_errors, materializedSuperpose]
  cases h : (sourceValues rows).isEmpty <;> simp

/-! ## Positive and negative discriminators -/

/-- An internal sentinel cannot spend the one-row demand. -/
example : pullPrefix 1 [none, some 7] = [7] := rfl

/-- **Negative witness.**  Taking a physical prefix before skipping sentinels
loses a visible row; demand must count logical occurrences, not cursor records. -/
theorem physical_take_before_sentinel_filter_is_wrong :
    (([none, some 7] : List (Option Nat)).take 1).filterMap id
      ≠ pullPrefix 1 [none, some 7] := by
  decide

/-- A mixed producer suppresses its producer error but retains branch results. -/
example :
    pullSuperpose (Error := String) (Result := Nat)
      (fun value => [Observation.value (value + 1)])
      [ProducerRow.error "hidden", ProducerRow.value 8]
      = [Observation.value 9] := by
  rfl

/-- An all-error producer retains every error occurrence in order. -/
example :
    pullSuperpose (Value := Nat) (Result := Nat)
      (fun value => [Observation.value value])
      [ProducerRow.error "one", ProducerRow.error "two"]
      = [Observation.error "one", Observation.error "two"] := by
  rfl

/-- **Negative witness.**  Emitting producer errors eagerly changes the mixed
observation and therefore cannot refine collapse/superpose. -/
theorem eager_producer_error_is_wrong :
    [Observation.error "hidden", Observation.value 9]
      ≠ pullSuperpose (Value := Nat)
          (fun value => [Observation.value (value + 1)])
          [ProducerRow.error "hidden", ProducerRow.value 8] := by
  decide

end Mettapedia.OSLF.PathMap.PullConsumerRefinement

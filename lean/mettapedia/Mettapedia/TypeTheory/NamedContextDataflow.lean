import Mettapedia.TypeTheory.NamedValueContexts
import Mettapedia.Languages.Dataflow.Operational

/-!
# Named value contexts consumed by existing dataflow instructions

The source instruction, its operand footprint, lookup, readiness evaluator
and firing relation all come from the existing dataflow language. Equality
of inspected operand bindings preserves readiness exactly, including missing
operands and arity rejection. An unrelated binding edit is therefore safe
for this consumer, although the complete context has changed.

The controls use the same open addition instruction with two different
bindings of its second operand. A captured version keeps the first result;
an explicit live reference selects the revised result. Pure inspection
retains the code and requested bindings without firing the instruction.
No closure calling convention, live-handle effect semantics, or reference
default is selected.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NamedContextDataflow

open Mettapedia.Machines
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.Languages.Dataflow
open NamedValueContexts

variable {Op Value : Type}

/-- Operand evaluation depends only on the bindings it actually names. -/
theorem evalOperands_eq_of_agreement (left right : List (CellId × Value))
    (operands : List CellId)
    (agrees : ∀ cell ∈ operands, lookup left cell = lookup right cell) :
    evalOperands left operands = evalOperands right operands := by
  induction operands with
  | nil => rfl
  | cons cell cells inductionHypothesis =>
      have head := agrees cell (by simp)
      have tail := inductionHypothesis (fun observed member => agrees observed (by simp [member]))
      simp only [evalOperands, head, tail]

/-- The existing readiness evaluator is a concrete footprint-sensitive
consumer. This theorem covers every source instruction and operator spec. -/
theorem readyValue_eq_of_agreement (spec : PureOperatorSpec Op Value)
    (left right : List (CellId × Value)) (instruction : Instruction Op Value)
    (agrees : ∀ cell ∈ instruction.operands, lookup left cell = lookup right cell) :
    readyValue spec left instruction = readyValue spec right instruction := by
  cases instruction with
  | const _ _ => rfl
  | apply destination operator operands =>
      have same := evalOperands_eq_of_agreement left right operands agrees
      simp only [readyValue, same]

theorem readyValue_eq_of_inspection (spec : PureOperatorSpec Op Value)
    (left right : List (CellId × Value)) (instruction : Instruction Op Value)
    (same : inspectBindings (lookup left) instruction.operands =
      inspectBindings (lookup right) instruction.operands) :
    readyValue spec left instruction = readyValue spec right instruction :=
  readyValue_eq_of_agreement spec left right instruction
    ((inspectBindings_eq_iff _ _ _).mp same)

/-- Prepending an unrelated binding can change the environment without
changing either a successful result or the reason that readiness fails. -/
theorem readyValue_unrelated_binding (spec : PureOperatorSpec Op Value)
    (environment : List (CellId × Value)) (instruction : Instruction Op Value)
    (changed : CellId) (value : Value) (outside : changed ∉ instruction.operands) :
    readyValue spec ((changed, value) :: environment) instruction =
      readyValue spec environment instruction := by
  apply readyValue_eq_of_agreement
  intro observed member
  have different : changed ≠ observed := by
    intro same
    exact outside (same.symm ▸ member)
  exact lookup_cons_of_ne different value environment

/-- Resolve the explicit context, then call the existing source evaluator.
The nested option distinguishes absent context from a present but unready
instruction. -/
def runReady {Name Revision : Type} (spec : PureOperatorSpec Op Value)
    (table : ContextTable Name Revision (List (CellId × Value)))
    (current : RevisionEnvironment Name Revision)
    (object : NamedCode Name Revision (Instruction Op Value)) : Option (Option Value) :=
  execute table current (fun instruction environment => readyValue spec environment instruction) object

theorem runReady_resolved {Name Revision : Type} (spec : PureOperatorSpec Op Value)
    (table : ContextTable Name Revision (List (CellId × Value)))
    (current : RevisionEnvironment Name Revision)
    (object : NamedCode Name Revision (Instruction Op Value)) (environment : List (CellId × Value))
    (found : resolve table current object.context = some environment) :
    runReady spec table current object = some (readyValue spec environment object.code) :=
  execute_resolved table current _ object environment found

/-- Two explicitly resolved contexts may differ outside the instruction's
footprint and still give the same complete readiness result. -/
theorem runReady_eq_of_inspected_bindings {Name Revision : Type}
    (spec : PureOperatorSpec Op Value)
    (table : ContextTable Name Revision (List (CellId × Value)))
    (current : RevisionEnvironment Name Revision) (instruction : Instruction Op Value)
    (first second : Reference Name Revision) (left right : List (CellId × Value))
    (leftFound : resolve table current first = some left)
    (rightFound : resolve table current second = some right)
    (same : inspectBindings (lookup left) instruction.operands =
      inspectBindings (lookup right) instruction.operands) :
    runReady spec table current ⟨instruction, first⟩ =
      runReady spec table current ⟨instruction, second⟩ := by
  rw [runReady_resolved spec table current _ left leftFound,
    runReady_resolved spec table current _ right rightFound]
  exact congrArg some (readyValue_eq_of_inspection spec left right instruction same)

namespace Controls

inductive Operator where
  | add
deriving DecidableEq, Repr

def arithmetic : PureOperatorSpec Operator Nat where
  arity _ := 2
  apply _ values := values.sum

/-- Read cells 0 and 1 and write their sum to cell 2. -/
def addition : Instruction Operator Nat := .apply 2 .add [0, 1]

def original : List (CellId × Nat) := [(0, 3), (1, 7)]
def revised : List (CellId × Nat) := [(0, 3), (1, 9)]

def originalVersion : StoreReadToken String Nat := ⟨"lexical", 0⟩
def revisedVersion : StoreReadToken String Nat := ⟨"lexical", 1⟩

def originalTable : ContextTable String Nat (List (CellId × Nat)) :=
  writeSource emptySourceEnvironment (originalVersion, original)

def revisedTable : ContextTable String Nat (List (CellId × Nat)) :=
  writeSource originalTable (revisedVersion, revised)

def originalCurrent : RevisionEnvironment String Nat := ⟨fun _ => 0⟩
def revisedCurrent : RevisionEnvironment String Nat := originalCurrent.update "lexical" 1

def fixed : NamedCode String Nat (Instruction Operator Nat) :=
  ⟨addition, capture originalCurrent "lexical"⟩

def live : NamedCode String Nat (Instruction Operator Nat) := ⟨addition, .live "lexical"⟩

theorem publication_is_fresh_and_replacement_rejected :
    publishVersion? originalTable revisedVersion revised = some revisedTable ∧
      publishVersion? revisedTable originalVersion revised = none := ⟨rfl, rfl⟩

/-- The same source and named context have explicit stable/live behaviors.
Both versions remain available; advancing the selector is not erasure. -/
theorem captured_and_live_after_revision :
    fixed.code = live.code ∧
      runReady arithmetic originalTable originalCurrent fixed = some (some 10) ∧
      runReady arithmetic originalTable originalCurrent live = some (some 10) ∧
      runReady arithmetic revisedTable revisedCurrent fixed = some (some 10) ∧
      runReady arithmetic revisedTable revisedCurrent live = some (some 12) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Code alone cannot determine this open instruction's value across the
two actually resolved contexts. Missing-reference behavior is not used. -/
theorem no_context_free_evaluator :
    ¬ ∃ evaluateCode : Instruction Operator Nat → Option Nat,
      ∀ reference environment,
        resolve revisedTable revisedCurrent reference = some environment →
        runReady arithmetic revisedTable revisedCurrent ⟨addition, reference⟩ =
          some (evaluateCode addition) := by
  rintro ⟨evaluateCode, agrees⟩
  have first := agrees (.versioned originalVersion) original rfl
  have second := agrees (.versioned revisedVersion) revised rfl
  have impossible : (some (some 10) : Option (Option Nat)) = some (some 12) :=
    first.trans second.symm
  cases impossible

theorem unrelated_binding_preserves_readiness :
    readyValue arithmetic ((99, 1000) :: original) addition = some 10 := by
  rw [readyValue_unrelated_binding arithmetic original addition 99 1000 (by decide)]
  rfl

/-- A present but missing-operand context is not an absent context. -/
theorem missing_binding_and_missing_context_are_distinct :
    runReady arithmetic (writeSource originalTable (revisedVersion, [(0, 3)]))
        revisedCurrent live = some none ∧
      runReady arithmetic originalTable revisedCurrent live = none := ⟨rfl, rfl⟩

/-- Inspection exposes the requested bindings and source without writing
the destination. The separately exhibited source firing does write it. -/
theorem inspection_and_explicit_firing :
    inspect revisedTable revisedCurrent lookup fixed addition.operands =
        some (addition, [(0, some 3), (1, some 7)]) ∧
      lookup original 2 = none ∧
      Step arithmetic ⟨original, [addition]⟩ ⟨(2, 10) :: original, []⟩ := by
  refine ⟨rfl, rfl, ?_⟩
  exact Step.fire (pre := []) (post := []) rfl

/-- Execution is not an inverse of source inspection: constant and open
addition instructions can agree in value while their inspected code differs. -/
theorem same_value_different_source :
    readyValue arithmetic original addition =
        readyValue arithmetic original (.const 2 10) ∧
      addition ≠ .const 2 10 := by
  exact ⟨rfl, by intro same; cases same⟩

end Controls

#print axioms evalOperands_eq_of_agreement
#print axioms readyValue_eq_of_inspection
#print axioms readyValue_unrelated_binding
#print axioms runReady_eq_of_inspected_bindings
#print axioms Controls.captured_and_live_after_revision
#print axioms Controls.no_context_free_evaluator
#print axioms Controls.inspection_and_explicit_firing

end Mettapedia.TypeTheory.NamedContextDataflow
